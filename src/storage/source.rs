//! External data source abstraction.
//!
//! This module defines traits and types for loading XML data from external
//! sources (like TerminusDB) into Xot's internal representation.
//!
//! # Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────────────┐
//! │                      Xot                             │
//! │  - names, namespaces (local ID lookup)              │
//! │  - storage: ArenaStorage (internal cache)           │
//! │  - source: Box<dyn DataSource> (external data)      │
//! ├─────────────────────────────────────────────────────┤
//! │                 DataSource trait                     │
//! │  Provides raw node data with string names/URIs      │
//! ├─────────────────────────────────────────────────────┤
//! │  TerminusDBSource │ FileSource │ CustomSource │ ... │
//! └─────────────────────────────────────────────────────┘
//! ```
//!
//! When Xot navigates to a node not in the cache:
//! 1. It asks the DataSource for raw data
//! 2. Converts strings to local IDs (NameId, NamespaceId, etc.)
//! 3. Creates a Value and inserts into the Arena
//! 4. Maps external ID ↔ internal NodeId

use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;

/// External node identifier.
///
/// Each data source defines its own ID type. For TerminusDB this might be
/// an IRI, for a file-based source it might be a byte offset, etc.
pub trait ExternalId: Clone + Eq + Hash + Debug + Send + Sync + 'static {}

// Blanket implementation for common types
impl<T: Clone + Eq + Hash + Debug + Send + Sync + 'static> ExternalId for T {}

/// Raw node data before conversion to Xot's internal representation.
///
/// This contains strings for names/namespaces rather than IDs, since
/// the external source doesn't know about Xot's internal ID mappings.
#[derive(Debug, Clone)]
pub struct RawNode<Id: ExternalId> {
    /// The external ID of this node
    pub id: Id,
    /// The node's data
    pub kind: RawNodeKind,
}

/// The kind of raw node data.
#[derive(Debug, Clone)]
pub enum RawNodeKind {
    /// Document root node
    Document,

    /// Element node
    Element {
        /// Local name of the element
        name: String,
        /// Namespace URI (None for no namespace)
        namespace: Option<String>,
    },

    /// Text node
    Text {
        /// Text content
        content: String,
    },

    /// Comment node
    Comment {
        /// Comment content
        content: String,
    },

    /// Processing instruction node
    ProcessingInstruction {
        /// Target name
        target: String,
        /// Data content (optional)
        data: Option<String>,
    },

    /// Attribute node
    Attribute {
        /// Local name of the attribute
        name: String,
        /// Namespace URI (None for no namespace)
        namespace: Option<String>,
        /// Attribute value
        value: String,
    },

    /// Namespace declaration node
    Namespace {
        /// Prefix (empty string for default namespace)
        prefix: String,
        /// Namespace URI
        uri: String,
    },
}

/// Relationship information from external source.
#[derive(Debug, Clone)]
pub struct RawRelationships<Id: ExternalId> {
    /// Parent node ID (None for document root)
    pub parent: Option<Id>,
    /// Child node IDs in order
    pub children: Vec<Id>,
    /// Previous sibling (None if first child)
    pub previous_sibling: Option<Id>,
    /// Next sibling (None if last child)
    pub next_sibling: Option<Id>,
}

/// Error type for data source operations.
#[derive(Debug)]
pub enum SourceError {
    /// Node not found in external source
    NotFound(String),
    /// Connection or communication error
    ConnectionError(String),
    /// Data format or parsing error
    DataError(String),
    /// Other error
    Other(Box<dyn std::error::Error + Send + Sync>),
}

impl std::fmt::Display for SourceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotFound(id) => write!(f, "Node not found: {}", id),
            Self::ConnectionError(msg) => write!(f, "Connection error: {}", msg),
            Self::DataError(msg) => write!(f, "Data error: {}", msg),
            Self::Other(e) => write!(f, "Error: {}", e),
        }
    }
}

impl std::error::Error for SourceError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Other(e) => Some(e.as_ref()),
            _ => None,
        }
    }
}

/// External data source trait.
///
/// Implement this trait to provide XML data from an external source
/// (database, file, network, etc.) that can be lazily loaded into Xot.
///
/// # Type Parameter
///
/// The `Id` type is the external identifier used by the source. This could be:
/// - An IRI string for TerminusDB
/// - A byte offset for file-based sources
/// - A UUID for some databases
/// - Any other unique identifier
///
/// # Example
///
/// ```ignore
/// struct MyDatabaseSource {
///     connection: DatabaseConnection,
/// }
///
/// impl DataSource for MyDatabaseSource {
///     type Id = String;  // Use IRIs as IDs
///
///     fn root(&self) -> Result<Self::Id, SourceError> {
///         self.connection.query_root_id()
///     }
///
///     fn fetch_node(&self, id: &Self::Id) -> Result<RawNode<Self::Id>, SourceError> {
///         self.connection.query_node(id)
///     }
///
///     // ... etc
/// }
/// ```
pub trait DataSource: Send + Sync {
    /// The external ID type used by this source.
    type Id: ExternalId;

    /// Get the root document node ID.
    fn root(&self) -> Result<Self::Id, SourceError>;

    /// Fetch a single node's data.
    fn fetch_node(&self, id: &Self::Id) -> Result<RawNode<Self::Id>, SourceError>;

    /// Fetch a node's relationships (parent, children, siblings).
    fn fetch_relationships(&self, id: &Self::Id) -> Result<RawRelationships<Self::Id>, SourceError>;

    /// Fetch a node and its relationships in one call.
    ///
    /// Default implementation calls `fetch_node` and `fetch_relationships` separately.
    /// Override for more efficient combined queries.
    fn fetch_node_with_relationships(
        &self,
        id: &Self::Id,
    ) -> Result<(RawNode<Self::Id>, RawRelationships<Self::Id>), SourceError> {
        let node = self.fetch_node(id)?;
        let relationships = self.fetch_relationships(id)?;
        Ok((node, relationships))
    }

    /// Fetch multiple nodes in batch.
    ///
    /// Default implementation calls `fetch_node` for each ID.
    /// Override for more efficient batch queries.
    fn fetch_nodes_batch(
        &self,
        ids: &[Self::Id],
    ) -> Result<Vec<RawNode<Self::Id>>, SourceError> {
        ids.iter().map(|id| self.fetch_node(id)).collect()
    }

    /// Check if a node exists without fetching its data.
    ///
    /// Default implementation tries to fetch and returns Ok(true) on success.
    fn exists(&self, id: &Self::Id) -> Result<bool, SourceError> {
        match self.fetch_node(id) {
            Ok(_) => Ok(true),
            Err(SourceError::NotFound(_)) => Ok(false),
            Err(e) => Err(e),
        }
    }
}

/// Bidirectional mapping between external IDs and internal NodeIds.
pub struct IdMapping<ExtId: ExternalId, IntId: Copy + Eq + Hash> {
    /// External ID → Internal ID
    ext_to_int: HashMap<ExtId, IntId>,
    /// Internal ID → External ID
    int_to_ext: HashMap<IntId, ExtId>,
}

impl<ExtId: ExternalId, IntId: Copy + Eq + Hash> IdMapping<ExtId, IntId> {
    /// Create a new empty mapping.
    pub fn new() -> Self {
        Self {
            ext_to_int: HashMap::new(),
            int_to_ext: HashMap::new(),
        }
    }

    /// Insert a mapping between external and internal IDs.
    pub fn insert(&mut self, ext: ExtId, int: IntId) {
        self.ext_to_int.insert(ext.clone(), int);
        self.int_to_ext.insert(int, ext);
    }

    /// Look up internal ID from external ID.
    pub fn get_internal(&self, ext: &ExtId) -> Option<IntId> {
        self.ext_to_int.get(ext).copied()
    }

    /// Look up external ID from internal ID.
    pub fn get_external(&self, int: IntId) -> Option<&ExtId> {
        self.int_to_ext.get(&int)
    }

    /// Check if an external ID is mapped.
    pub fn contains_external(&self, ext: &ExtId) -> bool {
        self.ext_to_int.contains_key(ext)
    }

    /// Check if an internal ID is mapped.
    pub fn contains_internal(&self, int: IntId) -> bool {
        self.int_to_ext.contains_key(&int)
    }

    /// Remove a mapping by internal ID.
    pub fn remove_by_internal(&mut self, int: IntId) -> Option<ExtId> {
        if let Some(ext) = self.int_to_ext.remove(&int) {
            self.ext_to_int.remove(&ext);
            Some(ext)
        } else {
            None
        }
    }

    /// Clear all mappings.
    pub fn clear(&mut self) {
        self.ext_to_int.clear();
        self.int_to_ext.clear();
    }

    /// Number of mappings.
    pub fn len(&self) -> usize {
        self.ext_to_int.len()
    }

    /// Check if empty.
    pub fn is_empty(&self) -> bool {
        self.ext_to_int.is_empty()
    }
}

impl<ExtId: ExternalId, IntId: Copy + Eq + Hash> Default for IdMapping<ExtId, IntId> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_id_mapping() {
        let mut mapping: IdMapping<String, u32> = IdMapping::new();

        mapping.insert("ext1".to_string(), 1);
        mapping.insert("ext2".to_string(), 2);

        assert_eq!(mapping.get_internal(&"ext1".to_string()), Some(1));
        assert_eq!(mapping.get_internal(&"ext2".to_string()), Some(2));
        assert_eq!(mapping.get_external(1), Some(&"ext1".to_string()));
        assert_eq!(mapping.get_external(2), Some(&"ext2".to_string()));

        assert!(mapping.contains_external(&"ext1".to_string()));
        assert!(!mapping.contains_external(&"ext3".to_string()));
    }
}
