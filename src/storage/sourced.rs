//! Sourced Xot - Xot backed by an external data source.
//!
//! This module provides `SourcedXot`, which wraps a `Xot` instance and an
//! external `DataSource`, loading nodes on-demand into the internal cache.
//!
//! # Usage Pattern
//!
//! ```ignore
//! let source = MyDatabaseSource::connect("localhost")?;
//! let mut sourced = SourcedXot::new(source)?;
//!
//! // Load the document root and its children
//! sourced.load_root()?;
//! sourced.load_children(sourced.root())?;
//!
//! // Now navigate using regular Xot methods
//! let doc_element = sourced.xot().document_element(sourced.root())?;
//!
//! // Load more as needed
//! sourced.load_children(doc_element)?;
//! for child in sourced.xot().children(doc_element) {
//!     // ...
//! }
//! ```

use std::collections::HashSet;

use indextree::NodeId;

use crate::xotdata::{Node, Xot};
use crate::xmlvalue::{Attribute, Comment, Element, Namespace, ProcessingInstruction, Text, Value};

use super::source::{DataSource, IdMapping, RawNode, RawNodeKind, SourceError};

/// Error type for SourcedXot operations.
#[derive(Debug)]
pub enum SourcedError {
    /// Error from the data source
    Source(SourceError),
    /// Error from Xot operations
    Xot(crate::error::Error),
    /// Node not found in cache and couldn't be loaded
    NodeNotCached(String),
}

impl std::fmt::Display for SourcedError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Source(e) => write!(f, "Source error: {}", e),
            Self::Xot(e) => write!(f, "Xot error: {}", e),
            Self::NodeNotCached(msg) => write!(f, "Node not cached: {}", msg),
        }
    }
}

impl std::error::Error for SourcedError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Source(e) => Some(e),
            Self::Xot(e) => Some(e),
            _ => None,
        }
    }
}

impl From<SourceError> for SourcedError {
    fn from(e: SourceError) -> Self {
        Self::Source(e)
    }
}

impl From<crate::error::Error> for SourcedError {
    fn from(e: crate::error::Error) -> Self {
        Self::Xot(e)
    }
}

/// A Xot instance backed by an external data source.
///
/// `SourcedXot` wraps a regular `Xot` (used as an internal cache) and a
/// `DataSource` that provides data on-demand. Nodes are loaded explicitly
/// using `load_*` methods, then navigated using standard Xot methods.
///
/// # Example
///
/// ```ignore
/// let source = MyDatabaseSource::connect("localhost:6363")?;
/// let mut sourced = SourcedXot::new(source)?;
///
/// // Load children explicitly
/// let root = sourced.root();
/// sourced.load_children(root)?;
///
/// // Now navigate using regular Xot methods
/// let doc_element = sourced.xot().document_element(root)?;
/// ```
pub struct SourcedXot<S: DataSource> {
    /// The underlying Xot instance (used as cache)
    xot: Xot,
    /// The external data source
    source: S,
    /// Mapping between external IDs and internal NodeIds
    id_mapping: IdMapping<S::Id, NodeId>,
    /// Set of nodes whose children have been loaded
    children_loaded: HashSet<NodeId>,
    /// The external ID of the root document
    root_external_id: S::Id,
    /// The internal NodeId of the root document
    root_node: Node,
}

impl<S: DataSource> SourcedXot<S> {
    /// Create a new SourcedXot from a data source.
    ///
    /// This fetches the root document node from the source and creates
    /// an empty document structure. Call `load_children` to populate.
    pub fn new(source: S) -> Result<Self, SourcedError> {
        let mut xot = Xot::new();
        let mut id_mapping = IdMapping::new();

        // Get the root from the source
        let root_external_id = source.root()?;

        // Fetch the root node data to verify it's a Document
        let raw_root = source.fetch_node(&root_external_id)?;
        if !matches!(raw_root.kind, RawNodeKind::Document) {
            return Err(SourcedError::Source(SourceError::DataError(
                "Root node must be a Document".to_string(),
            )));
        }

        // Create an empty document in Xot
        let root_node = xot.new_document();

        // Map the external root ID to the internal root
        id_mapping.insert(root_external_id.clone(), root_node.get());

        Ok(Self {
            xot,
            source,
            id_mapping,
            children_loaded: HashSet::new(),
            root_external_id,
            root_node,
        })
    }

    /// Get read-only access to the underlying Xot.
    pub fn xot(&self) -> &Xot {
        &self.xot
    }

    /// Get mutable access to the underlying Xot.
    ///
    /// **Warning**: Modifying the Xot directly may cause inconsistencies
    /// with the external source. Use with caution.
    pub fn xot_mut(&mut self) -> &mut Xot {
        &mut self.xot
    }

    /// Get the root document node.
    pub fn root(&self) -> Node {
        self.root_node
    }

    /// Get the data source.
    pub fn source(&self) -> &S {
        &self.source
    }

    /// Check if a node's children have been loaded.
    pub fn children_loaded(&self, node: Node) -> bool {
        self.children_loaded.contains(&node.get())
    }

    /// Load a node's children from the external source.
    ///
    /// After this call, you can use `xot().children(node)` etc.
    pub fn load_children(&mut self, node: Node) -> Result<(), SourcedError> {
        if self.children_loaded.contains(&node.get()) {
            return Ok(());
        }

        let node_id = node.get();
        let external_id = self.id_mapping
            .get_external(node_id)
            .cloned()
            .ok_or_else(|| SourcedError::NodeNotCached(format!("{:?}", node_id)))?;

        // Fetch relationships from source
        let relationships = self.source.fetch_relationships(&external_id)?;

        // Load and attach each child
        for child_ext_id in &relationships.children {
            let child_node = self.load_or_get_node(child_ext_id)?;

            // Attach child to parent in the arena
            self.xot.append(node, child_node)?;
        }

        self.children_loaded.insert(node_id);
        Ok(())
    }

    /// Load a node from the external source, or return it if already cached.
    fn load_or_get_node(&mut self, external_id: &S::Id) -> Result<Node, SourcedError> {
        // Check if already loaded
        if let Some(node_id) = self.id_mapping.get_internal(external_id) {
            return Ok(Node::new(node_id));
        }

        // Fetch from source
        let raw_node = self.source.fetch_node(external_id)?;

        // Convert to Value
        let value = self.convert_raw_node(&raw_node)?;

        // Create the node in Xot
        let new_node = self.xot.new_node(value);

        // Record the mapping
        self.id_mapping.insert(external_id.clone(), new_node.get());

        Ok(new_node)
    }

    /// Convert a RawNode to a Xot Value.
    fn convert_raw_node(&mut self, raw: &RawNode<S::Id>) -> Result<Value, SourcedError> {
        match &raw.kind {
            RawNodeKind::Document => Ok(Value::Document),

            RawNodeKind::Element { name, namespace } => {
                let name_id = if let Some(ns) = namespace {
                    let ns_id = self.xot.add_namespace(ns);
                    self.xot.add_name_ns(name, ns_id)
                } else {
                    self.xot.add_name(name)
                };
                Ok(Value::Element(Element { name_id }))
            }

            RawNodeKind::Text { content } => {
                Ok(Value::Text(Text::new(content.clone())))
            }

            RawNodeKind::Comment { content } => {
                Ok(Value::Comment(Comment::new(content.clone())))
            }

            RawNodeKind::ProcessingInstruction { target, data } => {
                let target_id = self.xot.add_name(target);
                Ok(Value::ProcessingInstruction(ProcessingInstruction::new(
                    target_id,
                    data.clone(),
                )))
            }

            RawNodeKind::Attribute { name, namespace, value } => {
                let name_id = if let Some(ns) = namespace {
                    let ns_id = self.xot.add_namespace(ns);
                    self.xot.add_name_ns(name, ns_id)
                } else {
                    self.xot.add_name(name)
                };
                Ok(Value::Attribute(Attribute { name_id, value: value.clone() }))
            }

            RawNodeKind::Namespace { prefix, uri } => {
                let prefix_id = self.xot.add_prefix(prefix);
                let namespace_id = self.xot.add_namespace(uri);
                Ok(Value::Namespace(Namespace { prefix_id, namespace_id }))
            }
        }
    }

    /// Load a specific node by its external ID.
    pub fn load_node(&mut self, external_id: &S::Id) -> Result<Node, SourcedError> {
        self.load_or_get_node(external_id)
    }

    /// Get the internal Node for an external ID if it's already loaded.
    pub fn get_cached_node(&self, external_id: &S::Id) -> Option<Node> {
        self.id_mapping.get_internal(external_id).map(Node::new)
    }

    /// Get the external ID for an internal Node.
    pub fn get_external_id(&self, node: Node) -> Option<S::Id> {
        self.id_mapping.get_external(node.get()).cloned()
    }

    /// Load the entire subtree rooted at a node.
    pub fn load_subtree(&mut self, node: Node) -> Result<(), SourcedError> {
        self.load_children(node)?;

        // Recursively load children's children
        let children: Vec<_> = self.xot.children(node).collect();
        for child in children {
            self.load_subtree(child)?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::source::RawRelationships;

    // A simple in-memory data source for testing
    struct TestSource {
        nodes: std::collections::HashMap<String, (RawNode<String>, RawRelationships<String>)>,
        root_id: String,
    }

    impl DataSource for TestSource {
        type Id = String;

        fn root(&self) -> Result<Self::Id, SourceError> {
            Ok(self.root_id.clone())
        }

        fn fetch_node(&self, id: &Self::Id) -> Result<RawNode<Self::Id>, SourceError> {
            self.nodes
                .get(id)
                .map(|(node, _)| node.clone())
                .ok_or_else(|| SourceError::NotFound(id.clone()))
        }

        fn fetch_relationships(&self, id: &Self::Id) -> Result<RawRelationships<Self::Id>, SourceError> {
            self.nodes
                .get(id)
                .map(|(_, rel)| rel.clone())
                .ok_or_else(|| SourceError::NotFound(id.clone()))
        }
    }

    #[test]
    fn test_sourced_xot_creation() {
        let mut nodes = std::collections::HashMap::new();
        nodes.insert(
            "doc".to_string(),
            (
                RawNode {
                    id: "doc".to_string(),
                    kind: RawNodeKind::Document,
                },
                RawRelationships {
                    parent: None,
                    children: vec!["root".to_string()],
                    previous_sibling: None,
                    next_sibling: None,
                },
            ),
        );
        nodes.insert(
            "root".to_string(),
            (
                RawNode {
                    id: "root".to_string(),
                    kind: RawNodeKind::Element {
                        name: "root".to_string(),
                        namespace: None,
                    },
                },
                RawRelationships {
                    parent: Some("doc".to_string()),
                    children: vec![],
                    previous_sibling: None,
                    next_sibling: None,
                },
            ),
        );

        let source = TestSource {
            nodes,
            root_id: "doc".to_string(),
        };

        let result = SourcedXot::new(source);
        assert!(result.is_ok());
    }

    #[test]
    fn test_sourced_xot_load_children() {
        let mut nodes = std::collections::HashMap::new();
        nodes.insert(
            "doc".to_string(),
            (
                RawNode {
                    id: "doc".to_string(),
                    kind: RawNodeKind::Document,
                },
                RawRelationships {
                    parent: None,
                    children: vec!["root".to_string()],
                    previous_sibling: None,
                    next_sibling: None,
                },
            ),
        );
        nodes.insert(
            "root".to_string(),
            (
                RawNode {
                    id: "root".to_string(),
                    kind: RawNodeKind::Element {
                        name: "root".to_string(),
                        namespace: None,
                    },
                },
                RawRelationships {
                    parent: Some("doc".to_string()),
                    children: vec!["child1".to_string(), "child2".to_string()],
                    previous_sibling: None,
                    next_sibling: None,
                },
            ),
        );
        nodes.insert(
            "child1".to_string(),
            (
                RawNode {
                    id: "child1".to_string(),
                    kind: RawNodeKind::Element {
                        name: "child".to_string(),
                        namespace: None,
                    },
                },
                RawRelationships {
                    parent: Some("root".to_string()),
                    children: vec![],
                    previous_sibling: None,
                    next_sibling: Some("child2".to_string()),
                },
            ),
        );
        nodes.insert(
            "child2".to_string(),
            (
                RawNode {
                    id: "child2".to_string(),
                    kind: RawNodeKind::Text {
                        content: "Hello, world!".to_string(),
                    },
                },
                RawRelationships {
                    parent: Some("root".to_string()),
                    children: vec![],
                    previous_sibling: Some("child1".to_string()),
                    next_sibling: None,
                },
            ),
        );

        let source = TestSource {
            nodes,
            root_id: "doc".to_string(),
        };

        let mut sourced = SourcedXot::new(source).unwrap();
        let root = sourced.root();

        // Initially children are not loaded
        assert!(!sourced.children_loaded(root));

        // Load children of root document
        sourced.load_children(root).unwrap();
        assert!(sourced.children_loaded(root));

        // Now we should have the root element as a child
        let doc_element = sourced.xot().document_element(root).unwrap();

        // Load children of root element
        sourced.load_children(doc_element).unwrap();

        // Check that we can navigate the loaded children
        let children: Vec<_> = sourced.xot().children(doc_element).collect();
        assert_eq!(children.len(), 2);

        // First child should be an element named "child"
        use crate::xmlvalue::Value;
        if let Value::Element(elem) = sourced.xot().value(children[0]) {
            let (local_name, _namespace) = sourced.xot().name_ns_str(elem.name_id);
            assert_eq!(local_name, "child");
        } else {
            panic!("Expected element");
        }

        // Second child should be text
        if let Value::Text(text) = sourced.xot().value(children[1]) {
            assert_eq!(text.get(), "Hello, world!");
        } else {
            panic!("Expected text");
        }
    }

    #[test]
    fn test_sourced_xot_load_subtree() {
        let mut nodes = std::collections::HashMap::new();
        nodes.insert(
            "doc".to_string(),
            (
                RawNode {
                    id: "doc".to_string(),
                    kind: RawNodeKind::Document,
                },
                RawRelationships {
                    parent: None,
                    children: vec!["root".to_string()],
                    previous_sibling: None,
                    next_sibling: None,
                },
            ),
        );
        nodes.insert(
            "root".to_string(),
            (
                RawNode {
                    id: "root".to_string(),
                    kind: RawNodeKind::Element {
                        name: "root".to_string(),
                        namespace: None,
                    },
                },
                RawRelationships {
                    parent: Some("doc".to_string()),
                    children: vec!["nested".to_string()],
                    previous_sibling: None,
                    next_sibling: None,
                },
            ),
        );
        nodes.insert(
            "nested".to_string(),
            (
                RawNode {
                    id: "nested".to_string(),
                    kind: RawNodeKind::Element {
                        name: "nested".to_string(),
                        namespace: None,
                    },
                },
                RawRelationships {
                    parent: Some("root".to_string()),
                    children: vec!["deep".to_string()],
                    previous_sibling: None,
                    next_sibling: None,
                },
            ),
        );
        nodes.insert(
            "deep".to_string(),
            (
                RawNode {
                    id: "deep".to_string(),
                    kind: RawNodeKind::Element {
                        name: "deep".to_string(),
                        namespace: None,
                    },
                },
                RawRelationships {
                    parent: Some("nested".to_string()),
                    children: vec![],
                    previous_sibling: None,
                    next_sibling: None,
                },
            ),
        );

        let source = TestSource {
            nodes,
            root_id: "doc".to_string(),
        };

        let mut sourced = SourcedXot::new(source).unwrap();
        let root = sourced.root();

        // Load entire subtree
        sourced.load_subtree(root).unwrap();

        // Now all levels should be loaded
        let doc_element = sourced.xot().document_element(root).unwrap();
        let nested = sourced.xot().first_child(doc_element).unwrap();
        let deep = sourced.xot().first_child(nested).unwrap();

        // Verify we can access the deepest element
        use crate::xmlvalue::Value;
        if let Value::Element(elem) = sourced.xot().value(deep) {
            let (local_name, _namespace) = sourced.xot().name_ns_str(elem.name_id);
            assert_eq!(local_name, "deep");
        } else {
            panic!("Expected element");
        }
    }
}
