//! External data source abstraction for xot.
//!
//! This module provides traits and types for loading XML data from external
//! sources (like TerminusDB) into Xot's internal representation.
//!
//! # Overview
//!
//! - [`DataSource`]: Trait for external data providers
//! - [`SourcedXot`]: Wrapper combining Xot cache with external data source
//! - [`RawNode`], [`RawNodeKind`]: Raw node data before conversion
//! - [`IdMapping`]: Bidirectional external ↔ internal ID mapping

mod source;
mod sourced;

pub use source::{DataSource, ExternalId, IdMapping, RawNode, RawNodeKind, RawRelationships, SourceError};
pub use sourced::{SourcedXot, SourcedError};
