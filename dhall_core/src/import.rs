use std::path::PathBuf;

/// The beginning of a file path which anchors subsequent path components
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FilePrefix {
    /// Absolute path
    Absolute,
    /// Path relative to .
    Here,
    /// Path relative to ..
    Parent,
    /// Path relative to ~
    Home,
}

/// The location of import (i.e. local vs. remote vs. environment)
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImportLocation {
    Local(FilePrefix, PathBuf),
    // TODO: other import types
}

/// How to interpret the import's contents (i.e. as Dhall code or raw text)
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImportMode {
    Code,
    // TODO
    // RawText,
}

/// Reference to an external resource
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Import {
    pub mode: ImportMode,
    pub location: ImportLocation,
    // TODO
    pub hash: Option<()>,
}
