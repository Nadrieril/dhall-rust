/// The beginning of a file path which anchors subsequent path components
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Directory {
    pub components: Vec<String>,
}

impl IntoIterator for Directory {
    type Item = String;
    type IntoIter = ::std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.components.into_iter()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct File {
    pub directory: Directory,
    pub file: String,
}

impl IntoIterator for File {
    type Item = String;
    type IntoIter = ::std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        let mut paths = self.directory.components;
        paths.push(self.file);
        paths.into_iter()
    }
}

/// The location of import (i.e. local vs. remote vs. environment)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ImportLocation {
    Local(FilePrefix, File),
    Remote(URL),
    Env(String),
    Missing,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct URL {
    pub scheme: Scheme,
    pub authority: String,
    pub path: File,
    pub query: Option<String>,
    // TODO: implement inline headers
    pub headers: Option<Box<ImportHashed>>,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Scheme {
    HTTP,
    HTTPS,
}

/// How to interpret the import's contents (i.e. as Dhall code or raw text)
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum ImportMode {
    Code,
    RawText,
    Location,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Hash {
    SHA256(Vec<u8>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ImportHashed {
    pub location: ImportLocation,
    pub hash: Option<Hash>,
}

/// Reference to an external resource
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Import {
    pub mode: ImportMode,
    pub location_hashed: ImportHashed,
}

pub trait Canonicalize {
    fn canonicalize(&self) -> Self;
}

impl Canonicalize for Directory {
    fn canonicalize(&self) -> Directory {
        let mut components = Vec::new();
        let mut dir_components = self.clone().into_iter();

        loop {
           let component = dir_components.next();
           match component.as_ref() {
               // ───────────────────
               // canonicalize(ε) = ε
               None => break,

               // canonicalize(directory₀) = directory₁
               // ───────────────────────────────────────
               // canonicalize(directory₀/.) = directory₁
               Some(c) if c == "." => continue,

               Some(c) if c == ".." => match dir_components.next() {
                   // canonicalize(directory₀) = ε
                   // ────────────────────────────
                   // canonicalize(directory₀/..) = /..
                   None => components.push("..".to_string()),

                   // canonicalize(directory₀) = directory₁/..
                   // ──────────────────────────────────────────────
                   // canonicalize(directory₀/..) = directory₁/../..
                   Some(ref c) if c == ".." => {
                       components.push("..".to_string());
                       components.push("..".to_string());
                   },

                   // canonicalize(directory₀) = directory₁/component
                   // ───────────────────────────────────────────────  ; If "component" is not
                   // canonicalize(directory₀/..) = directory₁         ; ".."
                   Some(_) => continue,
               },

               // canonicalize(directory₀) = directory₁
               // ─────────────────────────────────────────────────────────  ; If no other
               // canonicalize(directory₀/component) = directory₁/component  ; rule matches
               Some(c) => components.push(c.clone()),
           }
        }

        Directory { components: components }
    }
}

impl Canonicalize for File {
    fn canonicalize(&self) -> File {
        File { directory: self.directory.canonicalize(), file: self.file.clone() }
    }
}

impl Canonicalize for ImportLocation {
    fn canonicalize(&self) -> ImportLocation {
        match self {
            ImportLocation::Local(prefix, file) => ImportLocation::Local(*prefix, file.canonicalize()),
            ImportLocation::Remote(url) => ImportLocation::Remote(URL {
                    scheme: url.scheme,
                    authority: url.authority.clone(),
                    path: url.path.canonicalize(),
                    query: url.query.clone(),
                    headers: url.headers.clone().map(|boxed_hash| Box::new(boxed_hash.canonicalize())),
            }),
            ImportLocation::Env(name) => ImportLocation::Env(name.to_string()),
            ImportLocation::Missing => ImportLocation::Missing,
        }
    }
}

impl Canonicalize for ImportHashed {
    fn canonicalize(&self) -> ImportHashed {
        ImportHashed { hash: self.hash.clone(), location: self.location.canonicalize() }
    }
}

impl Canonicalize for Import {
    fn canonicalize(&self) -> Import {
        Import { mode: self.mode, location_hashed: self.location_hashed.canonicalize() }
    }
}
