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
pub struct File {
    pub file_path: Vec<String>,
}

/// The location of import (i.e. local vs. remote vs. environment)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ImportLocation<SubExpr> {
    Local(FilePrefix, File),
    Remote(URL<SubExpr>),
    Env(String),
    Missing,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct URL<SubExpr> {
    pub scheme: Scheme,
    pub authority: String,
    pub path: File,
    pub query: Option<String>,
    pub headers: Option<SubExpr>,
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

/// Reference to an external resource
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Import<SubExpr> {
    pub mode: ImportMode,
    pub location: ImportLocation<SubExpr>,
    pub hash: Option<Hash>,
}

impl<SE> URL<SE> {
    pub fn visit_subexpr<'a, Err, SE2>(
        &'a self,
        f: impl FnOnce(&'a SE) -> Result<SE2, Err>,
    ) -> Result<URL<SE2>, Err> {
        let headers = self.headers.as_ref().map(f).transpose()?;
        Ok(URL {
            scheme: self.scheme,
            authority: self.authority.clone(),
            path: self.path.clone(),
            query: self.query.clone(),
            headers,
        })
    }
}

impl<SE> ImportLocation<SE> {
    pub fn visit_subexpr<'a, Err, SE2>(
        &'a self,
        f: impl FnOnce(&'a SE) -> Result<SE2, Err>,
    ) -> Result<ImportLocation<SE2>, Err> {
        use ImportLocation::*;
        Ok(match self {
            Local(prefix, path) => Local(*prefix, path.clone()),
            Remote(url) => Remote(url.visit_subexpr(f)?),
            Env(env) => Env(env.clone()),
            Missing => Missing,
        })
    }
}

impl<SE> Import<SE> {
    pub fn visit_subexpr<'a, Err, SE2>(
        &'a self,
        f: impl FnOnce(&'a SE) -> Result<SE2, Err>,
    ) -> Result<Import<SE2>, Err> {
        Ok(Import {
            mode: self.mode,
            location: self.location.visit_subexpr(f)?,
            hash: self.hash.clone(),
        })
    }
}

pub trait Canonicalize {
    fn canonicalize(&self) -> Self;
}

impl Canonicalize for File {
    fn canonicalize(&self) -> File {
        let mut file_path = Vec::new();
        let mut file_path_components = self.file_path.clone().into_iter();

        loop {
           let component = file_path_components.next();
           match component {
               // ───────────────────
               // canonicalize(ε) = ε
               None => break,

               // canonicalize(directory₀) = directory₁
               // ───────────────────────────────────────
               // canonicalize(directory₀/.) = directory₁
               Some(c) if c == "." => continue,

               Some(c) if c == ".." => match file_path_components.next() {
                   // canonicalize(directory₀) = ε
                   // ────────────────────────────
                   // canonicalize(directory₀/..) = /..
                   None => file_path.push("..".to_string()),

                   // canonicalize(directory₀) = directory₁/..
                   // ──────────────────────────────────────────────
                   // canonicalize(directory₀/..) = directory₁/../..
                   Some(ref c) if c == ".." => {
                       file_path.push("..".to_string());
                       file_path.push("..".to_string());
                   },

                   // canonicalize(directory₀) = directory₁/component
                   // ───────────────────────────────────────────────  ; If "component" is not
                   // canonicalize(directory₀/..) = directory₁         ; ".."
                   Some(_) => continue,
               },

               // canonicalize(directory₀) = directory₁
               // ─────────────────────────────────────────────────────────  ; If no other
               // canonicalize(directory₀/component) = directory₁/component  ; rule matches
               Some(c) => file_path.push(c.clone()),
           }
        }

        File { file_path }
    }
}

impl<SubExpr: Copy> Canonicalize for ImportLocation<SubExpr>  {
    fn canonicalize(&self) -> ImportLocation<SubExpr> {
        match self {
            ImportLocation::Local(prefix, file) => ImportLocation::Local(*prefix, file.canonicalize()),
            ImportLocation::Remote(url) => ImportLocation::Remote(URL {
                    scheme: url.scheme,
                    authority: url.authority.clone(),
                    path: url.path.canonicalize(),
                    query: url.query.clone(),
                    headers: url.headers.clone(),
            }),
            ImportLocation::Env(name) => ImportLocation::Env(name.to_string()),
            ImportLocation::Missing => ImportLocation::Missing,
        }
    }
}
