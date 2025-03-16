use gix_attributes;
use std::borrow::Cow;
use std::io;
use std::path::Path;
use std::path::PathBuf;
use std::sync::Arc;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum GitAttributesError {
    #[error("Failed to read ignore patterns from file {path}")]
    ReadFile { path: PathBuf, source: io::Error },
}

/// Models the effective contents of multiple .gitignore files.
#[derive(Debug)]
pub struct GitAttributesFile {
    search: gix_attributes::Search,
    collection: gix_attributes::search::MetadataCollection,
}

impl GitAttributesFile {
    /// Concatenates new `.gitattributes` file.
    pub fn chain_with_buffer(
        self: &Arc<GitAttributesFile>,
        bytes: &[u8],
        file: PathBuf,
    ) -> Arc<GitAttributesFile> {
        let mut search = self.search.clone();
        let mut collection = self.collection.clone();
        search.add_patterns_buffer(
            bytes,
            file.clone(),
            Some(Path::new(".")),
            &mut collection,
            true,
        );
        Arc::new(GitAttributesFile { search, collection })
    }

    /// Concatenates new `.gitattributes` file.
    pub fn chain_with_file(
        self: &Arc<GitAttributesFile>,
        file: PathBuf,
    ) -> Result<Arc<GitAttributesFile>, GitAttributesError> {
        if file.is_file() {
            let mut buf = Vec::new();
            let mut search = self.search.clone();
            let mut collection = self.collection.clone();
            search
                .add_patterns_file(
                    file.clone(),
                    true,
                    Some(Path::new(".")),
                    &mut buf,
                    &mut collection,
                    true,
                )
                .map_err(|err| GitAttributesError::ReadFile {
                    path: file.clone(),
                    source: err,
                })?;
            Ok(Arc::new(GitAttributesFile { search, collection }))
        } else {
            Ok(self.clone())
        }
    }

    pub fn matches(&self, path: &str) -> bool {
        //If path ends with slash, consider it as a directory.
        let (path, is_dir) = match path.strip_suffix('/') {
            Some(path) => (path, true),
            None => (path, false),
        };

        let mut out = gix_attributes::search::Outcome::default();
        out.initialize_with_selection(&self.collection, ["filter"]);
        self.search.pattern_matching_relative_path(
            path.into(),
            gix_glob::pattern::Case::Sensitive,
            Some(is_dir),
            &mut out,
        );

        let is_lfs = out
            .iter_selected()
            .filter_map(|attr| {
                if let gix_attributes::StateRef::Value(value_ref) = attr.assignment.state {
                    Some(value_ref.as_bstr())
                } else {
                    None
                }
            })
            .any(|value| value == "lfs");
        is_lfs
    }
}

impl Default for GitAttributesFile {
    fn default() -> Self {
        let files = [
            gix_attributes::Source::GitInstallation,
            gix_attributes::Source::System,
            gix_attributes::Source::Git,
            gix_attributes::Source::Local,
        ]
        .iter()
        .filter_map(|source| {
            source
                .storage_location(&mut gix_path::env::var)
                .and_then(|p| p.is_file().then_some(p))
                .map(Cow::into_owned)
        });

        let mut buf = Vec::new();
        let mut collection = gix_attributes::search::MetadataCollection::default();
        let search = gix_attributes::Search::new_globals(files, &mut buf, &mut collection)
            .unwrap_or_else(|_| gix_attributes::Search::default());

        GitAttributesFile { search, collection }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn matches_lfs(input: &[u8], path: &str) -> bool {
        let file = Arc::new(GitAttributesFile::default())
            .chain_with_buffer(input, PathBuf::from("test-attributes"));
        file.matches(path)
    }

    #[test]
    fn test_gitattributes_empty_file() {
        let file = GitAttributesFile::default();
        assert!(!file.matches("foo"));
    }

    #[test]
    fn test_gitattributes_basic_lfs() {
        assert!(matches_lfs(b"*.bin filter=lfs\n", "test.bin"));
        assert!(!matches_lfs(b"*.bin filter=lfs\n", "test.txt"));
    }

    #[test]
    fn test_gitattributes_directory_patterns() {
        assert!(matches_lfs(b"assets/** filter=lfs\n", "assets/image.png"));
        assert!(matches_lfs(
            b"assets/** filter=lfs\n",
            "assets/subfolder/image.png"
        ));
        assert!(!matches_lfs(
            b"assets/** filter=lfs\n",
            "src/assets/image.png"
        ));
    }

    #[test]
    fn test_gitattributes_directory_matching() {
        // Test with trailing slash to indicate directory
        assert!(matches_lfs(b"assets/ filter=lfs\n", "assets/"));
        assert!(!matches_lfs(b"assets/ filter=lfs\n", "assets"));
    }

    #[test]
    fn test_gitattributes_chaining() {
        let base = GitAttributesFile::default();
        let first = Arc::new(base).chain_with_buffer(b"*.bin filter=lfs\n", PathBuf::from("first"));
        let second = Arc::new(first.clone())
            .chain_with_buffer(b"*.png filter=lfs\n", PathBuf::from("second"));

        assert!(!first.matches("test.png"));
        assert!(second.matches("test.bin"));
        assert!(second.matches("test.png"));
        assert!(!second.matches("test.txt"));
    }

    #[test]
    fn test_gitattributes_pattern_negation() {
        assert!(matches_lfs(
            b"*.bin filter=lfs\n!test.bin filter=lfs\n",
            "other.bin"
        ));
        assert!(!matches_lfs(
            b"*.bin filter=lfs\n!test.bin filter=-\n",
            "test.bin"
        ));
    }

    #[test]
    fn test_gitattributes_glob_patterns() {
        assert!(matches_lfs(b"*.{bin,dat} filter=lfs\n", "test.bin"));
        assert!(matches_lfs(b"*.{bin,dat} filter=lfs\n", "test.dat"));
        assert!(!matches_lfs(b"*.{bin,dat} filter=lfs\n", "test.txt"));
    }

    #[test]
    fn test_gitattributes_exact_path() {
        assert!(matches_lfs(
            b"/exact/path/file.bin filter=lfs\n",
            "exact/path/file.bin"
        ));
        assert!(!matches_lfs(
            b"/exact/path/file.bin filter=lfs\n",
            "different/path/file.bin"
        ));
    }

    #[test]
    fn test_gitattributes_other_attributes() {
        // Should not match when filter is not lfs
        assert!(!matches_lfs(b"*.bin filter=text\n", "test.bin"));
        // Should not match when attribute is not filter
        assert!(!matches_lfs(b"*.bin diff=binary\n", "test.bin"));
    }
}
