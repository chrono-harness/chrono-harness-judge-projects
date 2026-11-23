//! Filesystem observations of the compiler outputs declared by the executed method.
use std::{fs, io::Read, path::Path};

pub(crate) struct DependencyIo<'a>(pub(crate) &'a Path);
impl chrono_harness::verified_verifier::sources::DependencyRead for DependencyIo<'_> {
    fn read(&self, path: &[u8], limit: u64) -> Result<Vec<u8>, String> {
        std::str::from_utf8(path)
            .map_err(|e| e.to_string())
            .and_then(|path| fs::File::open(self.0.join(path)).map_err(|e| e.to_string()))
            .and_then(|file| {
                let mut bytes = Vec::new();
                file.take(limit)
                    .read_to_end(&mut bytes)
                    .map(|_| bytes)
                    .map_err(|e| e.to_string())
            })
    }
}

impl chrono_harness::verified_verifier::ArtifactRead for DependencyIo<'_> {
    fn identity(&self, path: &[u8]) -> Result<(Vec<u8>, u64), String> {
        std::str::from_utf8(path)
            .map_err(|e| e.to_string())
            .and_then(|path| chrono_harness::no_symlink_parents(self.0, path))
            .and_then(|path| chrono_harness::file_identity(&path))
            .map(|(digest, length)| (digest.into_bytes(), length))
    }
}
