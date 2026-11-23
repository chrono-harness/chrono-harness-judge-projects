//! Public compiler evidence emitted by the installed runner while the operation owns its files.
use serde::{Deserialize, Serialize};
use std::path::Path;

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct OutputContract {
    pub version: String,
    pub commit: String,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Artifact {
    pub path: Vec<u8>,
    pub sha256: Vec<u8>,
    pub length: u64,
}

#[derive(Default, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Observed {
    pub dependency: Option<Result<Vec<u8>, String>>,
    pub artifact: Option<Result<Artifact, String>>,
}

pub fn observe(
    root: &Path,
    runner: &Path,
    op: &crate::routes::Operation,
    process: &crate::wire::ProcessResult,
) -> Result<Observed, String> {
    let Some(contract) = &op.method.output_contract else {
        return Ok(Observed::default());
    };
    crate::commands::query(
        root,
        runner,
        "compiler-output-v1",
        &serde_json::json!({
            "operation":"observe","contract":contract,"argv":op.method.argv,"exit":process.exit_code,
            "process_failed":process.failure.is_some(),"limit":op.output_limit_bytes
        }),
    )
}
