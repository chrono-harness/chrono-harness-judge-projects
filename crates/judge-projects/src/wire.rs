//! Project judge projections of chrono-judge/v1. The installed runner verifies request admission.
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::{
    collections::BTreeMap,
    path::{Path, PathBuf},
};

pub fn sha256(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}
pub fn digest<T: Serialize>(value: &T) -> Result<String, String> {
    serde_jcs::to_vec(value)
        .map(|bytes| sha256(&bytes))
        .map_err(|e| e.to_string())
}
pub fn is_digest(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(&c))
}
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord)]
#[serde(rename_all = "lowercase")]
pub enum Status {
    Pass,
    Warn,
    Fail,
    Error,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Finding {
    pub code: String,
    pub level: String,
    pub message: String,
    pub delta_refs: Vec<String>,
    pub causes: Vec<String>,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Evidence {
    pub path: String,
    pub sha256: String,
    pub kind: String,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Response {
    pub protocol: String,
    pub request_id: String,
    pub judge_id: String,
    pub status: Status,
    pub findings: Vec<Finding>,
    pub evidence: Vec<Evidence>,
    pub outputs: BTreeMap<String, Value>,
}
pub fn append_finding(
    status: &mut Status,
    findings: &mut Vec<Finding>,
    severity: Status,
    finding: Finding,
) {
    if severity > *status {
        *status = severity;
    }
    findings.push(finding);
}
#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Endpoint {
    pub commit: String,
    pub tree: String,
    pub root: PathBuf,
}
#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Registries {
    pub base: PathBuf,
    pub candidate: PathBuf,
    pub digest: String,
}
#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Context {
    pub path: PathBuf,
    pub sha256: String,
}
#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Executable {
    pub path: String,
    pub sha256: String,
    pub version: String,
}
#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Checkout {
    pub head: String,
    pub tracked: Vec<String>,
    pub untracked: Vec<String>,
    pub index_flags: Vec<IndexFlag>,
}
#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct IndexFlag {
    pub path: String,
    pub tag: String,
}
#[derive(Debug, Serialize, Deserialize, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct Delta {
    pub kind: String,
    pub path: String,
    pub old_blob: Option<String>,
    pub new_blob: Option<String>,
    pub old_mode: Option<String>,
    pub new_mode: Option<String>,
}
#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Request {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub scope: Option<chrono_harness::units::Scope>,
    #[serde(default)]
    pub observations: Value,
    pub protocol: String,
    pub request_id: String,
    pub judge_id: String,
    pub mode: String,
    pub base: Endpoint,
    pub candidate: Endpoint,
    pub delta: Vec<Delta>,
    pub registries: Registries,
    pub context: Context,
    pub impact: Value,
    pub prior_results: Vec<Response>,
    pub config_path: String,
    pub checkout: Checkout,
    pub runner: Executable,
}
impl Request {
    pub fn validate_at(&self, root: &Path, runner: &Path) -> Result<(), String> {
        let mut reader = crate::runtime_session::Session::open(root, runner, "judge-evidence-v1")?;
        reader.call::<()>(json!({"operation":"validate-request","request":self}))?;
        reader.close()
    }
    pub fn response(&self, status: Status) -> Response {
        Response {
            protocol: "chrono-judge/v1".into(),
            request_id: self.request_id.clone(),
            judge_id: self.judge_id.clone(),
            status,
            findings: Vec::new(),
            evidence: Vec::new(),
            outputs: BTreeMap::new(),
        }
    }
}
