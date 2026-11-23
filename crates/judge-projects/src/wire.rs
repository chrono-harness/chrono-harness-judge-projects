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
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "kebab-case", deny_unknown_fields)]
pub enum Scope {
    Unit { unit: String },
    Collect { manifest: String },
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Unit {
    pub tests: Vec<String>,
    pub report_path: String,
}
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ArtifactTransport {
    pub source_directory: String,
    pub directory: String,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FullManifest {
    pub schema: String,
    pub reports: Vec<ReportInput>,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReportInput {
    pub unit: String,
    pub path: String,
    pub sha256: String,
    pub runner_sha256: Option<String>,
    pub judge_sha256: Option<String>,
    pub artifacts: Option<ArtifactTransport>,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Request {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub scope: Option<Scope>,
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

/// Resolve the invocation name before the native process service is available.
pub(crate) fn resolve_program(
    root: &Path,
    program: &str,
    search: Option<&str>,
) -> Result<PathBuf, String> {
    let root = std::path::absolute(root).map_err(|error| error.to_string())?;
    let path = Path::new(program);
    let candidate = if path.is_absolute() || program.contains('/') {
        Some(root.join(path)).filter(|p| p.is_file())
    } else {
        let search = search
            .map(std::ffi::OsString::from)
            .or_else(|| std::env::var_os("PATH"))
            .ok_or("PATH is missing")?;
        std::env::split_paths(&search)
            .map(|dir| root.join(dir).join(program))
            .find(|p| p.is_file())
    };
    candidate.ok_or_else(|| format!("executable not found: {program}"))
}

pub(crate) fn file_identity(path: &Path) -> Result<(String, u64), String> {
    let error = |err| format!("{}: {err}", path.display());
    let invalid = || format!("not a regular input file: {}", path.display());
    if !path.metadata().map_err(error)?.is_file() {
        return Err(invalid());
    }
    let mut file = std::fs::File::open(path).map_err(error)?;
    if !file.metadata().map_err(error)?.is_file() {
        return Err(invalid());
    }
    let mut digest = Sha256::new();
    let length = std::io::copy(&mut file, &mut digest).map_err(error)?;
    Ok((format!("{:x}", digest.finalize()), length))
}

pub(crate) fn paths_overlap(a: &str, b: &str) -> bool {
    let (a, b) = (Path::new(a), Path::new(b));
    a.starts_with(b) || b.starts_with(a)
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Tool {
    pub program: String,
    pub path: PathBuf,
    pub basename: String,
    pub sha256: String,
    pub version: ProcessResult,
}

/// Wire receipt consumed by read-results-v1, including structured failures of an original process.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ProcessResult {
    pub argv: Vec<String>,
    pub cwd: PathBuf,
    pub environment: std::collections::BTreeMap<String, String>,
    pub environment_digest: String,
    /// Actual process-engine capability carrier, separate from declared inputs.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub ownership_fds: Option<String>,
    pub stdin_sha256: String,
    pub stdout_bytes: Vec<u8>,
    pub stderr_bytes: Vec<u8>,
    #[serde(default)]
    pub stdout_complete: bool,
    #[serde(default)]
    pub stderr_complete: bool,
    pub stdout_sha256: String,
    pub stderr_sha256: String,
    pub failure: Option<String>,
    /// Structured failure evidence is additive to the historical string.  It
    /// is deliberately outside the judge-v1 request/response wire contract.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub failure_record: Option<ErrorRecord>,
    pub exit_code: i32,
    /// Actual process-owner drain and direct join, independent of command success.
    #[serde(default)]
    pub owned_work_joined: bool,
    /// Actual terminal signal, including cancellation; exit_code keeps its wire meaning.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub exit_signal: Option<i32>,
    pub stdout: String,
    pub stderr: String,
    pub executable: PathBuf,
    pub sha256: String,
    /// Retained process records bind the launch identity to this receipt.
    /// These fields are optional only for historical inline records.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub launcher_pid: Option<u32>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub child_pid: Option<u32>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub timeout_seconds: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub output_limit_bytes: Option<usize>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub launch_original: Option<Value>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ErrorRecord {
    schema: ErrorSchema,
    error: ErrorNode,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
enum ErrorSchema {
    #[serde(rename = "chrono-error/v1")]
    V1,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct ErrorNode {
    #[serde(rename = "type")]
    kind: String,
    code: String,
    message: String,
    context: BTreeMap<String, Value>,
    source: Option<Box<ErrorNode>>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    native_code: Option<i64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    traceback: Option<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    related: Vec<RelatedError>,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct RelatedError {
    role: String,
    error: ErrorNode,
}
