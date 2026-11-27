//! Project judge projections of chrono-judge/v1. The installed runner verifies request admission.
#![allow(unexpected_cfgs)]
#[cfg(not(verus_keep_ghost))]
use vstd::prelude::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

verus! {

/// Each step consumes one complete Unix path component supplied by std::path.
pub trait Components<'a> {
    spec fn rest(&self) -> Seq<Seq<u8>>;
    fn next_component(&mut self) -> (next: Option<&'a [u8]>)
        ensures match next {
            None => old(self).rest().len() == 0 && self.rest().len() == 0,
            Some(bytes) => old(self).rest().len() > 0 && bytes@ == old(self).rest()[0]
                && self.rest() == old(self).rest().skip(1),
        };
}

pub open spec fn nested(a: Seq<Seq<u8>>, b: Seq<Seq<u8>>) -> bool {
    forall|i: int| 0 <= i < a.len() && i < b.len() ==> #[trigger] a[i] == #[trigger] b[i]
}

fn same_component(a: &[u8], b: &[u8]) -> (same: bool)
    ensures same == (a@ == b@),
{
    if a.len() != b.len() { return false; }
    let mut i = 0;
    while i < a.len()
        invariant i <= a.len(), a.len() == b.len(),
            forall|j:int| 0 <= j < i ==> #[trigger] a@[j] == #[trigger] b@[j],
        decreases a.len() - i,
    {
        if a[i] != b[i] { return false; }
        i += 1;
    }
    assert(a@ =~= b@);
    true
}

/// Equal paths and either direction of ancestry share their entire shorter prefix.
pub fn component_overlap<'a, 'b, A: Components<'a>, B: Components<'b>>(first: A, second: B) -> (overlaps: bool)
    ensures overlaps == nested(first.rest(), second.rest()),
{
    let ghost left = first.rest();
    let ghost right = second.rest();
    let mut a = first;
    let mut b = second;
    let ghost mut consumed: nat = 0;
    loop
        invariant left == first.rest(), right == second.rest(), consumed <= left.len(), consumed <= right.len(),
            a.rest() == left.skip(consumed as int), b.rest() == right.skip(consumed as int),
            forall|i:int| 0 <= i < consumed ==> #[trigger] left[i] == #[trigger] right[i],
        decreases a.rest().len(),
    {
        let Some(x) = a.next_component() else { return true; };
        let Some(y) = b.next_component() else { return true; };
        assert(left[consumed as int] == x@ && right[consumed as int] == y@);
        if !same_component(x, y) { return false; }
        proof {
            consumed = consumed + 1;
            assert(a.rest() =~= left.skip(consumed as int));
            assert(b.rest() =~= right.skip(consumed as int));
        }
    }
}
}

#[cfg(not(verus_keep_ghost))]
impl<'a> Components<'a> for std::path::Components<'a> {
    fn next_component(&mut self) -> Option<&'a [u8]> {
        self.next().map(|part| part.as_os_str().as_encoded_bytes())
    }
}

#[cfg(not(verus_keep_ghost))]
pub(crate) fn paths_overlap(a: &str, b: &str) -> bool {
    component_overlap(
        std::path::Path::new(a).components(),
        std::path::Path::new(b).components(),
    )
}
#[cfg(not(verus_keep_ghost))]
use serde::{Deserialize, Serialize};
#[cfg(not(verus_keep_ghost))]
use serde_json::{Value, json};
#[cfg(not(verus_keep_ghost))]
use sha2::{Digest, Sha256};
#[cfg(not(verus_keep_ghost))]
use std::{
    collections::BTreeMap,
    path::{Path, PathBuf},
};

#[cfg(not(verus_keep_ghost))]
pub fn sha256(bytes: &[u8]) -> String {
    hex::encode(Sha256::digest(bytes))
}
#[cfg(not(verus_keep_ghost))]
pub fn digest<T: Serialize>(value: &T) -> Result<String, String> {
    serde_jcs::to_vec(value)
        .map(|bytes| sha256(&bytes))
        .map_err(|e| e.to_string())
}
#[cfg(not(verus_keep_ghost))]
pub fn is_digest(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(&c))
}
#[cfg(not(verus_keep_ghost))]
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord)]
#[serde(rename_all = "lowercase")]
pub enum Status {
    Pass,
    Warn,
    Fail,
    Error,
}

#[cfg(not(verus_keep_ghost))]
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Finding {
    pub code: String,
    pub level: String,
    pub message: String,
    pub delta_refs: Vec<String>,
    pub causes: Vec<String>,
}
#[cfg(not(verus_keep_ghost))]
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Evidence {
    pub path: String,
    pub sha256: String,
    pub kind: String,
}
#[cfg(not(verus_keep_ghost))]
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
#[cfg(not(verus_keep_ghost))]
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
#[cfg(not(verus_keep_ghost))]
#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Endpoint {
    pub commit: String,
    pub tree: String,
    pub root: PathBuf,
}
#[cfg(not(verus_keep_ghost))]
#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Registries {
    pub base: PathBuf,
    pub candidate: PathBuf,
    pub digest: String,
}
#[cfg(not(verus_keep_ghost))]
#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Context {
    pub path: PathBuf,
    pub sha256: String,
}
#[cfg(not(verus_keep_ghost))]
#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Executable {
    pub path: String,
    pub sha256: String,
    pub version: String,
}
#[cfg(not(verus_keep_ghost))]
#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Checkout {
    pub head: String,
    pub tracked: Vec<String>,
    pub untracked: Vec<String>,
    pub index_flags: Vec<IndexFlag>,
}
#[cfg(not(verus_keep_ghost))]
#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct IndexFlag {
    pub path: String,
    pub tag: String,
}
#[cfg(not(verus_keep_ghost))]
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
#[cfg(not(verus_keep_ghost))]
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "kebab-case", deny_unknown_fields)]
pub enum Scope {
    Unit { unit: String },
    Collect { manifest: String },
}

#[cfg(not(verus_keep_ghost))]
#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Unit {
    pub tests: Vec<String>,
    pub report_path: String,
}
#[cfg(not(verus_keep_ghost))]
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ArtifactTransport {
    pub source_directory: String,
    pub directory: String,
}
#[cfg(not(verus_keep_ghost))]
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FullManifest {
    pub schema: String,
    pub reports: Vec<ReportInput>,
}
#[cfg(not(verus_keep_ghost))]
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

#[cfg(not(verus_keep_ghost))]
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
#[cfg(not(verus_keep_ghost))]
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
#[cfg(not(verus_keep_ghost))]
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

#[cfg(not(verus_keep_ghost))]
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
    let mut digest = digest_io::IoWrapper(Sha256::new());
    let length = std::io::copy(&mut file, &mut digest).map_err(error)?;
    Ok((hex::encode(digest.0.finalize()), length))
}

#[cfg(not(verus_keep_ghost))]
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Tool {
    pub program: String,
    pub path: PathBuf,
    pub basename: String,
    pub sha256: String,
    #[serde(serialize_with = "crate::routes::timeout_wire::observation")]
    pub version: ProcessResult,
}

/// Wire receipt consumed by read-results-v1, including structured failures of an original process.
#[cfg(not(verus_keep_ghost))]
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
    #[serde(deserialize_with = "crate::routes::timeout_wire::optional::deserialize")]
    pub timeout_seconds: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub output_limit_bytes: Option<usize>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub launch_original: Option<Value>,
}

#[cfg(not(verus_keep_ghost))]
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ErrorRecord {
    schema: ErrorSchema,
    error: ErrorNode,
}

#[cfg(not(verus_keep_ghost))]
#[derive(Clone, Debug, Serialize, Deserialize)]
enum ErrorSchema {
    #[serde(rename = "chrono-error/v1")]
    V1,
}

#[cfg(not(verus_keep_ghost))]
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
#[cfg(not(verus_keep_ghost))]
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct RelatedError {
    role: String,
    error: ErrorNode,
}
