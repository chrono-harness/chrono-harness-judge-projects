//! Pair admissibility and actual operation/test evidence. Selection remains FILEMAP-owned.
#![allow(unexpected_cfgs)]
#[cfg(not(verus_keep_ghost))]
use vstd::prelude::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

verus! {
/// Apply the scheduler's capacity, prerequisite and live-claim observations.
pub(crate) fn can_dispatch<W: FnOnce() -> bool, C: FnOnce() -> bool>(
    running: usize, limit: usize, waiting: W, conflict: C,
) -> (ready: bool)
    requires running < limit ==> waiting.requires(()),
        running < limit && waiting.ensures((), false) ==> conflict.requires(()),
    ensures running >= limit ==> !ready,
        running < limit ==> (
            (waiting.ensures((), true) && !ready)
            || (waiting.ensures((), false) && conflict.ensures((), !ready))),
{
    running < limit && !waiting() && !conflict()
}
}
#[cfg(not(verus_keep_ghost))]
mod commands;
#[cfg(not(verus_keep_ghost))]
mod compiler;
#[cfg(not(verus_keep_ghost))]
pub mod evidence_query;
#[cfg(not(verus_keep_ghost))]
pub mod execute_query;
#[cfg(not(verus_keep_ghost))]
mod git_reader;
#[cfg(not(verus_keep_ghost))]
mod impact;
#[cfg(not(verus_keep_ghost))]
pub use impact::decode as decode_impact;
#[cfg(not(verus_keep_ghost))]
mod pair_checks;
#[cfg(not(verus_keep_ghost))]
pub mod plan_trace;
#[cfg(not(verus_keep_ghost))]
mod receipt;
#[cfg(not(verus_keep_ghost))]
mod routes;
#[cfg(not(verus_keep_ghost))]
mod runtime_session;
#[cfg(not(verus_keep_ghost))]
mod state;
#[cfg(not(verus_keep_ghost))]
mod verified_languages;
#[cfg(not(verus_keep_ghost))]
mod verified_state;
#[cfg(not(verus_keep_ghost))]
pub use verified_state::query_exit;
#[cfg(not(verus_keep_ghost))]
pub mod wire;
#[cfg(not(verus_keep_ghost))]
use commands::Spec as CommandSpec;
#[cfg(not(verus_keep_ghost))]
use wire::{Finding, Request, Response, Status};
#[cfg(not(verus_keep_ghost))]
mod registration;
#[cfg(not(verus_keep_ghost))]
pub use receipt::Receipt;
#[cfg(not(verus_keep_ghost))]
use registration::Registry;
#[cfg(not(verus_keep_ghost))]
use routes::{Dispatch, Execution, Routes};
#[cfg(not(verus_keep_ghost))]
use serde::{Deserialize, Serialize};
#[cfg(not(verus_keep_ghost))]
use serde_json::{Value, json};
#[cfg(not(verus_keep_ghost))]
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::Path,
};
#[cfg(not(verus_keep_ghost))]
pub type OperationResult = verified_state::OperationRow<Receipt, Value>;
#[cfg(not(verus_keep_ghost))]
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Results {
    pub plan: String,
    pub selected: Vec<String>,
    pub executed: Vec<OperationResult>,
    pub blocked: Vec<OperationResult>,
    pub tests: BTreeMap<String, String>,
    pub removed: BTreeMap<String, Option<String>>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub scope: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub completion: Option<CollectedCompletion>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub operation_state: Option<Value>,
}

#[cfg(not(verus_keep_ghost))]
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CollectedCompletion {
    pub schema: String,
    pub status: String,
    pub reports: Vec<Value>,
    pub global_selected: Vec<String>,
    pub required_units: Vec<String>,
    pub test_sources: BTreeMap<String, Vec<String>>,
    pub removal_sources: BTreeMap<String, Vec<String>>,
    pub source: String,
    pub source_sha256: String,
    pub tools: Value,
    pub warnings: Vec<Value>,
}
#[cfg(not(verus_keep_ghost))]
impl Results {
    pub fn has_errors(&self) -> bool {
        verified_state::has_execution_error(&self.executed)
    }
    pub fn passed(&self) -> bool {
        evidence_query::report_passed(
            &self.executed,
            self.blocked.len(),
            &self.selected,
            &self.tests,
        )
    }
}
/// Execute a plan admitted by the installed routes judge.
#[cfg(not(verus_keep_ghost))]
fn execute(
    plan: &Execution,
    routes: &Routes,
    dispatch: &Dispatch,
    runner: &Path,
) -> Result<Results, String> {
    let state = state::Run::begin(plan, runner)?;
    let plan_original = &state.plan_original;
    let span = tracing::info_span!("projects.execution", plan = plan.identity);
    let _entered = span.enter();
    tracing::info!(
        event_id = "projects.execution_started",
        "registered execution started"
    );
    let mut statuses: BTreeMap<String, String> = BTreeMap::new();
    let mut results = Results {
        plan: plan.identity.clone(),
        selected: plan.selected.keys().cloned().collect(),
        executed: vec![],
        blocked: vec![],
        tests: BTreeMap::new(),
        removed: BTreeMap::new(),
        scope: None,
        completion: None,
        operation_state: None,
    };
    // Scoped threads are joined even if a launch, receipt or worker fails. Claims
    // are acquired together by this sole coordinator, never inside workers.
    let rows = std::thread::scope(|scope| {
        let (tx, rx) = std::sync::mpsc::channel();
        let mut pending: BTreeSet<usize> = (0..plan.operations.len()).collect();
        let mut running = BTreeSet::new();
        let mut rows = BTreeMap::new();
        while !pending.is_empty() || !running.is_empty() {
            let mut progressed = false;
            for &index in &dispatch.order {
                if !pending.contains(&index) {
                    continue;
                }
                let op = &plan.operations[index];
                let prerequisites =
                    verified_state::prerequisite_status(&op.predecessors, &statuses);
                if prerequisites == verified_state::Prerequisites::Blocked {
                    tracing::info!(
                        event_id = "projects.operation_blocked",
                        operation = op.method.operation,
                        "failed prerequisite"
                    );
                    let row = OperationResult {
                        operation: op.method.operation.clone(),
                        status: "blocked".into(),
                        receipt: None,
                        error: Some("failed prerequisite".into()),
                        original: None,
                    };
                    statuses.insert(row.operation.clone(), row.status.clone());
                    rows.insert(index, row);
                    pending.remove(&index);
                    progressed = true;
                    continue;
                }
                if !can_dispatch(
                    running.len(),
                    dispatch.max_running.get(),
                    || prerequisites == verified_state::Prerequisites::Waiting,
                    || {
                        plan.scheduling.as_ref().is_some_and(|policy| {
                            running.iter().any(|i: &usize| {
                                policy.claims[&op.method.operation].overlaps(
                                    &policy.claims[&plan.operations[*i].method.operation],
                                    &routes::OutputPaths,
                                )
                            })
                        })
                    },
                ) {
                    continue;
                }
                pending.remove(&index);
                running.insert(index);
                progressed = true;
                let tx = tx.clone();
                let dispatch = tracing::dispatcher::get_default(Clone::clone);
                let parent = tracing::Span::current();
                tracing::info!(
                    event_id = "projects.operation_dispatched",
                    operation = op.method.operation,
                    "operation worker dispatched"
                );
                let launch = std::thread::Builder::new().spawn_scoped(scope, move || {
                    tracing::dispatcher::with_default(&dispatch, || {
                        let _parent = parent.enter();
                        let span = tracing::info_span!(
                            "projects.operation",
                            operation = op.method.operation
                        );
                        let _entered = span.enter();
                        tracing::info!(
                            event_id = "projects.operation_started",
                            "operation worker started"
                        );
                        let row = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                            execute_operation(plan, index, plan_original, routes, runner)
                        }))
                        .unwrap_or_else(|_| OperationResult {
                            operation: op.method.operation.clone(),
                            status: "error".into(),
                            receipt: None,
                            error: Some("operation worker panicked".into()),
                            original: None,
                        });
                        tracing::info!(
                            event_id = "projects.operation_completed",
                            status = row.status,
                            has_receipt = row.receipt.is_some(),
                            error = row.error.as_deref().unwrap_or(""),
                            "operation result available; enclosing execution may be incomplete"
                        );
                        let _ = tx.send((index, row));
                    });
                });
                if let Err(error) = launch {
                    running.remove(&index);
                    let row = OperationResult {
                        operation: op.method.operation.clone(),
                        status: "error".into(),
                        receipt: None,
                        error: Some(format!("operation worker launch: {error}")),
                        original: None,
                    };
                    statuses.insert(row.operation.clone(), row.status.clone());
                    rows.insert(index, row);
                }
            }
            if !running.is_empty() {
                let operations: Vec<_> = running
                    .iter()
                    .map(|i| &plan.operations[*i].method.operation)
                    .collect();
                tracing::info!(event_id = "projects.scheduler_wait", running_operations = %serde_json::to_string(&operations).expect("operation identities serialize"), "waiting for an owned worker result");
                let (index, row) = rx.recv().expect("owned workers always send terminal rows");
                running.remove(&index);
                statuses.insert(row.operation.clone(), row.status.clone());
                rows.insert(index, row);
            } else if !pending.is_empty() && !progressed {
                // Routes rejects cycles; a malformed retained graph is still a
                // pre-effect error through Execution::validate.
                unreachable!("validated operation graph has no ready work");
            }
        }
        tracing::info!(
            event_id = "projects.workers_join",
            "leaving scheduler scope; owned worker threads must still join"
        );
        rows
    });
    tracing::info!(
        event_id = "projects.workers_joined",
        "all operation workers joined"
    );
    for row in rows.into_values() {
        if row.status == "blocked" {
            results.blocked.push(row);
        } else {
            results.executed.push(row);
        }
    }
    for (test, p) in &plan.selected {
        verified_state::record_executed_test(&mut results.tests, test, &p.operations, &statuses);
    }
    state.finish(&mut results)?;
    Ok(results)
}

#[cfg(not(verus_keep_ghost))]
fn reported_coverage_cause(bytes: &[u8], complete: bool) -> Option<&str> {
    bytes.split(|&byte| byte == b'\n').find_map(|line| {
        let line = std::str::from_utf8(line.strip_suffix(b"\r").unwrap_or(line)).ok()?;
        let (code, detail) = line.split_once(": ")?;
        (verified_state::report_coverage_cause(complete, code, detail.len())
            && !detail.trim().is_empty()
            && !detail.chars().any(char::is_control))
        .then_some(line)
    })
}

#[cfg(not(verus_keep_ghost))]
fn execute_operation(
    plan: &Execution,
    index: usize,
    plan_original: &Value,
    routes: &Routes,
    runner: &Path,
) -> OperationResult {
    let op = &plan.operations[index];
    let mut state = None;
    let result = (|| {
        let tool = plan
            .tools
            .get(&op.method.tool)
            .ok_or("E_TOOL_BINDING: missing plan tool")?;
        let spec = CommandSpec {
            program: tool.path.to_str().ok_or("tool UTF-8")?.into(),
            args: op.method.argv.clone(),
            env: plan.environment.clone(),
            timeout_seconds: op.timeout_seconds,
            output_limit_bytes: op.output_limit_bytes,
        };
        state = Some(state::Operation::begin(plan, index, plan_original, runner)?);
        let process = state.as_ref().unwrap().execute(&spec, &tool.sha256)?;
        Receipt::observe(plan, op, process, runner)
    })();
    let (receipt, error, status) = match result {
        Ok(receipt) => {
            let infrastructure = routes
                .check_receipt(plan, op, &receipt)
                .err()
                .or_else(|| receipt.process.failure.clone());
            let (error, status) = if let Some(error) = infrastructure {
                (Some(error), "error")
            } else if receipt.process.exit_code != 0 {
                let process = &receipt.process;
                let exit = format!("operation exit {}", process.exit_code);
                let cause = reported_coverage_cause(&process.stderr_bytes, process.stderr_complete)
                    .or_else(|| {
                        reported_coverage_cause(&process.stdout_bytes, process.stdout_complete)
                    });
                let message = match cause {
                    Some(line) => format!("{line} ({exit})"),
                    None => exit,
                };
                (Some(message), "failed")
            } else {
                (None, "passed")
            };
            (Some(receipt), error, status)
        }
        Err(e) => (None, Some(e), "error"),
    };
    let mut row = OperationResult {
        operation: op.method.operation.clone(),
        status: status.into(),
        receipt,
        error,
        original: None,
    };
    if let Some(state) = state {
        match state.finish(&row) {
            Ok(original) => row.original = Some(original),
            Err(error) => {
                row.error = Some(format!(
                    "{}operation original publication: {error}",
                    row.error
                        .as_ref()
                        .map(|e| format!("{e}; "))
                        .unwrap_or_default()
                ));
                row.status = "error".into();
            }
        }
    }
    row
}
/// Validate the caller's affected pairs in a fixed project registry.
#[cfg(not(verus_keep_ghost))]
pub fn check_pairs(input: impl std::io::Read) -> Result<(), String> {
    check_pairs_with(input, |registry| {
        let root = std::env::current_dir().map_err(|e| e.to_string())?;
        registration::standalone(&root, registry)
    })
}

#[cfg(not(verus_keep_ghost))]
pub fn check_pairs_with(
    input: impl std::io::Read,
    validate: impl FnOnce(&Value) -> Result<(), String>,
) -> Result<(), String> {
    #[derive(Deserialize)]
    #[serde(deny_unknown_fields)]
    struct Query {
        registry: Value,
        owners: BTreeSet<String>,
    }
    let Query { registry, owners } =
        serde_json::from_reader(input).map_err(|error| error.to_string())?;
    validate(&registry)?;
    for (key, prefix, test_field) in [
        ("projects", "project", "test_project"),
        ("scripts", "script", "test_script"),
    ] {
        let collection = registry[key].as_array().unwrap();
        for row in collection {
            let id = row["id"].as_str().unwrap();
            if owners.contains(&format!("{prefix}:{id}")) {
                pair_checks::dedicated_pair(&registry, collection, prefix, test_field, row)?;
            }
        }
    }
    Ok(())
}

#[cfg(not(verus_keep_ghost))]
fn pairs(root: &Path, r: &Registry, affected: &BTreeSet<String>) -> Result<(), String> {
    let mut tests_for_owner: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
    for (test, rows) in &r.bindings {
        for row in rows {
            tests_for_owner.entry(&row.owner).or_default().push(test);
        }
    }
    pair_checks::check(
        root,
        r.projects(),
        &r.filemap,
        r.config()["artifacts"].as_array().unwrap(),
        affected,
        |node| {
            r.definitions
                .get(node)
                .into_iter()
                .flat_map(|node| node.iter().map(String::as_str))
                .collect()
        },
        &tests_for_owner,
    )
}
#[cfg(not(verus_keep_ghost))]
fn snapshot_with_reader(
    candidate: &str,
    artifacts: &[String],
    reader: &mut git_reader::Reader,
) -> Result<(), String> {
    let state = reader.checkout(artifacts)?;
    if state.head != candidate
        || !state.tracked.is_empty()
        || state
            .untracked
            .iter()
            .any(|p| !artifacts.iter().any(|a| p.starts_with(a.as_str())))
        || state.index_flags.iter().any(|f| {
            f.tag.as_bytes().first().is_some_and(u8::is_ascii_lowercase)
                || f.tag.eq_ignore_ascii_case("S")
        })
    {
        return Err("E_SNAPSHOT_DIRTY: operation changed candidate inputs".into());
    }
    Ok(())
}

#[cfg(not(verus_keep_ghost))]
fn check_selected_coverage(
    selected: &[String],
    results: &BTreeMap<String, String>,
) -> Result<(), String> {
    if let Some(test) = verified_state::uncovered_test(selected, results) {
        return Err(format!(
            "E_COLLECTION_INPUT: selected test coverage is missing or failed: {test}"
        ));
    }
    Ok(())
}

/// Validate transported full unit reports without invoking any business
/// operation.  The collector consumes the original sealed request and judge
/// observations retained by each unit; it never reconstructs or replays a
/// process locally.
#[cfg(not(verus_keep_ghost))]
fn collect_reports(
    req: &Request,
    plan: &Execution,
    selected: &BTreeSet<String>,
    registrations: &Registry,
    effective: &Value,
) -> Result<(Results, CollectedCompletion), String> {
    let wire::Scope::Collect { manifest } = req.scope.as_ref().ok_or("collection scope missing")?
    else {
        return Err("collection requires collect scope".into());
    };
    let units: BTreeMap<String, wire::Unit> =
        serde_json::from_value(req.observations["execution_units"]["units"].clone())
            .map_err(|e| format!("E_COLLECTION_INPUT: units: {e}"))?;
    let root = &req.candidate.root;
    let mut originals = runtime_session::Session::open(
        root,
        &registrations.runner(root)?,
        "retained-artifacts-v1",
    )?;
    let mut reader =
        runtime_session::Session::open(root, &registrations.runner(root)?, "judge-evidence-v1")?;
    let required: Vec<String> =
        reader.call(json!({"operation":"required-units","units":units,"selected":selected}))?;
    let manifest_path = manifest.clone();
    let report_path = req.observations["execution_units"]["report_path"]
        .as_str()
        .ok_or("E_COLLECTION_INPUT: full report path missing")?;
    let unit_paths: Vec<String> = units
        .values()
        .map(|unit| unit.report_path.clone())
        .collect();
    reader.call::<()>(json!({"operation":"collection-paths","manifest":manifest_path,"report":report_path,"units":unit_paths}))
        .map_err(|error| format!("E_COLLECTION_INPUT: {error}"))?;
    let limits = req.observations["execution_units"]["collection_limits"]
        .as_object()
        .ok_or("E_COLLECTION_INPUT: collection limits missing")?;
    let manifest_limit = limits["manifest_bytes"]
        .as_u64()
        .filter(|n| *n > 0 && *n <= 64 * 1024 * 1024)
        .ok_or("E_COLLECTION_INPUT: invalid manifest limit")?;
    let report_limit = limits["report_bytes"]
        .as_u64()
        .filter(|n| *n > 0 && *n <= 64 * 1024 * 1024)
        .ok_or("E_COLLECTION_INPUT: invalid report limit")?;
    let bytes = report_bytes(&mut originals, &manifest_path, None, manifest_limit)
        .map_err(|e| format!("E_COLLECTION_INPUT: manifest: {e}"))?;
    let manifest_sha256 = wire::sha256(&bytes);
    let manifest: wire::FullManifest = reader.decode(&bytes)?;
    if !matches!(
        manifest.schema.as_str(),
        "chrono-full-collection/v1" | "chrono-ci-collection/v1"
    ) {
        return Err("E_COLLECTION_INPUT: unsupported manifest schema".into());
    }
    let mut seen = BTreeSet::new();
    let mut paths = BTreeSet::from([manifest_path.clone()]);
    paths.insert(report_path.to_owned());
    let mut reports = vec![];
    let mut warnings = vec![];
    let mut tools = serde_json::Map::new();
    let mut tests = BTreeMap::<String, String>::new();
    let mut removed = BTreeMap::<String, Option<String>>::new();
    let mut test_sources = BTreeMap::<String, Vec<String>>::new();
    let mut removal_sources = BTreeMap::<String, Vec<String>>::new();
    for input in &manifest.reports {
        if !units.contains_key(&input.unit)
            || !seen.insert(input.unit.clone())
            || !wire::is_digest(&input.sha256)
        {
            return Err("E_COLLECTION_INPUT: unknown or duplicate unit report".into());
        }
        let expected_path: String = originals.call(json!({"operation":"resolve-original","original":{"path":units[&input.unit].report_path,"sha256":input.sha256},"transport":input.artifacts}))?;
        if input.path != expected_path {
            return Err(format!(
                "E_COLLECTION_INPUT: unit report path differs from registration: {}",
                input.unit
            ));
        }
        if !routes::reserve_report(&mut paths, &input.path, &routes::OutputPaths) {
            return Err("E_COLLECTION_INPUT: report path collision/overlap".into());
        }
        let report_bytes = report_bytes(&mut originals, &input.path, None, report_limit)
            .map_err(|e| format!("E_COLLECTION_INPUT: {}: {e}", input.unit))?;
        if wire::sha256(&report_bytes) != input.sha256 {
            return Err(format!(
                "E_COLLECTION_INPUT: report digest mismatch: {}",
                input.unit
            ));
        }
        let report = reader.decode::<Value>(&report_bytes)?;
        if reader.call::<u64>(json!({"operation":"report-transport-bytes", "report":report,"metadata_bytes": report_bytes.len()}))?
            > report_limit
        {
            return Err(
                "full unit metadata and original streams exceed registered report bound".into(),
            );
        }
        if input
            .runner_sha256
            .as_deref()
            .is_some_and(|pin| pin != req.runner.sha256)
            || input
                .judge_sha256
                .as_deref()
                .is_some_and(|pin| pin != report["judge_sha256"].as_str().unwrap_or_default())
        {
            return Err(format!(
                "E_COLLECTION_INPUT: supplied executable pin differs: {}",
                input.unit
            ));
        }
        if registrations.config()["schema_version"] == 4 {
            if let Some(transport) = &input.artifacts {
                originals.call::<()>(json!({"operation":"check-preparation","binding":report["request"]["observations"]["preparation"],"transport":transport}))?;
            }
        }
        let unit_results = validate_unit_report(
            &mut originals,
            &mut reader,
            req,
            registrations,
            &units,
            selected,
            &required,
            &input.unit,
            &report,
            &plan,
            effective,
            &req.candidate.root,
            input.artifacts.as_ref(),
            None,
        )?;
        for (test, status) in &unit_results.tests {
            if let Some(previous) = tests.insert(test.clone(), status.clone()) {
                if previous != *status {
                    return Err(format!(
                        "E_COLLECTION_INPUT: conflicting test coverage: {test}"
                    ));
                }
            }
            test_sources
                .entry(test.clone())
                .or_default()
                .push(input.unit.clone());
        }
        for (retired, replacement) in &unit_results.removed {
            if !verified_state::record_removal(
                &mut removed,
                &mut removal_sources,
                retired,
                replacement,
                &input.unit,
            ) {
                return Err(format!(
                    "E_COLLECTION_INPUT: conflicting removal coverage: {retired}"
                ));
            }
        }
        for finding in report["findings"].as_array().ok_or("unit findings")? {
            if finding["level"] == "warning" {
                warnings.push(json!({"unit":input.unit,"finding":finding}));
            }
        }
        let status = report["status"].as_str().unwrap_or("");
        if report["schema_version"] != 1
            || report["scope"] != "configured-judges"
            || !matches!(status, "pass" | "warn")
            || report["request"]["scope"] != serde_json::json!({"kind":"unit","unit":input.unit})
            || report["request"]["base"]["commit"] != req.base.commit
            || report["request"]["candidate"]["commit"] != req.candidate.commit
            || report["request"]["candidate"]["tree"] != req.candidate.tree
            || report["request"]["base"]["tree"] != req.base.tree
            || report["request"]["registries"]["digest"] != req.registries.digest
            || report["request"]["context"]["sha256"] != req.context.sha256
            || report["request"]["config_path"] != req.config_path
            || report["delta"] != serde_json::to_value(&req.delta).unwrap()
            || report["candidate_tree"] != req.candidate.tree
            || report["registry_digest"] != req.registries.digest
            || report["context_digest"] != req.context.sha256
        {
            return Err(format!(
                "E_COLLECTION_INPUT: stale or mismatched report: {}",
                input.unit
            ));
        }
        let judges = report["judges"]
            .as_array()
            .ok_or("E_COLLECTION_INPUT: report judges missing")?;
        if judges.is_empty() {
            return Err(format!(
                "E_COLLECTION_INPUT: incomplete judge evidence: {}",
                input.unit
            ));
        }
        let retained_artifacts: Value = originals.call(json!({"operation":"restage-map","artifacts":report["artifacts"],"transport":input.artifacts,"directory":".chrono-harness/state/imported/"}))?;
        let retained_path = format!(".chrono-harness/state/import-{}.json", input.sha256);
        let destination: std::path::PathBuf =
            originals.call(json!({"operation":"checked-path","path":retained_path}))?;
        match fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&destination)
        {
            Ok(mut file) => {
                use std::io::Write;
                file.write_all(&report_bytes).map_err(|e| e.to_string())?;
            }
            Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => {
                if fs::read(&destination).map_err(|e| e.to_string())? != report_bytes {
                    return Err("E_COLLECTION_INPUT: retained original replaced".into());
                }
            }
            Err(e) => return Err(e.to_string()),
        }
        for (id, observation) in unit_tools(&report)?
            .as_object()
            .ok_or("unit tool bindings")?
        {
            if let Some(previous) = tools.insert(id.clone(), observation.clone()) {
                if previous != *observation {
                    return Err("E_COLLECTION_INPUT: conflicting original tool observations".into());
                }
            }
        }
        reports.push(serde_json::json!({
            "unit": input.unit,
            "path": input.path,
            "retained_path": retained_path,
            "retained_artifacts": retained_artifacts,
            "sha256": input.sha256,
            "runner_sha256": req.runner.sha256,
            "judge_sha256": report["judge_sha256"],
            "status": status,
            "request_digest": report["request_digest"],
            "artifacts": input.artifacts,
        }));
    }
    if required.iter().any(|unit| !seen.contains(unit)) {
        return Err("E_COLLECTION_INPUT: missing required unit report".into());
    }
    let selected_ids: Vec<_> = selected.iter().cloned().collect();
    check_selected_coverage(&selected_ids, &tests)?;
    let requests = registrations.retirements.as_ref().map_err(Clone::clone)?;
    let deferred = registrations.downstream;
    for retired in req.impact["retired_tests"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(Value::as_str)
    {
        let id = retired.to_owned();
        let expected = verified_state::declared_removal(requests.get(&id), deferred)
            .ok_or_else(|| format!("E_REQUIRED_TEST_REMOVED: {retired}"))?;
        if !verified_state::record_removal(
            &mut removed,
            &mut removal_sources,
            &id,
            expected,
            "global-obligation",
        ) {
            return Err(format!(
                "E_COLLECTION_INPUT: removal obligation differs from registration: {retired}"
            ));
        }
    }
    let completion = CollectedCompletion {
        schema: "chrono-collected-completion/v1".into(),
        status: "passed".into(),
        reports,
        global_selected: selected_ids.clone(),
        required_units: required.clone(),
        test_sources,
        removal_sources,
        source: manifest_path,
        source_sha256: manifest_sha256,
        tools: Value::Object(tools),
        warnings,
    };
    let results = Results {
        plan: plan.identity.clone(),
        selected: selected_ids,
        executed: vec![],
        blocked: vec![],
        tests,
        removed,
        scope: Some("collect".into()),
        completion: Some(completion.clone()),
        operation_state: None,
    };
    originals.close()?;
    reader.close()?;
    Ok((results, completion))
}

/// Validate one transported full-v3 report using only retained bytes and the
/// current declaration view.  Paths and run identities remain at their
/// original coordinates; only typed endpoint and declaration projections are
/// compared with the current collection request.
#[cfg(not(verus_keep_ghost))]
fn validate_unit_report(
    originals: &mut runtime_session::Session,
    reader: &mut runtime_session::Session,
    req: &Request,
    registrations: &Registry,
    units: &BTreeMap<String, wire::Unit>,
    selected: &BTreeSet<String>,
    required: &[String],
    unit: &str,
    report: &Value,
    global_plan: &Execution,
    current_effective: &Value,
    declaration_root: &Path,
    transport: Option<&wire::ArtifactTransport>,
    closure: Option<&Value>,
) -> Result<Results, String> {
    let top_request: Request = serde_json::from_value(report["request"].clone())
        .map_err(|e| format!("E_COLLECTION_INPUT: retained request: {e}"))?;
    reader.call::<()>(json!({"operation":"validate-request","request":&top_request}))?;
    if top_request.scope
        != Some(wire::Scope::Unit {
            unit: unit.to_owned(),
        })
        || report["request_digest"] != wire::digest(&top_request)?
    {
        return Err(format!(
            "E_COLLECTION_INPUT: retained request digest differs: {unit}"
        ));
    }
    if report["schema_version"] != 1
        || report["scope"] != "configured-judges"
        || report["execution_scope"] != json!({"kind":"unit","unit":unit})
        || report["base"] != req.base.commit
        || report["candidate"] != req.candidate.commit
        || report["candidate_tree"] != req.candidate.tree
        || report["registry_digest"] != req.registries.digest
        || report["context_digest"] != req.context.sha256
        || report["delta"] != json!(req.delta)
        || report["environment"] != req.observations["environment"]
        || report["base_snapshot"] != json!(top_request.base.root)
        || report["report_path"] != top_request.observations["report_path"]
        || top_request.observations["report_path"]
            != format!(
                "{}run-{}.json",
                top_request.observations["preparation"]["request"]["native_artifacts"]["directory"]
                    .as_str()
                    .unwrap_or(".chrono-harness/state/"),
                wire::digest(&top_request.observations["run"])?
            )
        || top_request.runner.version != req.runner.version
    {
        return Err("E_COLLECTION_INPUT: original report/root/run/runner summary differs".into());
    }
    if report["runner"]["sha256"] != req.runner.sha256 || report["judge_sha256"].as_str().is_none()
    {
        return Err(format!(
            "E_COLLECTION_INPUT: executable pins differ: {unit}"
        ));
    }
    let judges_cfg = registrations.judges()["judges"]
        .as_array()
        .ok_or("E_COLLECTION_INPUT: configured judges missing")?;
    let pins: Vec<_> = judges_cfg
        .iter()
        .map(|j| json!({"id":j["id"],"sha256":j["sha256"]}))
        .collect();
    let judge_pin = wire::digest(&pins)?;
    if report["judge_sha256"] != judge_pin {
        return Err(format!(
            "E_COLLECTION_INPUT: configured judge pins differ: {unit}"
        ));
    }
    let records = report["judges"]
        .as_array()
        .ok_or("E_COLLECTION_INPUT: judge records missing")?;
    #[derive(Deserialize)]
    struct CheckedJudges {
        request: Request,
        status: Status,
    }
    let checked: CheckedJudges = reader.call(json!({
        "operation": "retained-judges",
        "request": &top_request,
        "bindings": judges_cfg,
        "records": records,
        "judge": "routes"
    }))?;
    // The runner has checked each response, exit, and request identity against its original streams.
    let parsed: BTreeMap<String, Response> = records
        .iter()
        .map(|record| {
            let response = Response::deserialize(&record["response"]).map_err(|e| e.to_string())?;
            Ok((response.judge_id.clone(), response))
        })
        .collect::<Result<_, String>>()?;
    let resolved: Value = originals.call(
        json!({"operation":"resolve-map","artifacts":report["artifacts"],"closure":closure}),
    )?;
    let artifacts = &resolved;

    let effective = validate_retained_request_at(
        originals,
        &top_request,
        registrations,
        artifacts,
        declaration_root,
        transport,
    )?;
    let supplied_view = parsed
        .get("registration")
        .ok_or("original registration")?
        .outputs
        .get("registration_view")
        .ok_or(
            "E_COLLECTION_INPUT: registration judge missing required output registration_view",
        )?;
    if effective != registrations.evidence(declaration_root,&top_request,json!({"mode":"unit","supplied_view":supplied_view,"effective_inputs":current_effective}))? {
        return Err(
            "E_COLLECTION_INPUT: original effective inputs differ from current obligations".into(),
        );
    }
    let artifact_dirs: Vec<String> =
        reader.call(json!({"operation":"artifact-directories","config":registrations.config()}))?;
    if top_request.observations["execution_units"] != req.observations["execution_units"]
        || top_request.registries.base != top_request.base.root.join(".chrono-harness")
        || top_request.registries.candidate != top_request.candidate.root.join(".chrono-harness")
        || top_request.checkout.head != top_request.candidate.commit
        || !top_request.checkout.tracked.is_empty()
        || top_request
            .checkout
            .untracked
            .iter()
            .any(|path| !artifact_dirs.iter().any(|dir| path.starts_with(dir)))
        || top_request.checkout.index_flags.iter().any(|flag| {
            flag.tag.is_empty()
                || flag.tag.as_bytes()[0].is_ascii_lowercase()
                || flag.tag.eq_ignore_ascii_case("S")
        })
        || top_request.observations["run"]
            .as_str()
            .is_none_or(|s| s.is_empty())
    {
        return Err("E_COLLECTION_INPUT: original root/run/declaration binding".into());
    }
    if top_request.base.commit != req.base.commit
        || top_request.base.tree != req.base.tree
        || top_request.candidate.commit != req.candidate.commit
        || top_request.candidate.tree != req.candidate.tree
        || top_request.config_path != req.config_path
        || top_request.registries.digest != req.registries.digest
        || top_request.context.sha256 != req.context.sha256
        || top_request.delta != req.delta
        || top_request.runner.sha256 != req.runner.sha256
        || top_request.observations["registry_bindings"] != req.observations["registry_bindings"]
        || top_request.observations["environment"] != req.observations["environment"]
    {
        return Err("E_COLLECTION_INPUT: original fixed request binding differs".into());
    }
    let mut findings = vec![];
    for record in records {
        let id = record["id"].as_str().ok_or("original judge id")?;
        let response = parsed.get(id).ok_or("original judge")?;
        // Every reconstructed request uses the retained template's DELTA.
        validate_retained_response(&top_request, response)?;
        findings.extend(
            response
                .findings
                .iter()
                .map(|f| serde_json::to_value(f).unwrap()),
        );
        for evidence in &response.evidence {
            let identity: Value = originals.call(json!({"operation":"artifact-identity","path":evidence.path,"artifacts":artifacts,"transport":transport}))?;
            if identity["sha256"] != evidence.sha256 {
                return Err("E_COLLECTION_INPUT: original judge artifact differs".into());
            }
        }
    }
    if report["status"] != serde_json::to_value(&checked.status).unwrap()
        || report["findings"] != json!(findings)
    {
        return Err("E_COLLECTION_INPUT: report summary differs from actual judges".into());
    }
    let route = parsed
        .get("routes")
        .ok_or("E_COLLECTION_INPUT: routes judge missing")?;
    let route_plan: Execution = serde_json::from_value(
        route
            .outputs
            .get("execution_plan")
            .ok_or("E_COLLECTION_INPUT: routes judge missing required output execution_plan")?
            .clone(),
    )
    .map_err(|e| format!("E_COLLECTION_INPUT: unit plan: {e}"))?;
    let routes = Routes::new(
        declaration_root,
        registrations,
        &req.observations["environment"]["effective"],
    )?;
    routes.check(&route_plan)?;
    let filemap = parsed
        .get("filemap")
        .ok_or("E_COLLECTION_INPUT: filemap judge missing")?;
    if filemap.outputs.get("impact") != Some(&req.impact) || checked.request.impact != req.impact {
        return Err("E_COLLECTION_INPUT: original global provenance differs".into());
    }
    let workflow = parsed
        .get("workflow")
        .ok_or("E_COLLECTION_INPUT: workflow judge missing")?;
    let verdict = workflow
        .outputs
        .get("workflow")
        .ok_or("E_COLLECTION_INPUT: contribution verdict missing")?;
    if verdict["mode"] != "contribution"
        || verdict["unit"] != unit
        || !verdict["integration"].is_null()
        || verdict["completion"] != "pending collection"
    {
        return Err("E_COLLECTION_INPUT: original contribution verdict differs".into());
    }
    let projects = parsed
        .get("projects")
        .ok_or("E_COLLECTION_INPUT: projects judge missing")?;
    let original_tests = projects
        .outputs
        .get("tests")
        .ok_or("E_COLLECTION_INPUT: projects judge missing required output tests")?;
    let owned: BTreeSet<String> = reader
        .call(json!({"operation":"unit-tests","units":units,"unit":unit,"selected":selected}))?;
    let operations: BTreeMap<_, Vec<_>> = registrations
        .bindings
        .iter()
        .map(|(id, bindings)| {
            (
                id.clone(),
                bindings.iter().map(|b| b.operation.clone()).collect(),
            )
        })
        .collect();
    let declared=routes.query("unit-declarations-v1", &json!({"request":checked.request,"effective_inputs":effective,
        "filemap":&registrations.filemap,"projects":&registrations.projects(),"test_operations":operations,"global":selected,"unit":owned}))?;
    if declared["request_id"] != checked.request.request_id
        || route_plan.binding != declared["binding"]
        || route.outputs.get("effective_inputs") != Some(&effective)
        || route.outputs.get("global_selected") != Some(&json!(selected))
        || report["effective_inputs"] != effective
        || &report["tests"] != original_tests
    {
        return Err("E_COLLECTION_INPUT: original plan/input/global binding".into());
    }
    validate_declared_tools(originals, &route_plan, registrations, &effective, &routes)?;
    if route.outputs.get("global_graph") != declared.get("global_graph")
        || declared.get("global_graph").is_none()
    {
        return Err("E_COLLECTION_INPUT: original global graph differs".into());
    }
    if route_plan.scheduling
        != registrations
            .scheduling
            .as_ref()
            .map_err(Clone::clone)?
            .clone()
        || json!(route_plan.selected) != declared["selected"]
        || json!(route_plan.operations) != declared["operations"]
    {
        return Err(format!(
            "E_COLLECTION_INPUT: unit plan differs from declarations: {unit}"
        ));
    }
    if route_plan.root != checked.request.candidate.root
        || route_plan.environment
            != serde_json::from_value(
                checked.request.observations["environment"]["effective"].clone(),
            )
            .map_err(|e| e.to_string())?
    {
        return Err(format!(
            "E_COLLECTION_INPUT: unit plan binding differs: {unit}"
        ));
    }
    let results: Results = serde_json::from_value(original_tests.clone())
        .map_err(|e| format!("E_COLLECTION_INPUT: unit results: {e}"))?;
    if results.plan != route_plan.identity
        || results.selected != owned.iter().cloned().collect::<Vec<_>>()
        || results.scope != Some(format!("unit:{unit}"))
        || results.completion.is_some()
        || results.blocked.len() > 0
        || !verified_state::unit_test_results_complete(&owned, &results.tests)
        || results.executed.len() != route_plan.operations.len()
    {
        return Err(format!(
            "E_COLLECTION_INPUT: unit contribution is incomplete: {unit}"
        ));
    }
    let requests = registrations.retirements.as_ref().map_err(Clone::clone)?;
    let expected_removed: BTreeMap<String, Option<String>> = req.impact["retired_tests"]
        .as_array()
        .into_iter()
        .flatten()
        .map(|test| {
            let id = test.as_str().ok_or("removed node")?;
            Ok((
                id.to_owned(),
                requests.get(id).ok_or("removed declaration")?.clone(),
            ))
        })
        .collect::<Result<_, String>>()?;
    if results.removed != expected_removed {
        return Err("E_COLLECTION_INPUT: original removal obligations differ".into());
    }
    let receipts: BTreeMap<_, _> = results
        .executed
        .iter()
        .filter_map(|r| r.receipt.as_ref().map(|receipt| (&r.operation, receipt)))
        .collect();
    let checked = routes.query(
        "check-plan-receipts-v1",
        &json!({"plan":route_plan,"receipts":receipts}),
    )?;
    if checked["plan"] != route_plan.identity {
        return Err("E_COLLECTION_INPUT: routes receipt plan differs".into());
    }
    for operation in &route_plan.operations {
        let rows: Vec<_> = results
            .executed
            .iter()
            .filter(|row| row.operation == operation.method.operation)
            .collect();
        if rows.len() != 1
            || rows[0].status != "passed"
            || rows[0].error.is_some()
            || checked["operations"].get(&operation.method.operation) != Some(&Value::Null)
            || rows[0].receipt.as_ref().is_none_or(|r| {
                reader
                    .call::<()>(json!({"operation":"check-process","process":r.process}))
                    .is_err()
            })
        {
            return Err(format!(
                "E_COLLECTION_INPUT: receipt differs: {unit}/{}",
                operation.method.operation
            ));
        }
    }
    let helper_evidence = assertion_helpers(registrations.projects(), &route_plan, &results)?;
    if projects.outputs.get("assertion_helpers")
        != (!helper_evidence.is_empty())
            .then(|| json!(helper_evidence))
            .as_ref()
    {
        return Err(format!(
            "E_COLLECTION_INPUT: {unit} assertion helper evidence differs from the original receipts"
        ));
    }
    let evidence = &report["unit_evidence"];
    let all_tests: BTreeSet<_> = units
        .values()
        .flat_map(|u| u.tests.iter().cloned())
        .collect();
    let assigned_elsewhere: BTreeSet<_> = selected.difference(&owned).cloned().collect();
    let not_required: BTreeSet<_> = all_tests.difference(selected).cloned().collect();
    let list =
        |set: &BTreeSet<String>| Value::Array(set.iter().cloned().map(Value::String).collect());
    if evidence["global_selected"] != list(selected)
        || evidence["own"] != list(&owned)
        || evidence["assigned_elsewhere"] != list(&assigned_elsewhere)
        || evidence["required_units"] != serde_json::to_value(required).unwrap()
        || evidence["not_required"] != list(&not_required)
        || evidence["acceptance"] != "contribution-only"
    {
        return Err(format!(
            "E_COLLECTION_INPUT: unit obligation partition differs: {unit}"
        ));
    }
    if global_plan
        .selected
        .keys()
        .cloned()
        .collect::<BTreeSet<_>>()
        != *selected
    {
        return Err("E_COLLECTION_INPUT: current global selection differs".into());
    }
    Ok(results)
}

#[cfg(not(verus_keep_ghost))]
fn artifact_text(
    originals: &mut runtime_session::Session,
    path: &str,
    artifacts: &Value,
    transport: Option<&wire::ArtifactTransport>,
) -> Result<Vec<u8>, String> {
    originals
        .call::<String>(json!({
            "operation":"read-artifact-text","path":path,"artifacts":artifacts,"transport":transport
        }))
        .map(String::into_bytes)
}

#[cfg(not(verus_keep_ghost))]
fn report_bytes(
    originals: &mut runtime_session::Session,
    path: &str,
    artifacts: Option<&Value>,
    limit: u64,
) -> Result<Vec<u8>, String> {
    if let Some(artifacts) = artifacts {
        return artifact_text(originals, path, artifacts, None);
    }
    originals
        .call::<String>(json!({
            "operation":"read-bounded-text","path":path,"limit":limit
        }))
        .map(String::into_bytes)
}

/// Validate the transported original context and declared input closure for
/// both contributions and their finalized collector proof.
#[cfg(not(verus_keep_ghost))]
fn validate_retained_request_at(
    originals: &mut runtime_session::Session,
    req: &Request,
    r: &Registry,
    artifacts: &Value,
    root: &Path,
    transport: Option<&wire::ArtifactTransport>,
) -> Result<Value, String> {
    let mut reader = runtime_session::Session::open(root, &r.runner(root)?, "judge-evidence-v1")?;
    reader.call::<()>(json!({"operation":"validate-request","request":req}))?;
    let ctx: Value = reader.decode(&artifact_text(
        originals,
        req.context.path.to_str().ok_or("context address")?,
        artifacts,
        transport,
    )?)?;
    if wire::digest(&ctx)? != req.context.sha256
        || ctx["base"] != req.base.commit
        || ctx["candidate"] != req.candidate.commit
    {
        return Err("E_COLLECTION_INPUT: original context bytes differ".into());
    }
    if let Some(path) = ctx["retained_inputs"].as_str() {
        if reader.decode::<Value>(&artifact_text(originals, path, artifacts, transport)?)?
            != req.observations["retained"]
        {
            return Err("E_COLLECTION_INPUT: original retained snapshot differs".into());
        }
    }
    if r.config()["schema_version"] == 4 {
        let binding = &req.observations["preparation"];
        originals.call::<()>(json!({"operation":"check-preparation","binding":binding,"transport":transport,"artifacts":artifacts}))?;
        let prepared = &binding["result"];
        if prepared["base"] != req.base.commit
            || prepared["candidate"] != req.candidate.commit
            || prepared["scope"] != json!(req.scope)
            || prepared["context"]["semantic_digest"] != req.context.sha256
        {
            return Err("original preparation differs from full request".into());
        }
    }
    validate_original_entry(&mut reader, req, r)?;
    reader.close()?;
    r.evidence(
        root,
        req,
        json!({"mode":"retained","artifacts":artifacts,"transport":transport}),
    )
}
#[cfg(not(verus_keep_ghost))]
fn validate_original_entry(
    reader: &mut runtime_session::Session,
    req: &Request,
    r: &Registry,
) -> Result<(), String> {
    reader
        .call::<()>(json!({"operation":"retained-entry","request":req,"config":r.config()}))
        .map_err(|error| format!("E_COLLECTION_INPUT: original entry: {error}"))?;
    let runner = req.candidate.root.join(
        r.config()["runner"]["path"]
            .as_str()
            .ok_or("runner declaration")?,
    );
    let entry = &req.observations["entry"];
    let resolved = entry["resolved_paths"]["paths"][0]["actual"]
        .as_str()
        .ok_or("original resolved runner")?;
    let cwd = entry["cwd"].as_str().ok_or("original entry cwd")?;
    let program = entry["argv"][0].as_str().ok_or("original entry program")?;
    let invocation = Path::new(cwd).join(program);
    let executable = Path::new(&req.runner.path);
    // A worktree-local launcher can resolve to a pinned installation outside
    // the host. Bind both the original invocation and its observed executable.
    // current_exe may also retain the literal form of a host-root alias.
    let valid = if Path::new(resolved) == runner {
        executable == runner || invocation == executable
    } else {
        invocation == runner && Path::new(resolved) == executable
    };
    if !valid {
        return Err("E_COLLECTION_INPUT: original runner invocation differs".into());
    }
    Ok(())
}
#[cfg(not(verus_keep_ghost))]
fn validate_declared_tools(
    originals: &mut runtime_session::Session,
    plan: &Execution,
    r: &Registry,
    effective: &Value,
    routes: &Routes,
) -> Result<(), String> {
    let expected: BTreeSet<_> = plan
        .operations
        .iter()
        .map(|op| op.method.tool.clone())
        .collect();
    if plan.tools.keys().cloned().collect::<BTreeSet<_>>() != expected {
        return Err("E_COLLECTION_INPUT: original tool set".into());
    }
    for (id, tool) in &plan.tools {
        let declarations: Vec<_> = r.config()["tools"]
            .as_array()
            .unwrap()
            .iter()
            .filter(|t| t["id"] == *id)
            .collect();
        if declarations.len() != 1 {
            return Err("E_COLLECTION_INPUT: tool declaration".into());
        }
        let d = declarations[0];
        let program = d["program"].as_str().ok_or("tool program")?;
        let argv: Vec<String> =
            serde_json::from_value(d["version_argv"].clone()).map_err(|e| e.to_string())?;
        let checked = routes.query("retained-tool-v1",&json!({"tool":tool,"program":program,"version_argv":argv,
            "environment":plan.environment,"root":plan.root,"expected_version":d["expected_version"]}))?;
        if checked["sha256"] != tool.sha256 {
            return Err("E_TOOL_BINDING: retained routes tool identity differs".into());
        }
        let declared_path = Path::new(program);
        if (declared_path.is_absolute() || program.contains('/'))
            && plan.root.join(declared_path) != tool.path
        {
            return Err("E_COLLECTION_INPUT: original declared tool path".into());
        }
        let input = r.config()["environment"]["inputs"].as_array().unwrap().iter().any(|i| {
            plan.root.join(i["location"].as_str().unwrap()) == tool.path && i["sha256"] == tool.sha256
                && effective["endpoints"]["candidate"]["files"][i["id"].as_str().unwrap()]["sha256"] == tool.sha256
        });
        let registered = tool
            .path
            .strip_prefix(&plan.root)
            .ok()
            .and_then(|p| p.to_str())
            .is_some_and(|p| {
                r.filemap["files"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .any(|f| f["path"] == p)
            });
        if !input && registered {
            let relative = tool
                .path
                .strip_prefix(&plan.root)
                .map_err(|e| e.to_string())?;
            let current: std::path::PathBuf = originals.call(json!({"operation":"checked-path","path":relative.to_str().ok_or("registered tool path")?}))?;
            if wire::sha256(&fs::read(current).map_err(|e| e.to_string())?) != tool.sha256 {
                return Err("E_COLLECTION_INPUT: candidate tool bytes differ".into());
            }
        }
        if !input && !registered {
            return Err("E_COLLECTION_INPUT: original tool input is undeclared".into());
        }
    }
    Ok(())
}
#[cfg(not(verus_keep_ghost))]
fn unit_tools(report: &Value) -> Result<Value, String> {
    let route = report["judges"]
        .as_array()
        .ok_or("judges")?
        .iter()
        .find(|r| r["id"] == "routes")
        .ok_or("routes")?;
    let plan: Execution =
        serde_json::from_value(route["response"]["outputs"]["execution_plan"].clone())
            .map_err(|e| e.to_string())?;
    let mut tools = serde_json::Map::new();
    for (id, t) in &plan.tools {
        let path = t
            .path
            .strip_prefix(&plan.root)
            .map(|p| format!("host:{}", p.display()))
            .unwrap_or_else(|_| format!("external:{}", t.path.display()));
        tools.insert(id.clone(),json!({"program":t.program,"path":path,"sha256":t.sha256,"version_argv":&t.version.argv[1..],"version_stdout_sha256":t.version.stdout_sha256,"version_stderr_sha256":t.version.stderr_sha256}));
    }
    Ok(Value::Object(tools))
}
/// Revalidate the original source closure for every complete consumer, without historical execution.
#[cfg(not(verus_keep_ghost))]
fn verify_completion(
    originals: &mut runtime_session::Session,
    req: &Request,
    r: &Registry,
    effective: &Value,
    plan: &Execution,
    results: &Results,
    artifacts: Option<&Value>,
    declaration_root: &Path,
) -> Result<(), String> {
    let completion = results
        .completion
        .as_ref()
        .ok_or("E_COLLECTION_INPUT: missing completion")?;
    let units: BTreeMap<String, wire::Unit> =
        serde_json::from_value(req.observations["execution_units"]["units"].clone())
            .map_err(|e| e.to_string())?;
    let selected: BTreeSet<_> = plan.selected.keys().cloned().collect();
    let mut reader = runtime_session::Session::open(
        declaration_root,
        &r.runner(declaration_root)?,
        "judge-evidence-v1",
    )?;
    let required: Vec<String> =
        reader.call(json!({"operation":"required-units","units":units,"selected":selected}))?;
    let mut seen = BTreeSet::new();
    let mut tests = BTreeMap::new();
    let mut removed = BTreeMap::<String, Option<String>>::new();
    let mut test_sources = BTreeMap::<String, Vec<String>>::new();
    let mut removal_sources = BTreeMap::<String, Vec<String>>::new();
    let mut tools = serde_json::Map::new();
    let mut warnings = vec![];
    if req.scope
        != Some(wire::Scope::Collect {
            manifest: completion.source.clone(),
        })
    {
        return Err("E_COLLECTION_INPUT: completed collection scope differs".into());
    }
    let manifest_bound = r.config()["execution_units"]["collection_limits"]["manifest_bytes"]
        .as_u64()
        .ok_or("manifest bound")?;
    let manifest_bytes = report_bytes(originals, &completion.source, artifacts, manifest_bound)?;
    if manifest_bytes.len() as u64 > manifest_bound
        || wire::sha256(&manifest_bytes) != completion.source_sha256
    {
        return Err("E_COLLECTION_INPUT: completed manifest bytes/bound differ".into());
    }
    let manifest: wire::FullManifest = reader.decode(&manifest_bytes)?;
    if !matches!(
        manifest.schema.as_str(),
        "chrono-full-collection/v1" | "chrono-ci-collection/v1"
    ) {
        return Err("E_COLLECTION_INPUT: completed manifest schema differs".into());
    }
    if manifest.reports.len() != completion.reports.len()
        || manifest
            .reports
            .iter()
            .zip(&completion.reports)
            .any(|(a, b)| b["unit"] != a.unit || b["path"] != a.path || b["sha256"] != a.sha256)
    {
        return Err("E_COLLECTION_INPUT: completion manifest sources differ".into());
    }
    if manifest
        .reports
        .iter()
        .zip(&completion.reports)
        .any(|(a, b)| {
            a.runner_sha256
                .as_deref()
                .is_some_and(|pin| pin != req.runner.sha256)
                || a.judge_sha256
                    .as_deref()
                    .is_some_and(|pin| Some(pin) != b["judge_sha256"].as_str())
        })
    {
        return Err("E_COLLECTION_INPUT: completed manifest executable pin differs".into());
    }
    let limit = r.config()["execution_units"]["collection_limits"]["report_bytes"]
        .as_u64()
        .ok_or("report limit")?;
    for source in &completion.reports {
        let unit = source["unit"].as_str().ok_or("unit")?;
        let address = source["retained_path"]
            .as_str()
            .ok_or("original source address")?;
        if !units.contains_key(unit)
            || !seen.insert(unit.to_owned())
            || source["path"]
                != originals.call::<String>(json!({"operation":"resolve-original","original":{"path":units[unit].report_path,"sha256":source["sha256"].as_str().ok_or("source digest")?},"transport":source["artifacts"]}))?
        {
            return Err("E_COLLECTION_INPUT: completion source set".into());
        }
        let bytes = report_bytes(originals, address, artifacts, limit)?;
        if bytes.len() as u64 > limit
            || source["sha256"] != wire::sha256(&bytes)
            || address
                != format!(
                    ".chrono-harness/state/import-{}.json",
                    source["sha256"].as_str().ok_or("original digest")?
                )
        {
            return Err("E_COLLECTION_INPUT: original source bytes/address".into());
        }
        let report = reader.decode::<Value>(&bytes)?;
        if reader.call::<u64>(json!({"operation":"report-transport-bytes", "report":report,"metadata_bytes": bytes.len()}))? > limit {
            return Err("original report metadata and streams exceed registered bound".into());
        }
        if source["runner_sha256"] != req.runner.sha256
            || source["judge_sha256"] != report["judge_sha256"]
            || source["status"] != report["status"]
            || source["request_digest"] != report["request_digest"]
        {
            return Err("E_COLLECTION_INPUT: completion source projection differs".into());
        }
        for finding in report["findings"].as_array().ok_or("unit findings")? {
            if finding["level"] == "warning" {
                warnings.push(json!({"unit":unit,"finding":finding}));
            }
        }
        let resolved: Value = originals.call(json!({"operation":"resolve-map","artifacts":source.get("retained_artifacts").unwrap_or(&json!({})),"closure":artifacts}))?;
        let verified = validate_unit_report(
            originals,
            &mut reader,
            req,
            r,
            &units,
            &selected,
            &required,
            unit,
            &report,
            plan,
            effective,
            declaration_root,
            None,
            Some(&resolved),
        )?;
        for (test, status) in verified.tests {
            tests.insert(test.clone(), status);
            test_sources.entry(test).or_default().push(unit.to_owned());
        }
        for (test, replacement) in verified.removed {
            if !verified_state::record_removal(
                &mut removed,
                &mut removal_sources,
                &test,
                &replacement,
                unit,
            ) {
                return Err("removal source conflict".into());
            }
        }
        for (id, t) in unit_tools(&report)?.as_object().unwrap() {
            if tools
                .insert(id.clone(), t.clone())
                .is_some_and(|previous| previous != *t)
            {
                return Err("original tool conflict".into());
            }
        }
    }
    let requests = r.retirements.as_ref().map_err(Clone::clone)?;
    for retired in req.impact["retired_tests"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(Value::as_str)
    {
        let id = retired.to_owned();
        let expected = requests.get(&id).ok_or("retirement declaration")?;
        if !verified_state::record_removal(
            &mut removed,
            &mut removal_sources,
            &id,
            expected,
            "global-obligation",
        ) {
            return Err("removal source conflict".into());
        }
    }
    let selected_ids: Vec<_> = selected.into_iter().collect();
    check_selected_coverage(&selected_ids, &tests)?;
    if completion.schema != "chrono-collected-completion/v1"
        || completion.status != "passed"
        || results.scope.as_deref() != Some("collect")
        || results.plan != plan.identity
        || !results.executed.is_empty()
        || !results.blocked.is_empty()
        || results.selected != selected_ids
        || results.removed != removed
        || completion.warnings != warnings
        || completion.test_sources != test_sources
        || completion.removal_sources != removal_sources
        || required.iter().any(|unit| !seen.contains(unit))
        || completion.required_units != required
        || completion.global_selected != selected_ids
        || results.tests != tests
        || completion.tools != Value::Object(tools)
    {
        return Err("E_COLLECTION_INPUT: completed original coverage/tools differ".into());
    }
    reader.close()?;
    Ok(())
}

#[cfg(not(verus_keep_ghost))]
fn validate_retained_response(req: &Request, response: &Response) -> Result<(), String> {
    for finding in &response.findings {
        if finding.code.is_empty()
            || finding.message.is_empty()
            || !matches!(finding.level.as_str(), "info" | "warning" | "error")
            || finding.delta_refs.is_empty()
            || finding
                .delta_refs
                .iter()
                .any(|p| !p.starts_with('/') && !req.delta.iter().any(|d| d.path == *p))
        {
            return Err("E_COLLECTION_INPUT: invalid retained finding".into());
        }
    }
    let errors = response.findings.iter().any(|f| f.level == "error");
    let warnings = response.findings.iter().any(|f| f.level == "warning");
    if (matches!(response.status, Status::Fail | Status::Error) != errors)
        || (response.status == Status::Pass && warnings)
        || (response.status == Status::Warn && !warnings)
    {
        return Err("E_COLLECTION_INPUT: retained response status/findings mismatch".into());
    }
    for evidence in &response.evidence {
        if !evidence.path.starts_with(".chrono-harness/state/")
            || !wire::is_digest(&evidence.sha256)
            || evidence.kind.is_empty()
        {
            return Err("E_COLLECTION_INPUT: invalid retained evidence identity".into());
        }
    }
    Ok(())
}

#[cfg(not(verus_keep_ghost))]
pub fn host_runner(root: &Path) -> Result<std::path::PathBuf, String> {
    let config = registration::host_config(root)?;
    crate::wire::resolve_program(
        root,
        config["runner"]["path"]
            .as_str()
            .unwrap_or("chrono-harness"),
        None,
    )
}

#[cfg(not(verus_keep_ghost))]
pub fn evaluate_original(
    input: impl std::io::Read,
    mut output: impl std::io::Write,
) -> Result<(), String> {
    #[derive(Deserialize)]
    #[serde(deny_unknown_fields)]
    struct Original {
        request: Request,
    }
    let Original { request } = serde_json::from_reader(input).map_err(|e| e.to_string())?;
    let response = judge(&request);
    #[derive(Serialize)]
    struct Decision {
        status: Status,
        outputs: BTreeMap<String, Value>,
        findings: Vec<Finding>,
        #[serde(skip_serializing_if = "Vec::is_empty")]
        evidence: Vec<wire::Evidence>,
    }
    let decision = Decision {
        status: response.status,
        outputs: response.outputs,
        findings: response.findings,
        evidence: response.evidence,
    };
    serde_json::to_writer(&mut output, &decision).map_err(|e| e.to_string())?;
    output.flush().map_err(|e| e.to_string())
}

#[cfg(not(verus_keep_ghost))]
pub fn judge(req: &Request) -> Response {
    let mut response = req.response(Status::Pass);
    let mut observations = registration::Observations::default();
    let result = git_reader::Reader::open(req).and_then(|mut reader| {
        let evaluation = evaluate(req, &mut response, &mut reader, &mut observations);
        let facts = if reader.bound {
            observations.finish(&mut reader).map(Some)
        } else {
            Ok(None)
        };
        let closed = reader.close();
        if let Some(facts) = facts? {
            response.outputs.insert("git_facts".into(), facts);
        }
        evaluation.and(closed)
    });
    match result {
        Ok(()) => {}
        Err(message) => {
            wire::append_finding(
                &mut response.status,
                &mut response.findings,
                Status::Fail,
                Finding {
                    code: message.split(':').next().unwrap_or("E_PROJECTS").into(),
                    level: "error".into(),
                    message,
                    delta_refs: vec!["/request".into()],
                    causes: vec![],
                },
            );
        }
    }
    response
}
/// Check only helper operations explicitly assigned assertion responsibility for a selected test.
/// The checked execution plan and the retained direct process identify what actually ran.
#[cfg(not(verus_keep_ghost))]
pub(crate) fn assertion_helpers(
    projects: &Value,
    plan: &crate::routes::Execution,
    results: &crate::Results,
) -> Result<Vec<Value>, String> {
    let mut evidence = Vec::new();
    for (collection, prefix) in [("projects", "project"), ("scripts", "script")] {
        let members = projects[collection]
            .as_array()
            .ok_or("projects collection missing")?;
        for dedicated in members {
            let Some(helpers) = dedicated["assertion_helpers"].as_object() else {
                continue;
            };
            let Some(production) = members
                .iter()
                .find(|row| row["id"] == dedicated["tests_for"])
            else {
                return Err("E_TEST_PAIR: assertion helper has no production unit".into());
            };
            let implementation = production["language"]
                .as_str()
                .ok_or("production language missing")?;
            for (test, operations) in helpers {
                let Some(selected) = plan.selected.get(test) else {
                    continue;
                };
                for operation in operations
                    .as_array()
                    .ok_or("assertion helper list required")?
                {
                    let name = operation
                        .as_str()
                        .ok_or("assertion helper operation required")?;
                    if !selected.operations.iter().any(|id| id == name) {
                        return Err(format!(
                            "E_TEST_BINDING: {test} assertion helper {name} is absent from its registered execution plan"
                        ));
                    }
                    let actual = results
                        .executed
                        .iter()
                        .find(|entry| entry.operation == name)
                        .and_then(|entry| entry.receipt.as_ref());
                    let Some(receipt) = actual else {
                        if results
                            .tests
                            .get(test)
                            .is_some_and(|status| status == "passed")
                        {
                            return Err(format!(
                                "E_EXECUTION: {test} assertion helper {name} has no receipt"
                            ));
                        }
                        continue;
                    };
                    let method = &plan
                        .operations
                        .iter()
                        .find(|op| op.method.operation == name)
                        .ok_or("E_EXECUTION: assertion helper method missing")?
                        .method;
                    if receipt.operation != name
                        || receipt.plan != plan.identity
                        || receipt.method != crate::wire::digest(method)?
                    {
                        return Err(format!(
                            "E_EXECUTION: {test} assertion helper {name} receipt differs from its method"
                        ));
                    }
                    let producer = format!("{prefix}:{}", production["id"].as_str().unwrap());
                    let language = pair_checks::assertion_language(
                        projects,
                        &producer,
                        implementation,
                        test,
                        &method.owner,
                        name,
                        &receipt.process.argv,
                        &receipt.digest,
                    )?;
                    evidence.push(serde_json::json!({"test":test, "production":producer, "operation":name,
                        "owner":method.owner, "language":language, "method":receipt.method, "receipt":receipt.digest}));
                }
            }
        }
    }
    Ok(evidence)
}

#[cfg(not(verus_keep_ghost))]
fn evaluate(
    req: &Request,
    response: &mut Response,
    reader: &mut git_reader::Reader,
    observations: &mut registration::Observations,
) -> Result<(), String> {
    req.validate_at(
        &req.candidate.root,
        &crate::wire::resolve_program(&req.candidate.root, &req.runner.path, None)?,
    )?;
    let r = registration::views(req, reader, observations, true)?;
    let inputs = r
        .effective_inputs
        .as_ref()
        .ok_or("registration live inputs missing")?
        .as_ref()
        .map_err(Clone::clone)?;
    let plans: Vec<_> = req
        .prior_results
        .iter()
        .filter_map(|r| r.outputs.get("execution_plan"))
        .collect();
    if plans.len() != 1 {
        return Err("E_ROUTE_MISSING: checked execution plan".into());
    }
    let plan: Execution = serde_json::from_value(plans[0].clone()).map_err(|e| e.to_string())?;
    let routes = Routes::new(
        &req.candidate.root,
        &r,
        &req.observations["environment"]["effective"],
    )?;
    let dispatch = if matches!(req.scope, Some(wire::Scope::Collect { .. })) {
        routes.check(&plan)?;
        None
    } else {
        Some(routes.dispatch(&plan)?)
    };
    if plan.binding != routes.binding(req, &inputs)? || plan.root != req.candidate.root {
        return Err("E_PLAN_IDENTITY: endpoints/registry/context/inputs/run".into());
    }
    let impact = impact::decode(
        &req.impact,
        &r.config()["protocol"],
        &plan.environment,
        |command, input| {
            commands::invoke(&req.candidate.root, routes.runner(), command, None, input)
        },
    )?;
    let mut affected = impact.reached;
    affected.extend(plan.selected.keys().cloned());
    pairs(&req.candidate.root, &r, &affected)?;
    let artifacts: Vec<_> = r.config()["artifacts"]
        .as_array()
        .unwrap()
        .iter()
        .map(|a| a["path"].as_str().unwrap().to_string())
        .collect();
    let Some(dispatch) = dispatch else {
        let (results, completion) = collect_reports(
            req,
            &plan,
            &plan.selected.keys().cloned().collect(),
            &r,
            &inputs,
        )?;
        if !completion.warnings.is_empty() {
            for source in &completion.warnings {
                wire::append_finding(
                    &mut response.status,
                    &mut response.findings,
                    Status::Warn,
                    serde_json::from_value(source["finding"].clone()).map_err(|e| e.to_string())?,
                );
            }
        }
        response.evidence.push(wire::Evidence {
            path: completion.source.clone(),
            sha256: completion.source_sha256.clone(),
            kind: "full collection manifest".into(),
        });
        response
            .outputs
            .insert("tests".into(), serde_json::to_value(&results).unwrap());
        response.outputs.insert(
            "collected_completion".into(),
            serde_json::to_value(completion).unwrap(),
        );
        response.outputs.insert(
            "execution_boundary".into(),
            json!({
                "input_completeness_proven":false,
                "retirement_certification":"unresolved: workflow-owned",
                "collection":"contribution evidence verified; no business operations executed"
            }),
        );
        return Ok(());
    };
    snapshot_with_reader(&req.candidate.commit, &artifacts, reader)?;
    let mut results = execute(&plan, &routes, &dispatch, routes.runner())?;
    if let Some(wire::Scope::Unit { unit }) = &req.scope {
        results.scope = Some(format!("unit:{unit}"));
    }
    if results.has_errors() {
        response.status = Status::Error;
    }
    let requests = r.retirements.as_ref().map_err(Clone::clone)?;
    let deferred = r.downstream;
    for removed in &impact.retired_tests {
        let target = verified_state::declared_removal(requests.get(removed), deferred)
            .ok_or_else(|| format!("E_REQUIRED_TEST_REMOVED: {removed}"))?;
        results.removed.insert(removed.clone(), target.clone());
        if let Some(replacement) = target {
            let assigned_to_peer = match &req.scope {
                Some(wire::Scope::Unit { unit }) => req.observations["execution_units"]["units"]
                    .as_object()
                    .into_iter()
                    .flatten()
                    .any(|(owner, definition)| {
                        owner != unit
                            && definition["tests"]
                                .as_array()
                                .into_iter()
                                .flatten()
                                .any(|test| test.as_str() == Some(replacement))
                    }),
                _ => false,
            };
            if !verified_state::replacement_covered(
                results.tests.get(replacement),
                assigned_to_peer,
            ) {
                response
                    .outputs
                    .insert("tests".into(), serde_json::to_value(&results).unwrap());
                return Err(format!(
                    "E_REQUIRED_TEST_REMOVED: replacement did not succeed: {removed}"
                ));
            }
        }
    }
    response
        .outputs
        .insert("tests".into(), serde_json::to_value(&results).unwrap());
    let helpers = assertion_helpers(r.projects(), &plan, &results)?;
    if !helpers.is_empty() {
        response
            .outputs
            .insert("assertion_helpers".into(), json!(helpers));
    }
    snapshot_with_reader(&req.candidate.commit, &artifacts, reader)?;
    r.evidence(&req.candidate.root, req, json!({"mode":"live"}))
        .map_err(|e| format!("E_EVIDENCE_UNRESOLVED: post-execution {e}"))?;
    if !results.passed() {
        return Err("E_EXECUTION: selected operations/tests failed or blocked".into());
    }
    response.outputs.insert("execution_boundary".into(),json!({"input_completeness_proven":false,"retirement_certification":"unresolved: workflow-owned"}));
    Ok(())
}
