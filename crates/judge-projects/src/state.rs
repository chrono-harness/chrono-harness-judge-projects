//! Execution originals belong to projects; retention only protects their lifetime.
#![allow(unexpected_cfgs)]
#[cfg(not(verus_keep_ghost))]
use vstd::prelude::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

verus! {
/// Admission for a declared compiler destination inside the shared run directory.
pub fn owned_compiler_output(exact_name: bool, single_component: bool, canonical: bool) -> (owned: bool)
    ensures owned == (exact_name && single_component && canonical),
{
    exact_name && single_component && canonical
}
}

#[cfg(not(verus_keep_ghost))]
use crate::routes::Execution;
#[cfg(not(verus_keep_ghost))]
use crate::runtime_session::Session;
#[cfg(not(verus_keep_ghost))]
use crate::verified_state::{self, OperationObservation};
use crate::wire::sha256;
#[cfg(not(verus_keep_ghost))]
use crate::{OperationResult, Results};
#[cfg(not(verus_keep_ghost))]
use chrono_harness::{CommandSpec, ProcessResult};
#[cfg(not(verus_keep_ghost))]
use serde_json::{Value, json};
#[cfg(not(verus_keep_ghost))]
use std::time::SystemTime;

#[cfg(not(verus_keep_ghost))]
struct Original {
    path: String,
    session: std::cell::RefCell<Session>,
}

#[cfg(not(verus_keep_ghost))]
fn now() -> Result<u128, String> {
    SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH)
        .map(|d| d.as_millis())
        .map_err(|e| e.to_string())
}

#[cfg(not(verus_keep_ghost))]
impl Original {
    fn begin(
        plan: &Execution,
        path: String,
        intent: Value,
        runner: &std::path::Path,
    ) -> Result<Self, String> {
        let mut session = Session::open(&plan.root, runner, "retained-artifacts-v1")?;
        session.call::<Value>(
            json!({"operation":"begin-directory","producer":"check-original",
            "path":path,"reference":format!("projects-recovery:{}", sha256(path.as_bytes())),
            "intent":{"kind":"project-execution","plan":plan.identity,"state":"unknown"}}),
        )?;
        let original = Self {
            path,
            session: std::cell::RefCell::new(session),
        };
        original.write("intent.json", &intent)?;
        Ok(original)
    }

    fn write(&self, name: &str, value: &Value) -> Result<Value, String> {
        self.session
            .borrow_mut()
            .call(json!({"operation":"write-directory","path":self.path,"name":name,"value":value}))
    }

    fn finish(self, terminal: bool, outcome: Value, inputs: &[String]) -> Result<(), String> {
        let mut session = self.session.into_inner();
        session.call::<()>(json!({"operation":"finish-directory","path":self.path,"terminal":terminal,"outcome":outcome,"inputs":inputs}))?;
        session.close()
    }
}

#[cfg(not(verus_keep_ghost))]
pub(crate) struct Run {
    original: Original,
    pub(crate) plan_original: Value,
}

#[cfg(not(verus_keep_ghost))]
pub(crate) fn address(plan: &Execution) -> Result<&str, String> {
    plan.binding["operation_state"]
        .as_str()
        .ok_or("E_OPERATION_STATE: missing registered operation state address".into())
}

#[cfg(not(verus_keep_ghost))]
fn observation<'a>(
    original: &Original,
    row: &'a OperationResult,
) -> Result<OperationObservation<'a>, String> {
    let terminal = row
        .receipt
        .as_ref()
        .map(|receipt| {
            original.session.borrow_mut().call(json!({
        "operation":"process-completion","exit_code":receipt.process.exit_code,
        "signal":receipt.process.exit_signal,"owned_work_joined":receipt.process.owned_work_joined,
    }))
        })
        .transpose()?;
    Ok(OperationObservation {
        status: &row.status,
        process_terminal: terminal,
    })
}

#[cfg(not(verus_keep_ghost))]
fn encoded(
    original: &Original,
    row: &OperationResult,
    retained_process: Option<Value>,
) -> Result<Value, String> {
    let mut value = serde_json::to_value(row).map_err(|e| e.to_string())?;
    if row.receipt.is_some() {
        value["receipt"]["process"] = match retained_process {
            Some(process) => process,
            None => original.session.borrow_mut().call(
                json!({"operation":"compact-process","process":value["receipt"]["process"]}),
            )?,
        };
    }
    value["schema"] = json!("chrono-project-operation-result/v1");
    value["updated_at_unix_millis"] = json!(now()?);
    value["state"] = json!(verified_state::operation_state(&observation(
        original, row
    )?));
    Ok(value)
}

#[cfg(not(verus_keep_ghost))]
impl Run {
    pub(crate) fn begin(plan: &Execution, runner: &std::path::Path) -> Result<Self, String> {
        let path = address(plan)?.to_owned();
        let original = Original::begin(
            plan,
            path,
            json!({
                "schema":"chrono-project-execution/v1", "producer":"chrono-judge-projects",
                "plan":plan.identity, "state":"intent", "updated_at_unix_millis":now()?,
                "handle":null, "result":null,
                "recovery":"read this execution and its independent operation originals; absent results remain unknown; never redispatch the same identity"
            }),
            runner,
        )?;
        let plan_original = original.write(
            "plan.json",
            &serde_json::to_value(plan).map_err(|e| e.to_string())?,
        )?;
        Ok(Self {
            original,
            plan_original,
        })
    }

    pub(crate) fn finish(self, results: &mut Results) -> Result<(), String> {
        let mut originals = Vec::new();
        let mut inputs = Vec::new();
        for (index, row) in results
            .executed
            .iter_mut()
            .chain(&mut results.blocked)
            .enumerate()
        {
            let reference = match &row.original {
                Some(original) => original.clone(),
                None => self.original.write(
                    &format!("undelivered-{index}.json"),
                    &encoded(&self.original, row, None)?,
                )?,
            };
            if row.original.is_some() {
                inputs.push(
                    reference["path"]
                        .as_str()
                        .ok_or("operation original path")?
                        .to_owned(),
                );
            }
            row.original = Some(reference.clone());
            originals.push(reference);
        }
        let observations = results
            .executed
            .iter()
            .chain(&results.blocked)
            .map(|row| observation(&self.original, row))
            .collect::<Result<Vec<_>, String>>()?;
        let terminal = verified_state::all_terminal(&observations);
        let reference = self.original.write(
            "result.json",
            &json!({
                "schema":"chrono-project-execution-result/v1", "producer":"chrono-judge-projects",
                "plan":results.plan, "state":"returned", "terminal":terminal,
                "updated_at_unix_millis":now()?, "plan_original":self.plan_original,
                "operations":originals, "tests":results.tests,
            }),
        )?;
        self.original.finish(
            terminal,
            json!({"kind":"project-execution","state":"returned","terminal":terminal}),
            &inputs,
        )?;
        results.operation_state = Some(reference);
        Ok(())
    }
}

#[cfg(not(verus_keep_ghost))]
pub(crate) struct Operation {
    original: Original,
    compiler_output: Option<String>,
}

#[cfg(not(verus_keep_ghost))]
impl Operation {
    pub(crate) fn begin(
        plan: &Execution,
        index: usize,
        plan_original: &Value,
        runner: &std::path::Path,
    ) -> Result<Self, String> {
        let run = address(plan)?;
        let path = format!("{run}.operation-{index}");
        let streams =
            ["stdout", "stderr", "launch.json"].map(|name| plan.root.join(&path).join(name));
        let op = &plan.operations[index];
        let mut compiler_output = None;
        if op.method.output_contract.is_some() {
            if let Some(output) = op
                .method
                .argv
                .get(10)
                .filter(|output| std::path::Path::new(output).starts_with(run))
            {
                let expected = format!("{run}/{}.rlib", op.method.operation);

                if !owned_compiler_output(
                    output == &expected,
                    !op.method.operation.contains('/'),
                    crate::commands::query(
                        &plan.root,
                        runner,
                        "compiler-output-v1",
                        &json!({"operation":"canonical","argv":op.method.argv}),
                    )?,
                ) {
                    return Err(
                        "compiler output in the run directory must belong to this operation".into(),
                    );
                }
                compiler_output = Some(expected);
            }
        }
        let original = Original::begin(
            plan,
            path,
            json!({
                "schema":"chrono-project-operation/v1", "producer":"chrono-judge-projects",
                "plan":plan.identity, "plan_original":plan_original, "operation":op,
                "state":"intent", "updated_at_unix_millis":now()?, "handle":null, "result":null,
                "process_originals":streams.iter().map(|p| p.strip_prefix(&plan.root).unwrap()).collect::<Vec<_>>(),
                "recovery":"the native runner owns the only wait; inspect launch and partial streams; missing result remains unknown"
            }),
            runner,
        )?;
        Ok(Self {
            original,
            compiler_output,
        })
    }

    pub(crate) fn execute(
        &self,
        command: &CommandSpec,
        expected_sha256: &str,
    ) -> Result<ProcessResult, String> {
        self.original.session.borrow_mut().call(json!({"operation":"execute-retained","path":self.original.path,"command":command,"expected_sha256":expected_sha256}))
    }

    /// The run owns this directory until all its operations have joined. Its durable receipt contains
    /// everything later consumers read. Failed or interrupted runs keep their evidence.
    fn retire_compiler_files(&self, row: &OperationResult) -> Result<(), String> {
        let Some(receipt) = &row.receipt else {
            return Ok(());
        };
        let (Some(Ok(library)), Some(Ok(dependency))) =
            (&receipt.compiler_artifact, &receipt.compiler_dependency)
        else {
            return Ok(());
        };
        let Some(output) = self.compiler_output.as_deref() else {
            return Ok(());
        };
        if !verified_state::can_release_compiler_files(
            &row.status,
            receipt.process.owned_work_joined,
            library.path == output.as_bytes(),
        ) {
            return Ok(());
        }
        let library_digest = std::str::from_utf8(&library.sha256).map_err(|e| e.to_string())?;
        self.original.session.borrow_mut().call(json!({
            "operation":"dispose-compiler-originals","path":self.original.path,
            "library_sha256":library_digest,"library_length":library.length,
            "dependency_sha256":sha256(dependency),"dependency_length":dependency.len()
        }))
    }

    pub(crate) fn finish(self, row: &OperationResult) -> Result<Value, String> {
        let retained_process = if let Some(receipt) = &row.receipt {
            #[derive(serde::Deserialize)]
            struct Evidence {
                record: Value,
                stdout_length: u64,
                stderr_length: u64,
            }
            let original: Evidence = self.original.session.borrow_mut().call(json!({
                "operation":"directory-evidence","path":self.original.path,"process":receipt.process
            }))?;
            let process = original.record;
            for (stream, expected_digest, expected_length, length) in [
                (
                    "stdout",
                    &receipt.process.stdout_sha256,
                    receipt.process.stdout_bytes.len() as u64,
                    original.stdout_length,
                ),
                (
                    "stderr",
                    &receipt.process.stderr_sha256,
                    receipt.process.stderr_bytes.len() as u64,
                    original.stderr_length,
                ),
            ] {
                let digest = process[format!("{stream}_original")]["sha256"]
                    .as_str()
                    .ok_or("operation stream original digest")?;
                verified_state::validate_original(
                    digest,
                    length,
                    Some((expected_digest, expected_length)),
                )?;
            }
            Some(process)
        } else {
            None
        };
        let reference = self.original.write(
            "result.json",
            &encoded(&self.original, row, retained_process)?,
        )?;
        self.retire_compiler_files(row)?;
        // The operation directory owns both its result and the exact streams it
        // references. Unknown results keep that directory's recovery protection.
        let known = verified_state::terminal(&observation(&self.original, row)?);
        self.original.finish(
            known,
            json!({"kind":"project-operation", "operation":row.operation, "terminal":known}),
            &[],
        )?;
        Ok(reference)
    }
}
