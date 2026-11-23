//! The executor consumes a checked plan and retains the original business-process receipt.
use chrono_harness::{
    CommandSpec, file_identity, observation::Tool, resolve_program, run_process_observed,
};
use chrono_judge_registration::{
    Registrations,
    execution::{Method, Plan, Scheduling},
};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Execution {
    pub schema: String,
    pub identity: String,
    pub binding: Value,
    pub root: PathBuf,
    pub environment: BTreeMap<String, String>,
    pub selected: BTreeMap<String, Plan>,
    pub operations: Vec<Operation>,
    pub tools: BTreeMap<String, Tool>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub scheduling: Option<Scheduling>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Operation {
    pub method: Method,
    pub predecessors: BTreeSet<String>,
    pub timeout_seconds: u64,
    pub output_limit_bytes: usize,
}

/// Resolve the host's installed routes command in the current declaration checkout.
/// A transported plan can refer to a different original working directory.
pub struct Routes<'a> {
    root: &'a Path,
    program: String,
    digest: String,
    environment: BTreeMap<String, String>,
    timeout_seconds: u64,
    output_limit_bytes: usize,
}
impl<'a> Routes<'a> {
    pub fn new(
        root: &'a Path,
        registry: &Registrations,
        environment: &Value,
    ) -> Result<Self, String> {
        let name = "chrono-judge-routes";
        let tools = registry.config()["tools"]
            .as_array()
            .ok_or("missing registered tools")?;
        let judges = registry.judges()["judges"]
            .as_array()
            .ok_or("missing registered judges")?;
        let tool = tools.iter().find(|row| row["id"] == name);
        let judge = judges.iter().find(|row| row["id"] == "routes");
        let (program, expected) = if let Some(tool) = tool {
            (
                tool["program"]
                    .as_str()
                    .ok_or("missing routes tool program")?,
                None,
            )
        } else if let Some(judge) = judge {
            (
                judge["executable"]
                    .as_str()
                    .ok_or("missing routes executable")?,
                Some(
                    judge["sha256"]
                        .as_str()
                        .ok_or("missing routes judge checksum")?,
                ),
            )
        } else {
            (name, None)
        };
        let environment: BTreeMap<String, String> =
            serde_json::from_value(environment.clone()).map_err(|e| e.to_string())?;
        let path = if expected.is_some() {
            root.join(program)
        } else {
            resolve_program(root, program, environment.get("PATH").map(String::as_str))?
        };
        let protocol = &registry.config()["protocol"];
        Self::bound(
            root,
            &path,
            expected,
            environment,
            protocol["timeout_seconds"]
                .as_u64()
                .ok_or("missing routes timeout")?,
            serde_json::from_value(protocol["stdout_limit_bytes"].clone())
                .map_err(|e| e.to_string())?,
        )
    }

    pub(super) fn bound(
        root: &'a Path,
        path: &Path,
        expected: Option<&str>,
        environment: BTreeMap<String, String>,
        timeout_seconds: u64,
        output_limit_bytes: usize,
    ) -> Result<Self, String> {
        let observed = file_identity(path)?.0;
        if expected.is_some_and(|digest| digest != observed) {
            return Err("E_TOOL_BINDING: routes executable differs".into());
        }
        Ok(Self {
            root,
            program: path.to_str().ok_or("routes path is not UTF-8")?.into(),
            digest: observed,
            environment,
            timeout_seconds,
            output_limit_bytes,
        })
    }

    pub fn query(&self, command: &str, input: &impl Serialize) -> Result<Value, String> {
        let spec = CommandSpec {
            program: self.program.clone(),
            args: vec![command.into()],
            env: self.environment.clone(),
            timeout_seconds: self.timeout_seconds,
            output_limit_bytes: self.output_limit_bytes,
        };
        let bytes = serde_json::to_vec(input).map_err(|e| e.to_string())?;
        let p = run_process_observed(self.root, &spec, &bytes, &self.digest)?;
        if let Some(failure) = p.failure {
            return Err(failure);
        }
        if p.exit_code != 0 {
            return Err(if p.stderr.is_empty() {
                format!("routes {command} exited {}", p.exit_code)
            } else {
                p.stderr.strip_suffix('\n').unwrap_or(&p.stderr).to_owned()
            });
        }
        chrono_harness::decode(&p.stdout_bytes)
    }
    pub fn check(&self, plan: &Execution) -> Result<(), String> {
        let reply = self.query("check-plan-v1", plan)?;
        if reply["plan"] != plan.identity {
            return Err("E_PLAN_IDENTITY: routes response differs".into());
        }
        Ok(())
    }
    pub fn check_receipt(
        &self,
        plan: &Execution,
        receipt: &crate::receipt::Receipt,
    ) -> Result<(), String> {
        #[derive(Serialize)]
        struct Records<'a> {
            plan: &'a Execution,
            receipts: BTreeMap<&'a str, &'a crate::receipt::Receipt>,
        }
        let originals = Records {
            plan,
            receipts: BTreeMap::from([(receipt.operation.as_str(), receipt)]),
        };
        let reply = self.query("check-plan-receipts-v1", &originals)?;
        if reply["plan"] != plan.identity {
            return Err("E_RECEIPT_MISMATCH: routes response refers to another plan".into());
        }
        match reply["operations"].get(&receipt.operation) {
            Some(Value::Null) => Ok(()),
            Some(Value::String(reason)) => Err(reason.clone()),
            _ => Err("E_RECEIPT_MISMATCH: routes did not check the operation".into()),
        }
    }
    pub fn binding(
        &self,
        req: &chrono_harness::wire::Request,
        effective: &Value,
    ) -> Result<Value, String> {
        let reply = self.query(
            "plan-context-v1",
            &json!({"request":req,"effective_inputs":effective,"templates":{}}),
        )?;
        if reply["request_id"] != req.request_id {
            return Err("E_PLAN_IDENTITY: route context differs".into());
        }
        Ok(reply["binding"].clone())
    }
}
