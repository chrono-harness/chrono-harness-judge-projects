//! The executor consumes a checked plan and retains the original business-process receipt.
use crate::commands::{self, Spec};
use crate::registration::Registry;
use chrono_harness::{file_identity, observation::Tool, resolve_program};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Method {
    pub owner: String,
    pub operation: String,
    pub tool: String,
    pub argv: Vec<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub output_contract: Option<chrono_harness::verified_verifier::OutputContract>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Bounds {
    pub timeout_seconds: u64,
    pub output_limit_bytes: usize,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Plan {
    pub operations: Vec<String>,
    pub timeout_seconds: u64,
    pub output_limit_bytes: usize,
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub operation_bounds: BTreeMap<String, Bounds>,
}

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct Claims {
    resources: Vec<String>,
    outputs: Vec<String>,
}

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct Scheduling {
    pub max_running: usize,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub priority: Vec<String>,
    pub resources: Vec<String>,
    pub claims: BTreeMap<String, Claims>,
}
impl Claims {
    pub(super) fn overlaps(&self, other: &Self) -> bool {
        self.resources
            .iter()
            .any(|resource| other.resources.contains(resource))
            || self.outputs.iter().any(|path| {
                other
                    .outputs
                    .iter()
                    .any(|other| chrono_harness::units::overlap(path, other))
            })
    }
}

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

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct Dispatch {
    pub max_running: std::num::NonZeroUsize,
    pub order: Vec<usize>,
}

impl Dispatch {
    fn admit(&self, count: usize) -> Result<(), String> {
        let mut seen = vec![false; count];
        let invalid = "E_EXECUTION_PLAN: routes dispatch order must cover every operation once";
        if self.order.len() != count {
            return Err(invalid.into());
        }
        for &index in &self.order {
            let visited = seen.get_mut(index).ok_or(invalid)?;
            if *visited {
                return Err(invalid.into());
            }
            *visited = true;
        }
        Ok(())
    }
}

/// Resolve the host's installed routes command in the current declaration checkout.
/// A transported plan can refer to a different original working directory.
pub struct Routes<'a> {
    root: &'a Path,
    runner: PathBuf,
    program: String,
    digest: String,
    environment: BTreeMap<String, String>,
    timeout_seconds: u64,
    output_limit_bytes: usize,
}
impl<'a> Routes<'a> {
    pub fn new(root: &'a Path, registry: &Registry, environment: &Value) -> Result<Self, String> {
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
        let runner = resolve_program(root, "chrono-harness", None)?;
        Ok(Self {
            root,
            runner,
            program: path.to_str().ok_or("routes path is not UTF-8")?.into(),
            digest: observed,
            environment,
            timeout_seconds,
            output_limit_bytes,
        })
    }

    pub fn runner(&self) -> &Path {
        &self.runner
    }

    pub fn query(&self, command: &str, input: &impl Serialize) -> Result<Value, String> {
        let spec = Spec {
            program: self.program.clone(),
            args: vec![command.into()],
            env: self.environment.clone(),
            timeout_seconds: self.timeout_seconds,
            output_limit_bytes: self.output_limit_bytes,
        };
        let bytes = serde_json::to_vec(input).map_err(|e| e.to_string())?;
        let (code, stdout, stderr) =
            commands::invoke(self.root, &self.runner, &spec, Some(&self.digest), &bytes)?;
        if code != 0 {
            if stderr.is_empty() {
                return Err(format!("routes {command} exited {code}"));
            }
            let diagnostic = String::from_utf8(stderr).map_err(|e| e.to_string())?;
            return Err(diagnostic
                .strip_suffix('\n')
                .unwrap_or(&diagnostic)
                .to_owned());
        }
        serde_json::from_slice(&stdout).map_err(|e| e.to_string())
    }
    pub fn check(&self, plan: &Execution) -> Result<(), String> {
        let reply = self.query("check-plan-v1", plan)?;
        if reply["plan"] != plan.identity {
            return Err("E_PLAN_IDENTITY: routes response differs".into());
        }
        Ok(())
    }
    pub(super) fn dispatch(&self, plan: &Execution) -> Result<Dispatch, String> {
        #[derive(Deserialize)]
        #[serde(deny_unknown_fields)]
        struct Reply {
            plan: String,
            dispatch: Dispatch,
        }
        let reply: Reply = serde_json::from_value(self.query("dispatch-plan-v1", plan)?)
            .map_err(|e| e.to_string())?;
        if reply.plan != plan.identity {
            return Err("E_PLAN_IDENTITY: routes response differs".into());
        }
        reply.dispatch.admit(plan.operations.len())?;
        Ok(reply.dispatch)
    }
    pub fn check_receipt(
        &self,
        plan: &Execution,
        operation: &Operation,
        receipt: &crate::receipt::Receipt,
    ) -> Result<(), String> {
        #[derive(Deserialize)]
        #[serde(deny_unknown_fields)]
        struct Reply {
            plan: String,
            operation: String,
            error: Value,
        }
        #[derive(Serialize)]
        struct Original<'a> {
            plan: &'a str,
            root: &'a Path,
            environment: &'a BTreeMap<String, String>,
            operation: &'a Operation,
            tool: Option<&'a Tool>,
            receipt: &'a crate::receipt::Receipt,
        }
        let original = Original {
            plan: &plan.identity,
            root: &plan.root,
            environment: &plan.environment,
            operation,
            tool: plan.tools.get(&operation.method.tool),
            receipt,
        };
        let reply: Reply =
            serde_json::from_value(self.query("check-operation-receipt-v1", &original)?)
                .map_err(|error| error.to_string())?;
        if reply.plan != plan.identity || reply.operation != operation.method.operation {
            return Err(
                "E_RECEIPT_MISMATCH: routes response refers to another plan or operation".into(),
            );
        }
        match reply.error {
            Value::Null => Ok(()),
            Value::String(reason) => Err(reason),
            _ => Err("E_RECEIPT_MISMATCH: invalid receipt comparison".into()),
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
