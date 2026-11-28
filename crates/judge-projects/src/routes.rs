//! The executor consumes a checked plan and retains the original business-process receipt.
#![allow(unexpected_cfgs)]
use vstd::contrib::exec_spec::ExecSpecEq;
#[cfg(not(verus_keep_ghost))]
use vstd::prelude::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

verus! {
#[cfg_attr(not(verus_keep_ghost), derive(Clone, Debug, serde::Deserialize, serde::Serialize, PartialEq, Eq))]
#[cfg_attr(not(verus_keep_ghost), serde(deny_unknown_fields))]
pub struct Claims {
    pub(crate) resources: Vec<String>,
    pub(crate) outputs: Vec<String>,
}

/// Compare complete resource names or the path-components supplied by the native path parser.
pub trait Conflict {
    spec fn related(&self, a: &String, b: &String) -> bool;
    fn conflicts(&self, a: &String, b: &String) -> (same: bool)
        ensures same == self.related(a,b);
}
pub struct Resource;
impl Conflict for Resource {
    open spec fn related(&self, a: &String, b: &String) -> bool { a@ == b@ }
    fn conflicts(&self, a: &String, b: &String) -> (same: bool) {
        <&str>::exec_eq(a.as_str(), b.as_str())
    }
}
pub open spec fn any_pair<M: Conflict>(a: Seq<String>, b: Seq<String>, cmp: &M) -> bool {
    exists|i:int,j:int| 0 <= i < a.len() && 0 <= j < b.len() && #[trigger] cmp.related(&a[i], &b[j])
}
fn pairs<M: Conflict>(a: &[String], b: &[String], cmp: &M) -> (found: bool)
    ensures found == any_pair(a@,b@,cmp),
{
    let mut i = 0;
    while i < a.len()
        invariant i <= a.len(), forall|k:int,l:int| 0 <= k < i && 0 <= l < b.len() ==>
            !#[trigger] cmp.related(&a@[k], &b@[l]),
        decreases a.len() - i,
    {
        let mut j = 0;
        while j < b.len()
            invariant i < a.len(), j <= b.len(),
                forall|l:int| 0 <= l < j ==> !#[trigger] cmp.related(&a@[i as int], &b@[l]),
            decreases b.len() - j,
        {
            if cmp.conflicts(&a[i], &b[j]) {
                assert(any_pair(a@,b@,cmp));
                return true;
            }
            j += 1;
        }
        i += 1;
    }
    false
}
/// Reserve a report location before its reader opens the file. A rejected
/// location leaves the manifest, result and all previously admitted paths intact.
pub(crate) fn reserve_report<M: Conflict>(
    known: &mut std::collections::BTreeSet<String>, candidate: &String, cmp: &M,
) -> (accepted: bool)
    requires vstd::laws_cmp::obeys_cmp::<String>(),
    ensures accepted == (!old(known)@.contains(*candidate) && forall|p:String| old(known)@.contains(p)
        ==> !#[trigger] cmp.related(&p,candidate)),
        known@ == if accepted { old(known)@.insert(*candidate) } else { old(known)@ },
{
    broadcast use vstd::std_specs::btree::group_btree_axioms;
    let mut entries = known.iter();
    loop
        invariant vstd::laws_cmp::obeys_cmp::<String>(), entries@.1.to_set() == old(known)@, known@ == old(known)@,
            0 <= entries@.0 <= entries@.1.len(),
            forall|j:int| 0 <= j < entries@.0 ==> !#[trigger] cmp.related(&entries@.1[j],candidate),
        decreases entries@.1.len() - entries@.0,
    {
        let Some(path) = entries.next() else {
            assert forall|p:String| old(known)@.contains(p) implies !#[trigger] cmp.related(&p,candidate) by {
                assert(entries@.1.contains(p));
                let j = choose|j:int| 0 <= j < entries@.1.len() && entries@.1[j] == p;
            }
            return known.insert(candidate.clone());
        };
        if cmp.conflicts(path,candidate) {
            assert(old(known)@.contains(*path));
            return false;
        }
    }
}
impl Claims {
    pub(crate) fn overlaps<M: Conflict>(&self, other: &Self, paths: &M) -> (yes: bool)
        ensures yes == (any_pair(self.resources@,other.resources@,&Resource)
            || any_pair(self.outputs@,other.outputs@,paths)),
    {
        pairs(&self.resources, &other.resources, &Resource) || pairs(&self.outputs, &other.outputs, paths)
    }
}
}
#[cfg(not(verus_keep_ghost))]
pub(crate) struct OutputPaths;
#[cfg(not(verus_keep_ghost))]
impl Conflict for OutputPaths {
    fn conflicts(&self, a: &String, b: &String) -> bool {
        crate::wire::paths_overlap(a, b)
    }
}
#[cfg(not(verus_keep_ghost))]
use crate::commands::{self, Spec};
#[cfg(not(verus_keep_ghost))]
use crate::registration::Registry;
#[cfg(not(verus_keep_ghost))]
use crate::wire::{Tool, file_identity, resolve_program};
#[cfg(not(verus_keep_ghost))]
use serde::{Deserialize, Serialize};
#[cfg(not(verus_keep_ghost))]
use serde_json::{Value, json};
#[cfg(not(verus_keep_ghost))]
use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};

#[cfg(not(verus_keep_ghost))]
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Method {
    pub owner: String,
    pub operation: String,
    pub tool: String,
    pub argv: Vec<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub output_contract: Option<crate::compiler::OutputContract>,
}

#[cfg(not(verus_keep_ghost))]
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Bounds {
    #[serde(with = "crate::routes::timeout_wire")]
    pub timeout_seconds: u64,
    pub output_limit_bytes: usize,
}

#[cfg(not(verus_keep_ghost))]
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Plan {
    pub operations: Vec<String>,
    #[serde(with = "crate::routes::timeout_wire")]
    pub timeout_seconds: u64,
    pub output_limit_bytes: usize,
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub operation_bounds: BTreeMap<String, Bounds>,
}

#[cfg(not(verus_keep_ghost))]
#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct Scheduling {
    pub max_running: usize,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub priority: Vec<String>,
    pub resources: Vec<String>,
    pub claims: BTreeMap<String, Claims>,
}
#[cfg(not(verus_keep_ghost))]
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

#[cfg(not(verus_keep_ghost))]
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Operation {
    pub method: Method,
    pub predecessors: BTreeSet<String>,
    #[serde(with = "crate::routes::timeout_wire")]
    pub timeout_seconds: u64,
    pub output_limit_bytes: usize,
}

#[cfg(not(verus_keep_ghost))]
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct Dispatch {
    pub max_running: std::num::NonZeroUsize,
    pub order: Vec<usize>,
}

#[cfg(not(verus_keep_ghost))]
impl Dispatch {
    fn admit(&self, count: usize) -> Result<(), String> {
        crate::verified_state::admit_dispatch_order(&self.order, count).map_err(String::from)
    }
}

/// Resolve the host's installed routes command in the current declaration checkout.
/// A transported plan can refer to a different original working directory.
#[cfg(not(verus_keep_ghost))]
pub struct Routes<'a> {
    root: &'a Path,
    runner: PathBuf,
    program: String,
    digest: String,
    environment: BTreeMap<String, String>,
    timeout_seconds: u64,
    output_limit_bytes: usize,
}
#[cfg(not(verus_keep_ghost))]
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
            registry.runner(root)?,
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
        runner: PathBuf,
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
        match crate::impact::reply_stream(code, &stdout, &stderr) {
            Ok(stdout) => serde_json::from_slice(stdout).map_err(|error| error.to_string()),
            Err([]) => Err(format!("routes {command} exited {code}")),
            Err(stderr) => {
                let diagnostic = std::str::from_utf8(stderr).map_err(|error| error.to_string())?;
                Err(diagnostic
                    .strip_suffix('\n')
                    .unwrap_or(diagnostic)
                    .to_owned())
            }
        }
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
        let error = match reply.error {
            Value::Null => Ok(None),
            Value::String(reason) => Ok(Some(reason)),
            _ => Err(()),
        };
        crate::verified_state::receipt_reply(
            &reply.plan,
            &plan.identity,
            &reply.operation,
            &operation.method.operation,
            error,
        )
    }
    pub fn binding(&self, req: &crate::wire::Request, effective: &Value) -> Result<Value, String> {
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

/// Public execution bounds use JSON numbers in the interoperable range and
/// canonical decimal strings above it so a v1 JCS transport preserves them.
#[cfg(not(verus_keep_ghost))]
pub(crate) mod timeout_wire {
    use serde::{Deserialize, Deserializer, Serializer, de::Error};

    const SAFE: u64 = (1 << 53) - 1;

    pub fn serialize<S: Serializer>(seconds: &u64, s: S) -> Result<S::Ok, S::Error> {
        if *seconds <= SAFE {
            s.serialize_u64(*seconds)
        } else {
            s.collect_str(seconds)
        }
    }

    pub fn observation<S: Serializer>(
        process: &crate::wire::ProcessResult,
        s: S,
    ) -> Result<S::Ok, S::Error> {
        use serde::Serialize;
        if let Some(seconds) = crate::receipt::exact_observation_timeout(process.timeout_seconds) {
            let mut value = serde_json::to_value(process).map_err(serde::ser::Error::custom)?;
            value["timeout_seconds"] = serde_json::Value::String(seconds.to_string());
            value.serialize(s)
        } else {
            process.serialize(s)
        }
    }

    pub mod optional {
        use super::*;
        #[derive(Deserialize)]
        struct Wrapped(#[serde(deserialize_with = "super::deserialize")] u64);

        pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<Option<u64>, D::Error> {
            Ok(Option::<Wrapped>::deserialize(d)?.map(|wrapped| wrapped.0))
        }
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<u64, D::Error> {
        #[derive(Deserialize)]
        #[serde(untagged)]
        enum Timeout {
            Number(u64),
            Decimal(String),
        }
        match Timeout::deserialize(d)? {
            Timeout::Number(value) => Ok(value),
            Timeout::Decimal(text) => text
                .parse::<u64>()
                .ok()
                .filter(|n| *n > SAFE && n.to_string() == text)
                .ok_or_else(|| D::Error::custom("invalid exact timeout")),
        }
    }
}
