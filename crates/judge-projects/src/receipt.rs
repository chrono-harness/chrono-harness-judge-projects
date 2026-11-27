//! Capture compiler originals in the process owner before the operation releases its files.
#[cfg(not(verus_keep_ghost))]
use crate::compiler;
#[cfg(not(verus_keep_ghost))]
use crate::routes::{Execution, Operation};
#[cfg(not(verus_keep_ghost))]
use crate::wire;
#[cfg(not(verus_keep_ghost))]
use crate::wire::ProcessResult;
#[cfg(not(verus_keep_ghost))]
use serde::{Deserialize, Serialize};

#[cfg(not(verus_keep_ghost))]
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Receipt {
    pub plan: String,
    pub operation: String,
    pub method: String,
    #[serde(serialize_with = "crate::routes::timeout_wire::observation")]
    pub process: ProcessResult,
    pub compiler_dependency: Option<Result<Vec<u8>, String>>,
    pub compiler_artifact: Option<Result<compiler::Artifact, String>>,
    pub digest: String,
}

#[cfg(not(verus_keep_ghost))]
impl Receipt {
    pub fn observe(
        plan: &Execution,
        op: &Operation,
        process: ProcessResult,
        runner: &std::path::Path,
    ) -> Result<Self, String> {
        let observed = compiler::observe(&plan.root, runner, op, &process)?;
        let mut receipt = Self {
            plan: plan.identity.clone(),
            operation: op.method.operation.clone(),
            method: wire::digest(&op.method)?,
            compiler_dependency: observed.dependency,
            compiler_artifact: observed.artifact,
            process,
            digest: String::new(),
        };
        receipt.digest = receipt.identity()?;
        Ok(receipt)
    }
    fn identity(&self) -> Result<String, String> {
        let mut v = serde_json::to_value(self).map_err(|e| e.to_string())?;
        v.as_object_mut().unwrap().remove("digest");
        wire::digest(&v)
    }
}

#[cfg(not(verus_keep_ghost))]
use vstd::prelude::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

verus! {
/// The receipt carries the exact decimal length of each wide process timeout.
pub fn exact_observation_timeout(seconds: Option<u64>) -> (out: Option<u64>)
    ensures match seconds {
        Some(n) if n >= 9007199254740992 => out == Some(n),
        _ => out.is_none(),
    },
{
    match seconds { Some(n) if n >= 9007199254740992u64 => Some(n), _ => None }
}
}
