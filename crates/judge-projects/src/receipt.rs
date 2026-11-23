//! Capture compiler originals in the process owner before the operation releases its files.
use crate::compiler::DependencyIo;
use crate::routes::{Execution, Operation};
use chrono_harness::{ProcessResult, wire};
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Receipt {
    pub plan: String,
    pub operation: String,
    pub method: String,
    pub process: ProcessResult,
    pub compiler_dependency: Option<Result<Vec<u8>, String>>,
    pub compiler_artifact:
        Option<Result<chrono_harness::verified_verifier::CompiledArtifact, String>>,
    pub digest: String,
}

impl Receipt {
    pub fn observe(
        plan: &Execution,
        op: &Operation,
        process: ProcessResult,
    ) -> Result<Self, String> {
        let mut receipt = Self {
            plan: plan.identity.clone(),
            operation: op.method.operation.clone(),
            method: wire::digest(&op.method)?,
            compiler_dependency: chrono_harness::verified_verifier::sources::observe_dependency(
                &op.method.output_contract,
                &op.method.argv,
                process.exit_code,
                process.failure.is_some(),
                op.output_limit_bytes,
                &DependencyIo(&plan.root),
            ),
            compiler_artifact: chrono_harness::verified_verifier::observe_artifact(
                &op.method.output_contract,
                &op.method.argv,
                process.exit_code,
                process.failure.is_some(),
                &DependencyIo(&plan.root),
            ),
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
