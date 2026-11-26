//! Public compiler evidence emitted by the installed runner while the operation owns its files.
#![allow(unexpected_cfgs)]
#[cfg(not(verus_keep_ghost))]
use vstd::prelude::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

verus! {

#[cfg_attr(not(verus_keep_ghost), derive(Clone, Debug, serde::Serialize, serde::Deserialize))]
#[cfg_attr(not(verus_keep_ghost), serde(deny_unknown_fields))]
pub struct OutputContract {
    pub version: String,
    pub commit: String,
}

#[cfg_attr(not(verus_keep_ghost), derive(serde::Serialize))]
pub struct Observation<'a> {
    pub operation: &'static str,
    pub contract: &'a OutputContract,
    pub argv: &'a [String],
    pub exit: i32,
    pub process_failed: bool,
    pub limit: usize,
}

/// An ordinary method keeps its empty observation. A compiler method calls the
/// runner once, even for failed processes, and propagates its original reply.
pub fn observe_method<'a, T, E, F>(
    contract: Option<&'a OutputContract>, argv: &'a [String], exit: i32,
    failure: Option<&String>, limit: usize, empty: T, query: F,
) -> (result: Result<T, E>)
    where F: FnOnce(&'static str, Observation<'a>) -> Result<T, E>,
    requires forall|name: &'static str, req: Observation<'a>|
        name@ == "compiler-output-v1"@ && req.operation@ == "observe"@
        && contract == Some(req.contract) && req.argv == argv && req.exit == exit
        && req.process_failed == failure.is_some() && req.limit == limit
        ==> #[trigger] query.requires((name, req)),
    ensures match contract {
        None => result == Ok::<T, E>(empty),
        Some(c) => exists|name: &'static str, req: Observation<'a>|
            name@ == "compiler-output-v1"@ && req.operation@ == "observe"@
            && req.contract == c && req.argv == argv && req.exit == exit
            && req.process_failed == failure.is_some() && req.limit == limit
            && #[trigger] query.ensures((name, req), result),
    },
{
    match contract {
        None => Ok(empty),
        Some(c) => query("compiler-output-v1", Observation {
            operation: "observe", contract: c, argv, exit, process_failed: failure.is_some(), limit,
        }),
    }
}
}

#[cfg(not(verus_keep_ghost))]
use serde::{Deserialize, Serialize};
#[cfg(not(verus_keep_ghost))]
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Artifact {
    pub path: Vec<u8>,
    pub sha256: Vec<u8>,
    pub length: u64,
}

#[cfg(not(verus_keep_ghost))]
#[derive(Default, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Observed {
    pub dependency: Option<Result<Vec<u8>, String>>,
    pub artifact: Option<Result<Artifact, String>>,
}

#[cfg(not(verus_keep_ghost))]
pub fn observe(
    root: &std::path::Path,
    runner: &std::path::Path,
    op: &crate::routes::Operation,
    process: &crate::wire::ProcessResult,
) -> Result<Observed, String> {
    observe_method(
        op.method.output_contract.as_ref(),
        &op.method.argv,
        process.exit_code,
        process.failure.as_ref(),
        op.output_limit_bytes,
        Observed::default(),
        |name, request| {
            let value = serde_json::to_value(request).map_err(|e| e.to_string())?;
            crate::commands::query(root, runner, name, &value)
        },
    )
}
