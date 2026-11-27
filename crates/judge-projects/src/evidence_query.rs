//! Read the public project execution results or verify a retained collection.
#[cfg(verus_keep_ghost)]
use super::{
    OperationRow, all_test_statuses_passed, selected_test_passed, test_statuses_pass,
    uncovered_test,
};
#[cfg(not(verus_keep_ghost))]
use crate::verified_state::{OperationRow, test_statuses_pass, uncovered_test};
use std::collections::BTreeMap;
use vstd::contrib::exec_spec::ExecSpecEq;
#[cfg(not(verus_keep_ghost))]
use vstd::prelude::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

verus! {
/// Complete project evidence requires every selected test and every reported operation to pass.
pub(crate) fn report_passed<R, O>(
    executed: &[OperationRow<R, O>], blocked: usize, selected: &[String], tests: &BTreeMap<String, String>,
) -> (passed: bool)
    requires vstd::laws_cmp::obeys_cmp::<String>(),
    ensures passed == (blocked == 0
        && (forall|i: int| 0 <= i < executed.len() ==> #[trigger] executed@[i].status@ == "passed"@)
        && all_test_statuses_passed(tests@)
        && (forall|i: int| 0 <= i < selected.len() ==> selected_test_passed(tests@, #[trigger] selected@[i]))),
{
    broadcast use vstd::std_specs::btree::group_btree_axioms;
    if blocked != 0 { return false; }
    let mut i = 0;
    while i < executed.len()
        invariant i <= executed.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] executed@[j].status@ == "passed"@,
        decreases executed.len() - i,
    {
        if !<&str>::exec_eq(executed[i].status.as_str(), "passed") { return false; }
        i += 1;
    }
    test_statuses_pass(tests) && uncovered_test(selected, tests).is_none()
}
}

#[cfg(not(verus_keep_ghost))]
use crate::routes::Execution;
#[cfg(not(verus_keep_ghost))]
use crate::wire::Request;
#[cfg(not(verus_keep_ghost))]
use crate::{Results, validate_retained_request_at, verify_completion};
#[cfg(not(verus_keep_ghost))]
use serde::Deserialize;
#[cfg(not(verus_keep_ghost))]
use serde_json::{Value, json};
#[cfg(not(verus_keep_ghost))]
use std::{io::Read, path::Path};

#[cfg(not(verus_keep_ghost))]
pub fn read_results(input: impl Read) -> Result<Value, String> {
    let results: Results = serde_json::from_reader(input).map_err(|error| error.to_string())?;
    Ok(json!({"passed":results.passed(),"results":results}))
}

#[cfg(not(verus_keep_ghost))]
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Retained {
    request: Request,
    artifacts: Value,
}

#[cfg(not(verus_keep_ghost))]
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Collection {
    request: Request,
    effective_inputs: Value,
    plan: Execution,
    results: Results,
    retained: Option<Retained>,
}

#[cfg(not(verus_keep_ghost))]
pub fn check_collection(root: &Path, input: impl Read) -> Result<(), String> {
    let query: Collection = serde_json::from_reader(input).map_err(|error| error.to_string())?;
    let current = &query.request;
    current.validate_at(root, &crate::host_runner(root)?)?;
    if current.candidate.root != root {
        return Err("collection declaration root differs from current checkout".into());
    }
    let mut reader = crate::git_reader::Reader::open(current)?;
    let registrations =
        crate::registration::views(current, &mut reader, &mut Default::default(), false)?;
    reader.close()?;
    let mut originals = crate::runtime_session::Session::open(
        root,
        &registrations.runner(root)?,
        "retained-artifacts-v1",
    )?;
    let (request, artifacts) = if let Some(retained) = &query.retained {
        let original = &retained.request;
        let observed = validate_retained_request_at(
            &mut originals,
            original,
            &registrations,
            &retained.artifacts,
            root,
            None,
        )?;
        if observed != query.effective_inputs {
            return Err("collected producer retained inputs differ".into());
        }
        (
            original,
            Some(
                originals
                    .call(json!({"operation":"transport-map","artifacts":retained.artifacts}))?,
            ),
        )
    } else {
        (current, None)
    };
    verify_completion(
        &mut originals,
        request,
        &registrations,
        &query.effective_inputs,
        &query.plan,
        &query.results,
        artifacts.as_ref(),
        root,
    )?;
    originals.close()
}
