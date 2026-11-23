//! Read the public project execution results or verify a retained collection.
use crate::routes::Execution;
use crate::wire::Request;
use crate::{Results, validate_retained_request_at, verify_completion};
use serde::Deserialize;
use serde_json::{Value, json};
use std::{io::Read, path::Path};

pub fn read_results(input: impl Read) -> Result<Value, String> {
    let results: Results = serde_json::from_reader(input).map_err(|error| error.to_string())?;
    Ok(json!({"passed":results.passed(),"results":results}))
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Retained {
    request: Request,
    artifacts: Value,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Collection {
    request: Request,
    effective_inputs: Value,
    plan: Execution,
    results: Results,
    retained: Option<Retained>,
}

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
