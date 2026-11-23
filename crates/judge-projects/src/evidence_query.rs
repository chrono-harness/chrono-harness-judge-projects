//! Read the public project execution results or verify a retained collection.
use crate::{Results, validate_retained_request_at, verify_completion};
use chrono_harness::{facts, wire::Request};
use chrono_judge_routes::Execution;
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
    current.validate()?;
    if current.candidate.root != root {
        return Err("collection declaration root differs from current checkout".into());
    }
    let reader = facts::Reader::for_request(current)?;
    let (old, registrations, _) = chrono_judge_registration::views_with_reader(current, &reader)?;
    let (request, artifacts) = if let Some(retained) = &query.retained {
        let original = &retained.request;
        let observed = validate_retained_request_at(
            original,
            &old,
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
            Some(chrono_harness::retained_artifacts::transport_map(
                &retained.artifacts,
                None,
            )?),
        )
    } else {
        (current, None)
    };
    verify_completion(
        request,
        &registrations,
        &old,
        &query.effective_inputs,
        &query.plan,
        &query.results,
        artifacts.as_ref(),
        root,
    )
}
