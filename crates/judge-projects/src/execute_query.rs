#[cfg(not(verus_keep_ghost))]
use vstd::prelude::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

verus! {
/// Check the two path observations before opening either the host runner or the routes program.
pub fn admit_query_location(same_root: bool, absolute_routes: bool) -> (res: Result<(), &'static str>)
    ensures res.is_ok() == (same_root && absolute_routes),
        res matches Err(e) ==> e@ == "E_PLAN_BINDING: execute from the plan root with an absolute routes executable"@,
{
    if same_root && absolute_routes { Ok(()) } else {
        Err("E_PLAN_BINDING: execute from the plan root with an absolute routes executable")
    }
}

/// A failed execution keeps its own error. A completed execution publishes its actual
/// result together with the first trace error, and returns the publisher's write/flush result.
pub fn publish_plan<T, F>(
    work: Result<T, String>, diagnostic: Option<String>, publish: F,
) -> (out: Result<(), String>)
    where F: FnOnce(T, Option<String>) -> Result<(), String>,
    requires forall|value: T| work == Ok::<T, String>(value) ==> #[trigger] publish.requires((value, diagnostic)),
    ensures match work {
        Err(error) => out == Err::<(), String>(error),
        Ok(value) => publish.ensures((value, diagnostic), out),
    },
{
    match work { Err(error) => Err(error), Ok(value) => publish(value, diagnostic) }
}
}

#[cfg(not(verus_keep_ghost))]
use crate::{
    execute,
    plan_trace::{PlanTrace, publish_frame, write_frame},
    routes::{Execution, Routes},
};
#[cfg(not(verus_keep_ghost))]
use serde::{Deserialize, Serialize};
#[cfg(not(verus_keep_ghost))]
use std::{
    io::{Read, Write},
    path::{Path, PathBuf},
    sync::Mutex,
};
#[cfg(not(verus_keep_ghost))]
use tracing_subscriber::{filter::LevelFilter, prelude::*};

#[cfg(not(verus_keep_ghost))]
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ExecuteRequest {
    plan: Execution,
    routes: RouteCommand,
    diagnostics: Option<String>,
}

#[cfg(not(verus_keep_ghost))]
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RouteCommand {
    executable: PathBuf,
    sha256: String,
    timeout_seconds: u64,
    output_limit_bytes: usize,
}

#[cfg(not(verus_keep_ghost))]
pub fn execute_plan(root: &Path, input: impl Read, output: impl Write) -> Result<(), String> {
    let query: ExecuteRequest = serde_json::from_reader(input).map_err(|err| err.to_string())?;
    admit_query_location(
        query.plan.root == root,
        query.routes.executable.is_absolute(),
    )?;
    let routes = Routes::bound(
        root,
        crate::host_runner(root)?,
        &query.routes.executable,
        Some(&query.routes.sha256),
        query.plan.environment.clone(),
        query.routes.timeout_seconds,
        query.routes.output_limit_bytes,
    )?;
    let work = || {
        let dispatch = routes.dispatch(&query.plan)?;
        execute(&query.plan, &routes, &dispatch, routes.runner())
    };
    let (execution, diagnostic_error) = if let Some(level) = query.diagnostics {
        let level: LevelFilter = level
            .parse()
            .map_err(|_| "E_USAGE: unknown diagnostics level")?;
        let trace_error = std::sync::Arc::new(Mutex::new(None));
        let error = trace_error.clone();
        let layer = PlanTrace(move |event| {
            let mut error = error.lock().unwrap();
            publish_frame(&mut error, || write_frame(&event).err());
        });
        let subscriber = tracing_subscriber::registry().with(level).with(layer);
        let result = tracing::subscriber::with_default(subscriber, work);
        (
            result,
            trace_error
                .lock()
                .unwrap()
                .take()
                .map(|error| error.to_string()),
        )
    } else {
        (work(), None)
    };
    #[derive(Serialize)]
    struct Reply {
        results: crate::Results,
        diagnostic_error: Option<String>,
    }
    publish_plan(execution, diagnostic_error, |results, diagnostic_error| {
        let mut output = output;
        serde_json::to_writer(
            &mut output,
            &Reply {
                results,
                diagnostic_error,
            },
        )
        .map_err(|error| error.to_string())?;
        output.flush().map_err(|error| error.to_string())
    })
}
