use crate::{
    execute,
    plan_trace::PlanTrace,
    routes::{Execution, Routes},
};
use serde::{Deserialize, Serialize};
use std::{
    io::{self, Read, Write},
    path::{Path, PathBuf},
    sync::Mutex,
};
use tracing_subscriber::{filter::LevelFilter, prelude::*};

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ExecuteRequest {
    plan: Execution,
    routes: RouteCommand,
    diagnostics: Option<String>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RouteCommand {
    executable: PathBuf,
    sha256: String,
    timeout_seconds: u64,
    output_limit_bytes: usize,
}

pub fn execute_plan(root: &Path, input: impl Read, output: impl Write) -> Result<(), String> {
    let query: ExecuteRequest = serde_json::from_reader(input).map_err(|err| err.to_string())?;
    if query.plan.root != root || !query.routes.executable.is_absolute() {
        return Err(
            "E_PLAN_BINDING: execute from the plan root with an absolute routes executable".into(),
        );
    }
    let routes = Routes::bound(
        root,
        &query.routes.executable,
        Some(&query.routes.sha256),
        query.plan.environment.clone(),
        query.routes.timeout_seconds,
        query.routes.output_limit_bytes,
    )?;
    let work = || {
        let dispatch = routes.dispatch(&query.plan)?;
        let runner = chrono_harness::resolve_program(root, "chrono-harness", None)?;
        execute(&query.plan, &routes, &dispatch, &runner)
    };
    let (results, diagnostic_error) = if let Some(level) = query.diagnostics {
        let level: LevelFilter = level
            .parse()
            .map_err(|_| "E_USAGE: unknown diagnostics level")?;
        let trace_error = std::sync::Arc::new(Mutex::new(None));
        let error = trace_error.clone();
        let layer = PlanTrace(move |event| {
            let mut error = error.lock().unwrap();
            if error.is_none() {
                let mut dest = io::stderr().lock();
                let published = (|| -> io::Result<()> {
                    dest.write_all(b"chrono-trace-v1 ")?;
                    serde_json::to_writer(&mut dest, &event)?;
                    dest.write_all(b"\n")?;
                    dest.flush()
                })();
                *error = published.err();
            }
        });
        let subscriber = tracing_subscriber::registry().with(level).with(layer);
        let result = tracing::subscriber::with_default(subscriber, work)?;
        (
            result,
            trace_error
                .lock()
                .unwrap()
                .take()
                .map(|error| error.to_string()),
        )
    } else {
        (work()?, None)
    };
    #[derive(Serialize)]
    struct Reply {
        results: crate::Results,
        diagnostic_error: Option<String>,
    }
    let mut output = output;
    serde_json::to_writer(
        &mut output,
        &Reply {
            results,
            diagnostic_error,
        },
    )
    .map_err(|e| e.to_string())?;
    output.flush().map_err(|e| e.to_string())
}
