#![allow(unexpected_cfgs)]
use vstd::contrib::exec_spec::ExecSpecEq;
#[cfg(not(verus_keep_ghost))]
use vstd::prelude::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

verus! {
pub enum Entry { Version, Evaluate, Execute, Pairs, Results, Collection, Protocol, Usage }

pub fn entry(count: usize, first: Option<&str>, second: Option<&str>) -> (out: Entry)
    ensures out == match first {
        Some(name) if count == 1 => if name@ == "--version"@ { Entry::Version }
            else if name@ == "evaluate-projects-v1"@ { Entry::Evaluate }
            else if name@ == "execute-plan-v1"@ { Entry::Execute }
            else if name@ == "check-pairs-v1"@ { Entry::Pairs }
            else if name@ == "read-results-v1"@ { Entry::Results }
            else if name@ == "check-collection-v1"@ { Entry::Collection }
            else { Entry::Usage },
        Some(name) if count == 2 && name@ == "--protocol"@
            && (second matches Some(version) && version@ == "chrono-judge/v1"@) => Entry::Protocol,
        _ => Entry::Usage,
    },
{
    let name = match first { Some(name) => name, None => return Entry::Usage };
    if count == 2 && <&str>::exec_eq(name, "--protocol") {
        if let Some(version) = second {
            if <&str>::exec_eq(version, "chrono-judge/v1") { return Entry::Protocol; }
        }
    }
    if count != 1 { return Entry::Usage; }
    if <&str>::exec_eq(name, "--version") {
        Entry::Version
    } else if <&str>::exec_eq(name, "evaluate-projects-v1") {
        Entry::Evaluate
    } else if <&str>::exec_eq(name, "execute-plan-v1") {
        Entry::Execute
    } else if <&str>::exec_eq(name, "check-pairs-v1") {
        Entry::Pairs
    } else if <&str>::exec_eq(name, "read-results-v1") {
        Entry::Results
    } else if <&str>::exec_eq(name, "check-collection-v1") {
        Entry::Collection
    } else {
        Entry::Usage
    }
}
}

#[cfg(not(verus_keep_ghost))]
fn main() -> std::process::ExitCode {
    use chrono_judge_projects::{check_pairs, evidence_query};
    use std::io::{self, Write};
    let arguments: Vec<_> = std::env::args_os().skip(1).collect();
    let operation = entry(
        arguments.len(),
        arguments.first().and_then(|s| s.to_str()),
        arguments.get(1).and_then(|s| s.to_str()),
    );
    let input = io::stdin().lock();
    let result = match operation {
        Entry::Version => {
            println!("chrono-judge-projects {}", env!("CARGO_PKG_VERSION"));
            return std::process::ExitCode::SUCCESS;
        }
        Entry::Evaluate => chrono_judge_projects::evaluate_original(input, io::stdout().lock()),
        Entry::Execute => std::env::current_dir()
            .map_err(|e| e.to_string())
            .and_then(|root| {
                chrono_judge_projects::execute_query::execute_plan(
                    &root,
                    input,
                    io::stdout().lock(),
                )
            }),
        Entry::Pairs => check_pairs(input),
        Entry::Results => evidence_query::read_results(input).and_then(|reply| {
            let mut output = io::stdout().lock();
            serde_json::to_writer(&mut output, &reply).map_err(|error| error.to_string())?;
            output.flush().map_err(|error| error.to_string())
        }),
        Entry::Collection => std::env::current_dir()
            .map_err(|error| error.to_string())
            .and_then(|root| evidence_query::check_collection(&root, input)),
        Entry::Usage => {
            eprintln!("E_USAGE: --protocol chrono-judge/v1");
            return 2.into();
        }
        Entry::Protocol => {
            drop(input);
            return protocol(arguments);
        }
    };
    chrono_judge_projects::query_exit(result, |error| {
        writeln!(io::stderr().lock(), "{error}").is_ok()
    })
    .into()
}

#[cfg(not(verus_keep_ghost))]
fn protocol(arguments: Vec<std::ffi::OsString>) -> std::process::ExitCode {
    use std::os::unix::process::CommandExt;
    let result = (|| -> Result<(), String> {
        let root = std::env::current_dir().map_err(|err| err.to_string())?;
        let runner = chrono_judge_projects::host_runner(&root)?;
        let current = std::env::current_exe().map_err(|err| err.to_string())?;
        let err = std::process::Command::new(runner)
            .args([
                "judge-command-v1",
                "chrono-judge-projects",
                env!("CARGO_PKG_VERSION"),
            ])
            .arg(current)
            .args(["evaluate-projects-v1", "E_PROJECTS", "--inherited"])
            .args(arguments)
            .exec();
        Err(err.to_string())
    })();
    if let Err(error) = result {
        eprintln!("chrono-harness judge-command-v1: {error}");
    }
    2.into()
}
