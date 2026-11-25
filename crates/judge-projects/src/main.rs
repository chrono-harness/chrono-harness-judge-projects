fn main() -> std::process::ExitCode {
    use chrono_judge_projects::{check_pairs, evidence_query};
    use std::io::{self, Write};
    let mut args = std::env::args_os().skip(1);
    let operation = args.next();
    let name = operation.as_deref().and_then(std::ffi::OsStr::to_str);
    if args.next().is_none() {
        let input = io::stdin().lock();
        let result = match name {
            Some("--version") => {
                println!("chrono-judge-projects {}", env!("CARGO_PKG_VERSION"));
                return std::process::ExitCode::SUCCESS;
            }
            Some("evaluate-projects-v1") => Some(chrono_judge_projects::evaluate_original(
                input,
                io::stdout().lock(),
            )),
            Some("execute-plan-v1") => Some(
                std::env::current_dir()
                    .map_err(|e| e.to_string())
                    .and_then(|root| {
                        chrono_judge_projects::execute_query::execute_plan(
                            &root,
                            input,
                            io::stdout().lock(),
                        )
                    }),
            ),
            Some("check-pairs-v1") => Some(check_pairs(input)),
            Some("read-results-v1") => {
                Some(evidence_query::read_results(input).and_then(|reply| {
                    let mut output = io::stdout().lock();
                    serde_json::to_writer(&mut output, &reply)
                        .map_err(|error| error.to_string())?;
                    output.flush().map_err(|error| error.to_string())
                }))
            }
            Some("check-collection-v1") => Some(
                std::env::current_dir()
                    .map_err(|error| error.to_string())
                    .and_then(|root| evidence_query::check_collection(&root, input)),
            ),
            _ => None,
        };
        if let Some(result) = result {
            return chrono_judge_projects::query_exit(result, |error| {
                writeln!(io::stderr().lock(), "{error}").is_ok()
            })
            .into();
        }
    }
    let arguments: Vec<_> = std::env::args_os().skip(1).collect();
    if arguments.as_slice()
        != [
            std::ffi::OsString::from("--protocol"),
            std::ffi::OsString::from("chrono-judge/v1"),
        ]
    {
        eprintln!("E_USAGE: --protocol chrono-judge/v1");
        return 2.into();
    }
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
