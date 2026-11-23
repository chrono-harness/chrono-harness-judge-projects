fn main() -> std::process::ExitCode {
    use chrono_judge_projects::{check_pairs, evidence_query};
    use std::io::{self, Write};
    let mut args = std::env::args_os().skip(1);
    let operation = args.next();
    let name = operation.as_deref().and_then(std::ffi::OsStr::to_str);
    if args.next().is_none() {
        let input = io::stdin().lock();
        let result = match name {
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
            return match result {
                Ok(()) => std::process::ExitCode::SUCCESS,
                Err(error) => {
                    eprintln!("{error}");
                    2.into()
                }
            };
        }
    }
    std::process::ExitCode::from(chrono_harness::wire::judge_main(
        "chrono-judge-projects",
        env!("CARGO_PKG_VERSION"),
        chrono_judge_projects::judge,
    ))
}
