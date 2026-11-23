fn main() -> std::process::ExitCode {
    if std::env::args_os().skip(1).eq(["check-pairs-v1"]) {
        return match chrono_judge_projects::check_pairs(std::io::stdin().lock()) {
            Ok(()) => std::process::ExitCode::SUCCESS,
            Err(error) => {
                eprintln!("{error}");
                2.into()
            }
        };
    }
    std::process::ExitCode::from(chrono_harness::wire::judge_main(
        "chrono-judge-projects",
        env!("CARGO_PKG_VERSION"),
        chrono_judge_projects::judge,
    ))
}
