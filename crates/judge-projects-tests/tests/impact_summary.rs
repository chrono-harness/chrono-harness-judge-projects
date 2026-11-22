#[path = "../../judge-projects/src/impact.rs"]
mod impact;
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};

#[test]
fn the_installed_decoder_receives_the_whole_impact_and_returns_affected_and_retired_tests() {
    let input = json!({"closure":{"reached":{"test:kept":[]}},"retired_tests":["old"],"edges":[]});
    let protocol = json!({"timeout_seconds":7,"stdout_limit_bytes":2048});
    let env = BTreeMap::from([("PATH".into(), "/tools".into())]);
    let result = impact::decode(&input, &protocol, &env, |cmd, bytes| {
        assert_eq!(cmd.program, "chrono-judge-filemap");
        assert_eq!(cmd.args, ["impact-summary"]);
        assert_eq!(cmd.env, env);
        assert_eq!((cmd.timeout_seconds, cmd.output_limit_bytes), (7, 2048));
        assert_eq!(serde_json::from_slice::<Value>(bytes).unwrap(), input);
        Ok((
            0,
            br#"{"reached":["test:kept"],"retired_tests":["old"],"schema":"v6"}"#.to_vec(),
            Vec::new(),
        ))
    })
    .unwrap();
    assert_eq!(result.reached, BTreeSet::from(["test:kept".into()]));
    assert_eq!(result.retired_tests, ["old"]);
    for (outcome, error) in [
        (
            Ok((2, Vec::new(), b"invalid edge kind\n".to_vec())),
            "invalid edge kind",
        ),
        (Err("process timeout".to_owned()), "process timeout"),
        (
            Ok((0, b"{}".to_vec(), Vec::new())),
            "missing field `reached`",
        ),
    ] {
        assert!(
            impact::decode(&input, &protocol, &env, |_, _| outcome)
                .unwrap_err()
                .starts_with(error)
        );
    }
}
