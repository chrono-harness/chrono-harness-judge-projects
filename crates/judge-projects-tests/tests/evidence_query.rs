use chrono_judge_projects::evidence_query::{check_collection, read_results};
use serde_json::json;

#[test]
fn result_queries_keep_the_native_wire_shape_and_outcome() {
    let mut raw = json!({"plan":"p", "tests":{"test:t":"passed"}, "selected":["test:t"],
        "executed":[{"operation":"run","status":"passed","original":{"path":"receipt"}}],
        "blocked":[], "removed":{"test:retired":null}, "scope":null, "custom":true});
    let read = |input: &serde_json::Value| read_results(input.to_string().as_bytes()).unwrap();
    let reply = read(&raw);
    let result = &reply["results"];
    assert_eq!(reply["passed"], true);
    assert_eq!(result["removed"], raw["removed"]);
    assert_eq!(
        result["executed"][0],
        json!({"operation":"run","status":"passed",
        "original":{"path":"receipt"},"receipt":null,"error":null})
    );
    assert!(result.get("scope").is_none() && result.get("custom").is_none());
    raw["tests"]["test:t"] = json!("failed");
    assert_eq!(read(&raw)["passed"], false);
    raw["tests"] = json!({"test:other":"passed"});
    assert_eq!(read(&raw)["passed"], false);
    raw["tests"] = json!({});
    assert_eq!(read(&raw)["passed"], false);
    raw["selected"] = json!([]);
    assert_eq!(read(&raw)["passed"], true);
    raw["tests"] = json!({"test:other":"failed"});
    assert_eq!(read(&raw)["passed"], false);
    raw["tests"] = json!([]);
    assert!(read_results(raw.to_string().as_bytes()).is_err());
}

#[test]
fn result_query_checks_executed_and_blocked_operations() {
    let operation = json!({"operation":"compile","status":"passed","receipt":null,"error":null});
    let base = json!({"plan":"p","selected":[],"executed":[operation],"blocked":[],"tests":{},"removed":{}});
    for (status, expected) in [
        ("passed", true),
        ("failed", false),
        ("error", false),
        ("passed ", false),
    ] {
        let mut report = base.clone();
        report["executed"][0]["status"] = json!(status);
        let reply = read_results(report.to_string().as_bytes()).unwrap();
        assert_eq!(reply["passed"], expected, "{status}");
        assert_eq!(reply["results"]["executed"][0]["status"], status);
    }
    let mut blocked = base;
    blocked["blocked"] =
        json!([{"operation":"deploy","status":"blocked","receipt":null,"error":null}]);
    assert_eq!(
        read_results(blocked.to_string().as_bytes()).unwrap()["passed"],
        false
    );
}

#[test]
fn incomplete_collection_query_is_rejected_before_reading_the_checkout() {
    let error = check_collection(std::path::Path::new("."), b"{}".as_slice()).unwrap_err();
    assert!(error.contains("missing field"));
}
