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
    raw["tests"] = json!([]);
    assert!(read_results(raw.to_string().as_bytes()).is_err());
}

#[test]
fn incomplete_collection_query_is_rejected_before_reading_the_checkout() {
    let error = check_collection(std::path::Path::new("."), b"{}".as_slice()).unwrap_err();
    assert!(error.contains("missing field"));
}

#[test]
fn compiler_originals_use_the_operation_directory_and_its_byte_limit() {
    use chrono_judge_projects::Receipt;
    let dir = tempfile::tempdir().unwrap();
    let plan = serde_json::from_value(json!({
        "schema": "chrono-execution-plan/v1", "identity": "fixture", "binding": {},
        "root": dir.path(), "environment": {}, "selected": {}, "operations": [], "tools": {}
    }))
    .unwrap();
    let args = [
        "--crate-type=lib",
        "--no-cheating",
        "--no-external-by-default",
        "--num-threads",
        "2",
        "--output-json",
        "--compile",
        "--emit=link=library.rlib,dep-info=library.rlib.d",
        "bounded.rs",
        "-o",
        "library.rlib",
        "-Zchecksum-hash-algorithm=sha256",
    ]
    .map(String::from)
    .to_vec();
    let operation = serde_json::from_value(json!({
        "method": {"owner":"fixture", "operation":"verify", "tool":"verus", "argv":args,
                   "output_contract":{"version":"fixture","commit":"fixture"}},
        "predecessors":[], "timeout_seconds":1, "output_limit_bytes":4
    }))
    .unwrap();
    let observe = |exit: i32, failure: Option<&str>| {
        let process = serde_json::from_value(json!({
            "argv":args, "cwd":dir.path(), "environment":{}, "environment_digest":"",
            "stdin_sha256":"", "stdout_bytes":[], "stderr_bytes":[], "stdout_sha256":"",
            "stderr_sha256":"", "failure":failure, "exit_code":exit, "stdout":"", "stderr":"",
            "executable":"verus", "sha256":""
        }))
        .unwrap();
        Receipt::observe(&plan, &operation, process).unwrap()
    };
    let dependency = |exit, failure| observe(exit, failure).compiler_dependency.unwrap();
    let artifact = || observe(0, None).compiler_artifact.unwrap();
    assert!(dependency(0, None).is_err());
    assert!(artifact().is_err());
    std::fs::write(dir.path().join("library.rlib.d"), [0u8, 255, 1, 127]).unwrap();
    let content = vec![255u8; 65537];
    std::fs::write(dir.path().join("library.rlib"), &content).unwrap();
    assert_eq!(dependency(0, None).unwrap(), [0, 255, 1, 127]);
    let original = artifact().unwrap();
    assert_eq!(original.path, b"library.rlib");
    assert_eq!(
        original.sha256,
        b"ef9993e97e36b66b65b16a741da437aecddffa22185e176a49f8cfe9ecc7a07c"
    );
    assert_eq!(original.length, 65537);
    assert!(dependency(9, None).is_err());
    assert!(dependency(0, Some("capture failed")).is_err());
    std::fs::write(dir.path().join("library.rlib.d"), [255u8; 5]).unwrap();
    assert!(
        dependency(0, None)
            .unwrap_err()
            .contains("exceeds its bound")
    );
    std::fs::remove_file(dir.path().join("library.rlib")).unwrap();
    std::os::unix::fs::symlink("library.rlib.d", dir.path().join("library.rlib")).unwrap();
    assert!(artifact().is_err());
}
