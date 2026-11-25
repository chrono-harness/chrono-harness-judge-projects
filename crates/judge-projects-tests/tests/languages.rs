#[path = "../../judge-projects/src/pair_checks.rs"]
mod pair_checks;
#[path = "../../judge-projects/src/verified_languages.rs"]
mod verified_languages;
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};
use std::fs;

struct PairCase {
    root: tempfile::TempDir,
    registry: Value,
    filemap: Value,
    definitions: BTreeMap<String, String>,
    test_owner: String,
}
impl PairCase {
    fn check(&self, affected: &BTreeSet<String>) -> Result<(), String> {
        pair_checks::check(
            self.root.path(),
            &self.registry,
            &self.filemap,
            &[],
            affected,
            |node| {
                self.definitions
                    .get(node)
                    .map(String::as_str)
                    .into_iter()
                    .collect()
            },
            &BTreeMap::from([(self.test_owner.as_str(), vec!["test:t"])]),
        )
    }
}
fn fixture(script: bool, implementation: &str, testing: &str) -> PairCase {
    let root = tempfile::tempdir().unwrap();
    let mut registry = json!({"schema_version":2,"status":"active","owners":["host","p","t"],"projects":[],"scripts":[]});
    let production = json!({"execute":{"operation":"host.produce","tool":"sh","argv":[]}});
    let verification = json!({"execute":{"operation":"host.verify","tool":"sh","argv":[]}});
    if script {
        registry["projects"] = json!([]);
        registry["scripts"] = json!([
            {"id":"p","path":"sources/value.data","test_script":"t","language":implementation,"actions":production},
            {"id":"t","path":"assays/contract.opaque","tests_for":"p","language":testing,"actions":verification}
        ]);
    } else {
        registry["projects"] = json!([
            {"id":"p","kind":"production","test_project":"t","language":implementation,"actions":production},
            {"id":"t","kind":"test","tests_for":"p","language":testing,"actions":verification}
        ]);
    }
    let prefix = if script { "script" } else { "project" };
    let production_owner = format!("{prefix}:p");
    let test_owner = format!("{prefix}:t");
    let definitions = BTreeMap::from([
        (production_owner.clone(), production_owner.clone()),
        (test_owner.clone(), test_owner.clone()),
        ("test:t".into(), test_owner.clone()),
    ]);
    let mut files = vec![];
    for (name, owner) in [("sources/value.data", "p"), ("assays/contract.opaque", "t")] {
        let path = root.path().join(name);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, "opaque fixture input").unwrap();
        files.push(json!({"path":name,"owner":owner}));
    }
    let filemap = json!({"files":files,"project_edges":[
        {"from": production_owner, "kind":"test-execution","to":"test:t"},
        {"from": test_owner, "kind":"test-execution","to":"test:t"}
    ]});
    PairCase {
        root,
        registry,
        filemap,
        definitions,
        test_owner,
    }
}
#[test]
fn same_declared_language_accepts_arbitrary_host_languages_and_paths() {
    for script in [false, true] {
        for language in [
            "rust",
            "go",
            "typescript",
            "python",
            "shell",
            "future host language",
        ] {
            let case = fixture(script, language, language);
            let prefix = if script { "script" } else { "project" };
            for node in [
                format!("{prefix}:p"),
                format!("{prefix}:t"),
                "test:t".into(),
            ] {
                case.check(&BTreeSet::from([node])).unwrap();
            }
        }
    }
}

#[test]
fn broken_dedicated_pairs_name_the_requested_owners() {
    for (script, key, prefix, field) in [
        (false, "projects", "project", "test_project"),
        (true, "scripts", "script", "test_script"),
    ] {
        let mut case = fixture(script, "rust", "rust");
        let check_pair = |case: &PairCase, selected: &str, expected: &str| {
            let error = case
                .check(&BTreeSet::from([format!("{prefix}:{selected}")]))
                .unwrap_err();
            assert!(error.starts_with("E_TEST_PAIR:"), "{error}");
            for id in [selected, expected] {
                assert!(error.contains(&format!("{prefix}:{id}")), "{error}");
            }
        };
        case.registry[key][0][field] = json!("absent-test");
        check_pair(&case, "p", "absent-test");
        case.registry[key][0][field] = json!("t");
        case.registry[key][1]["tests_for"] = json!("absent-production");
        check_pair(&case, "t", "absent-production");
        check_pair(&case, "p", "t");
    }
}

#[test]
fn shell_python_exception_is_explicit_and_directional() {
    for script in [false, true] {
        let prefix = if script { "script" } else { "project" };
        let affected = BTreeSet::from([format!("{prefix}:p")]);
        let case = fixture(script, "shell", "python");
        case.check(&affected).unwrap();
        for (implementation, testing) in [
            ("python", "shell"),
            ("rust", "python"),
            ("go", "typescript"),
        ] {
            let case = fixture(script, implementation, testing);
            let error = case.check(&affected).unwrap_err();
            assert!(error.starts_with("E_TEST_LANGUAGE:"), "{error}");
            assert!(error.contains(implementation) && error.contains(testing));
            let collection = if script { "scripts" } else { "projects" };
            let entry = &case.registry[collection][1]["actions"]["execute"];
            assert!(
                error.contains(&format!("actions.execute={entry}")),
                "{error}"
            );
        }
    }
}

#[test]
fn language_changes_check_the_selected_pair_and_leave_unrelated_pairs_alone() {
    let impacts: serde_json::Value =
        serde_json::from_str(include_str!("fixtures/language-impacts.json")).unwrap();
    let reached = |name: &str| -> BTreeSet<String> {
        serde_json::from_value(impacts[name]["reached"].clone()).unwrap()
    };
    for script in [false, true] {
        let mut case = fixture(script, "rust", "rust");
        let collection = if script { "scripts" } else { "projects" };
        case.registry[collection][1]["language"] = json!("python");
        let affected = reached(if script {
            "script_language"
        } else {
            "project_language"
        });
        assert!(
            case.check(&affected)
                .unwrap_err()
                .starts_with("E_TEST_LANGUAGE:")
        );
        case.check(&reached("docs")).unwrap();
    }
}

#[test]
fn language_v2_does_not_reinterpret_legacy_v1_pairs() {
    let mut case = fixture(false, "rust", "python");
    case.registry["schema_version"] = json!(1);
    for row in case.registry["projects"].as_array_mut().unwrap() {
        row.as_object_mut().unwrap().remove("language");
    }
    case.check(&BTreeSet::from(["project:p".into()])).unwrap();
}

#[test]
fn scoped_query_checks_only_the_affected_owner_pairs() {
    for (script, owner) in [(false, "project:p"), (true, "script:p")] {
        let case = fixture(script, "rust", "python");
        let registry = &case.registry;
        let query = |owners: &[&str]| {
            let request = json!({"registry":registry, "owners":owners});
            chrono_judge_projects::check_pairs_with(
                serde_json::to_vec(&request).unwrap().as_slice(),
                |original| {
                    assert_eq!(original, registry);
                    Ok(())
                },
            )
        };
        query(&[]).unwrap();
        let error = query(&[owner]).unwrap_err();
        assert!(error.starts_with("E_TEST_LANGUAGE:"), "{error}");
    }
}

#[test]
fn test_alias_alone_checks_the_defining_pair_and_ignores_unrelated_changes() {
    let aliases = BTreeSet::from(["test:t".into()]);
    for script in [false, true] {
        let case = fixture(script, "rust", "python");
        assert!(
            case.check(&aliases)
                .unwrap_err()
                .starts_with("E_TEST_LANGUAGE:")
        );
        case.check(&BTreeSet::from(["file:doc.txt".into()]))
            .unwrap();
    }
}

#[test]
fn public_pair_query_rejects_shared_links_and_kind_before_language() {
    let fixture = fixture(false, "rust", "python");
    let mut registry = fixture.registry;
    let base = registry.clone();
    let query = |v: &Value| {
        let q = json!({"registry":v,"owners":["project:p"]});
        chrono_judge_projects::check_pairs_with(q.to_string().as_bytes(), |_| Ok(())).unwrap_err()
    };
    assert!(query(&registry).starts_with("E_TEST_LANGUAGE:"));
    for (field, value) in [("test_project", "t"), ("tests_for", "p")] {
        registry = base.clone();
        registry["projects"]
            .as_array_mut()
            .unwrap()
            .push(json!({"id":"extra",field:value}));
        assert_eq!(
            query(&registry),
            "E_TEST_PAIR: nonreciprocal/shared dedicated pair project:p and project:t"
        );
    }
    registry = base.clone();
    registry["projects"][1]["kind"] = json!("production");
    assert_eq!(
        query(&registry),
        "E_TEST_PAIR: nonreciprocal/shared dedicated pair project:p and project:t"
    );
    registry = base.clone();
    registry["projects"][0]["test_project"] = json!("p");
    assert_eq!(
        query(&registry),
        "E_TEST_PAIR: nonreciprocal/shared dedicated pair project:p and project:p"
    );
}
