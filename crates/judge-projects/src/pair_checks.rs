use crate::verified_languages;
use serde_json::Value;
use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

pub(crate) fn dedicated_pair<'a>(
    registry: &Value,
    collection: &'a [Value],
    prefix: &str,
    test_field: &str,
    row: &'a Value,
) -> Result<(&'a Value, &'a Value), String> {
    let (production, test) = if let Some(test) = row[test_field].as_str() {
        (
            row,
            collection
                .iter()
                .find(|p| p["id"] == test)
                .ok_or("E_TEST_PAIR: missing dedicated test")?,
        )
    } else {
        let prod = row["tests_for"]
            .as_str()
            .ok_or("E_TEST_PAIR: tests_for missing")?;
        (
            collection
                .iter()
                .find(|p| p["id"] == prod)
                .ok_or("E_TEST_PAIR: missing production")?,
            row,
        )
    };
    let prod_id = production["id"].as_str().unwrap();
    let test_id = test["id"].as_str().unwrap();
    if production[test_field] != test["id"]
        || test["tests_for"] != production["id"]
        || prod_id == test_id
        || collection
            .iter()
            .filter(|p| p[test_field] == test["id"])
            .count()
            != 1
        || collection
            .iter()
            .filter(|p| p["tests_for"] == production["id"])
            .count()
            != 1
        || prefix == "project" && (production["kind"] != "production" || test["kind"] != "test")
    {
        return Err("E_TEST_PAIR: nonreciprocal/shared dedicated pair".into());
    }
    if registry["schema_version"] == 2 {
        let implementation = production["language"].as_str().unwrap();
        let testing = test["language"].as_str().unwrap();
        if !verified_languages::dedicated_test_language(implementation, testing) {
            return Err(format!(
                "E_TEST_LANGUAGE: {prefix}:{prod_id} declares {implementation:?}, \
             but its dedicated test {prefix}:{test_id} declares {testing:?}; \
             require the same language or the declared shell-to-python exception"
            ));
        }
    }
    Ok((production, test))
}

/// Check the files and reciprocal pairs owned by definitions reached in the registered graph.
pub(crate) fn check<'a>(
    root: &Path,
    registry: &Value,
    filemap: &Value,
    artifacts: &[Value],
    affected: &BTreeSet<String>,
    definitions: impl Fn(&str) -> Vec<&'a str>,
    tests_for_owner: &BTreeMap<&str, Vec<&str>>,
) -> Result<(), String> {
    let projects = registry["projects"].as_array().unwrap();
    let scripts = registry["scripts"].as_array().unwrap();
    let files = filemap["files"].as_array().unwrap();
    let registered = |path: &str, owner: &str| -> Result<(), String> {
        let matches: Vec<_> = files
            .iter()
            .filter(|f| f["path"] == path && f["owner"] == owner)
            .collect();
        if matches.len() != 1 || !root.join(path).is_file() {
            return Err(format!(
                "E_TEST_PAIR: missing/exclusive owner {owner}: {path}"
            ));
        }
        Ok(())
    };
    let edge = |from: &str, kind: &str, to: &str| {
        filemap["project_edges"]
            .as_array()
            .unwrap()
            .iter()
            .any(|e| e["from"] == from && e["kind"] == kind && e["to"] == to)
    };
    let owners: BTreeSet<&str> = affected.iter().flat_map(|node| definitions(node)).collect();
    for (collection, prefix, test_field) in [
        (projects, "project", "test_project"),
        (scripts, "script", "test_script"),
    ] {
        for row in collection {
            let id = row["id"].as_str().unwrap();
            if !owners.contains(format!("{prefix}:{id}").as_str()) {
                continue;
            }
            let (production, test) = dedicated_pair(registry, collection, prefix, test_field, row)?;
            let prod_id = production["id"].as_str().unwrap();
            let test_id = test["id"].as_str().unwrap();
            if !edge(
                &format!("{prefix}:{prod_id}"),
                "test-execution",
                &format!("test:{test_id}"),
            ) {
                return Err("E_TEST_PAIR: missing explicit pair execution edge".into());
            }
            for identity in tests_for_owner
                .get(format!("{prefix}:{test_id}").as_str())
                .into_iter()
                .flatten()
            {
                if !edge(&format!("{prefix}:{prod_id}"), "test-execution", identity) {
                    return Err(format!(
                        "E_TEST_PAIR: missing explicit group execution edge {identity}"
                    ));
                }
            }
            for member in [production, test] {
                let owner = member["id"].as_str().unwrap();
                if prefix == "script" {
                    let path = member["path"].as_str().unwrap();
                    registered(path, owner)?;
                    if collection.iter().filter(|p| p["path"] == path).count() != 1 {
                        return Err("E_TEST_PAIR: shared script path".into());
                    }
                }
                // Legacy paths remain optional opaque owned inputs. No language parsing,
                // ancestor discovery or inferred output directory belongs to this judge.
                for field in ["manifest", "lockfile"] {
                    if let Some(path) = member[field].as_str() {
                        registered(path, owner)?;
                    }
                }
                let owned: Vec<_> = files.iter().filter(|f| f["owner"] == owner).collect();
                if owned.is_empty() {
                    return Err(format!(
                        "E_TEST_PAIR: project {owner} has no registered files"
                    ));
                }
                for file in owned {
                    registered(file["path"].as_str().unwrap(), owner)?;
                }
                for artifact in artifacts.iter().filter(|a| a["owner"] == owner) {
                    let path = artifact["path"].as_str().unwrap();
                    if files
                        .iter()
                        .any(|f| f["path"].as_str().unwrap().starts_with(path))
                    {
                        return Err(format!(
                            "E_TEST_PAIR: generated output contains registered input: {path}"
                        ));
                    }
                    for other in artifacts.iter().filter(|a| a["owner"] != owner) {
                        let other_path = other["path"].as_str().unwrap();
                        if path.starts_with(other_path) || other_path.starts_with(path) {
                            return Err(format!(
                                "E_TEST_PAIR: overlapping registered outputs: {path}, {other_path}"
                            ));
                        }
                    }
                }
            }
        }
    }
    Ok(())
}
