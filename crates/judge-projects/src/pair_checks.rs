#![allow(unexpected_cfgs)]
#[cfg(not(verus_keep_ghost))]
use vstd::prelude::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

verus! {
pub enum PairLookupError<'a> {
    MissingTest(&'a str),
    MissingProductionLink,
    MissingProduction(&'a str),
}

/// Resolve the opposite row using the same first-match lookup as the registry iterator.
pub fn lookup_pair<'a, T, F>(
    row: T, forward: Option<&'a str>, reverse: Option<&'a str>, find: F,
) -> (out: Result<(T, T), PairLookupError<'a>>)
    where F: FnOnce(&'a str) -> Option<T>,
    requires forall|id: &'a str| find.requires((id,)),
    ensures match (forward, reverse) {
        (Some(id), _) => exists|other: Option<T>| #[trigger] find.ensures((id,), other)
            && out == match other {
                Some(test) => Ok((row, test)),
                None => Err(PairLookupError::MissingTest(id)),
            },
        (None, Some(id)) => exists|other: Option<T>| #[trigger] find.ensures((id,), other)
            && out == match other {
                Some(production) => Ok((production, row)),
                None => Err(PairLookupError::MissingProduction(id)),
            },
        (None, None) => out == Err::<(T, T), PairLookupError>(PairLookupError::MissingProductionLink),
    },
{
    if let Some(id) = forward {
        let other = find(id);
        assert(find.ensures((id,), other));
        return match other {
            Some(test) => Ok((row, test)),
            None => Err(PairLookupError::MissingTest(id)),
        };
    }
    let id = match reverse { Some(id) => id, None => return Err(PairLookupError::MissingProductionLink) };
    let other = find(id);
    assert(find.ensures((id,), other));
    match other {
        Some(production) => Ok((production, row)),
        None => Err(PairLookupError::MissingProduction(id)),
    }
}
}

#[cfg(not(verus_keep_ghost))]
use crate::verified_languages;
#[cfg(not(verus_keep_ghost))]
use serde_json::Value;
#[cfg(not(verus_keep_ghost))]
use std::collections::{BTreeMap, BTreeSet};
#[cfg(not(verus_keep_ghost))]
use std::path::Path;

#[cfg(not(verus_keep_ghost))]
struct RegistryLinks<'a> {
    rows: &'a [Value],
    test_field: &'a str,
}

#[cfg(not(verus_keep_ghost))]
impl verified_languages::PairTable for RegistryLinks<'_> {
    fn len(&self) -> usize {
        self.rows.len()
    }

    fn link(&self, index: usize, forward: bool) -> Option<&str> {
        let field = if forward {
            self.test_field
        } else {
            "tests_for"
        };
        self.rows[index][field].as_str()
    }
}

#[cfg(not(verus_keep_ghost))]
pub(crate) fn dedicated_pair<'a>(
    registry: &Value,
    collection: &'a [Value],
    prefix: &str,
    test_field: &str,
    row: &'a Value,
) -> Result<(&'a Value, &'a Value), String> {
    let row_id = row["id"].as_str().unwrap();
    let (production, test) = lookup_pair(
        row,
        row[test_field].as_str(),
        row["tests_for"].as_str(),
        |id| collection.iter().find(|p| p["id"] == id),
    )
    .map_err(|error| match error {
        PairLookupError::MissingTest(id) => {
            format!("E_TEST_PAIR: {prefix}:{row_id} names missing dedicated test {prefix}:{id}")
        }
        PairLookupError::MissingProductionLink => {
            format!("E_TEST_PAIR: {prefix}:{row_id} is missing tests_for")
        }
        PairLookupError::MissingProduction(id) => {
            format!("E_TEST_PAIR: {prefix}:{row_id} names missing production {prefix}:{id}")
        }
    })?;
    let prod_id = production["id"].as_str().unwrap();
    let test_id = test["id"].as_str().unwrap();
    let links = RegistryLinks {
        rows: collection,
        test_field,
    };
    if !verified_languages::dedicated_pair(
        &links,
        prefix,
        prod_id,
        test_id,
        production[test_field].as_str(),
        test["tests_for"].as_str(),
        production["kind"].as_str(),
        test["kind"].as_str(),
    ) {
        return Err(format!(
            "E_TEST_PAIR: nonreciprocal/shared dedicated pair {prefix}:{prod_id} and {prefix}:{test_id}"
        ));
    }
    let implementation = &production["language"];
    let testing = &test["language"];
    if !verified_languages::registered_test_language(
        registry["schema_version"].as_u64(),
        implementation.as_str(),
        testing.as_str(),
    ) {
        let entry = &test["actions"]["execute"];
        return Err(format!(
            "E_TEST_LANGUAGE: {prefix}:{prod_id} declares {implementation}, \
             but its dedicated test {prefix}:{test_id} declares {testing} at actions.execute={entry}; \
             require the same language or the declared shell-to-python exception"
        ));
    }
    Ok((production, test))
}

/// Check the files and reciprocal pairs owned by definitions reached in the registered graph.
#[cfg(not(verus_keep_ghost))]
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

/// The checked method supplies the helper owner and the original process supplies its argv.
#[cfg(not(verus_keep_ghost))]
pub(crate) fn assertion_language<'a>(
    registry: &'a Value,
    production: &str,
    implementation: &str,
    test: &str,
    owner: &str,
    operation: &str,
    argv: &[String],
    receipt: &str,
) -> Result<&'a str, String> {
    let (kind, id) = owner
        .split_once(':')
        .ok_or("assertion helper owner missing")?;
    let table = match kind {
        "project" => "projects",
        "script" => "scripts",
        _ => {
            return Err(format!(
                "E_TEST_BINDING: invalid assertion helper owner {owner}"
            ));
        }
    };
    let language = registry[table]
        .as_array()
        .and_then(|rows| rows.iter().find(|row| row["id"].as_str() == Some(id)))
        .and_then(|row| row["language"].as_str())
        .ok_or_else(|| {
            format!("E_TEST_BINDING: assertion helper {owner} has no registered language")
        })?;
    if !verified_languages::dedicated_test_language(implementation, language) {
        return Err(format!(
            "E_TEST_LANGUAGE: {production} declares {implementation:?}, but {test} executed assertion helper {owner} ({language:?}), operation {operation}, argv={}, receipt={receipt}",
            serde_json::json!(argv)
        ));
    }
    Ok(language)
}
