#![allow(unexpected_cfgs)]
#[cfg(not(verus_keep_ghost))]
use vstd::prelude::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

verus! {
/// A decoded registry table exposes only the columns named by the caller.
pub trait RegistryColumns {
    spec fn height(&self) -> nat;
    spec fn cell(&self, row: int, column: int) -> Option<Seq<char>>;
    fn len(&self) -> (n: usize) ensures n == self.height();
    fn get(&self, row: usize, column: usize) -> (value: Option<&str>)
        requires row < self.height(),
        ensures self.cell(row as int, column as int) == match value {Some(s) => Some(s@), None => None};
}

pub open spec fn matches_columns<T: RegistryColumns>(table: &T, row: int, key: Seq<&str>) -> bool {
    forall|col: int| 0 <= col < key.len() ==> #[trigger] table.cell(row, col) == Some(key[col]@)
}

fn row_matches<T: RegistryColumns>(table: &T, row: usize, key: &[&str]) -> (yes: bool)
    requires row < table.height(),
    ensures yes == matches_columns(table, row as int, key@),
{
    let mut col = 0;
    while col < key.len()
        invariant col <= key.len(), row < table.height(),
            forall|i: int| 0 <= i < col ==> #[trigger] table.cell(row as int,i) == Some(key@[i]@),
        decreases key.len() - col,
    {
        match table.get(row,col) {
            Some(s) if <&str as vstd::contrib::exec_spec::ExecSpecEq>::exec_eq(s,key[col]) => (),
            _ => return false,
        }
        col += 1;
    }
    true
}

/// Return the first matching row, requiring uniqueness for exclusive claims.
pub fn lookup_row<T: RegistryColumns>(table: &T, key: &[&str], exclusive: bool) -> (found: Option<usize>)
    ensures
        found matches Some(i) ==> i < table.height() && matches_columns(table,i as int,key@)
            && (forall|j: int| 0 <= j < i ==> !#[trigger] matches_columns(table,j,key@))
            && (exclusive ==> forall|j: int| i < j < table.height() ==> !#[trigger] matches_columns(table,j,key@)),
        found.is_none() ==> (!(exists|j: int| 0 <= j < table.height() && #[trigger] matches_columns(table,j,key@))
            || (exclusive && exists|a: int,b: int| 0 <= a < b < table.height() &&
                #[trigger] matches_columns(table,a,key@) && #[trigger] matches_columns(table,b,key@))),
{
    let size = table.len();
    let mut first: Option<usize> = None;
    let mut i = 0;
    while i < size
        invariant i <= size, size == table.height(),
            first.is_some() ==> exclusive,
            first matches Some(n) ==> n < i && matches_columns(table,n as int,key@),
            forall|j: int| 0 <= j < i && #[trigger] matches_columns(table,j,key@) ==> first == Some(j as usize),
        decreases size - i,
    {
        if row_matches(table,i,key) {
            if !exclusive { return Some(i); }
            if let Some(n) = first {
                assert(exists|a: int,b: int| 0 <= a < b < table.height() &&
                    #[trigger] matches_columns(table,a,key@) && #[trigger] matches_columns(table,b,key@)) by {
                    assert(matches_columns(table,n as int,key@) && matches_columns(table,i as int,key@));
                }
                return None;
            }
            first = Some(i);
        }
        i += 1;
    }
    first
}

/// FILEMAP output declarations use literal UTF-8 byte prefixes.
pub fn path_prefix(path: &[u8], prefix: &[u8]) -> (yes: bool)
    ensures yes == (prefix.len() <= path.len() &&
        forall|i: int| 0 <= i < prefix.len() ==> #[trigger] path@[i] == #[trigger] prefix@[i]),
{
    if path.len() < prefix.len() { return false; }
    let mut i = 0;
    while i < prefix.len()
        invariant i <= prefix.len() <= path.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] path@[j] == #[trigger] prefix@[j],
        decreases prefix.len() - i,
    {
        if path[i] != prefix[i] { return false; }
        i += 1;
    }
    true
}

pub fn owner_key(prefix: &str, id: &str) -> (key: String)
    ensures key@ == prefix@ + ":"@ + id@,
{
    let mut key = prefix.to_string();
    vstd::string::StringExecFns::append(&mut key, ":");
    vstd::string::StringExecFns::append(&mut key, id);
    key
}

pub fn selects_owner(owners: &std::collections::BTreeSet<String>, prefix: &str, id: &str) -> (selected: bool)
    requires vstd::laws_cmp::obeys_cmp::<String>(),
    ensures exists|key:String| key@ == prefix@ + ":"@ + id@ && selected == #[trigger] owners@.contains(key),
{
    broadcast use vstd::std_specs::btree::group_btree_axioms;
    let key = owner_key(prefix,id);
    let present = owners.contains(&key);
    assert(key@ == prefix@ + ":"@ + id@ && present == owners@.contains(key));
    present
}

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
struct Columns<'a> {
    rows: &'a [Value],
    names: &'a [&'a str],
}

#[cfg(not(verus_keep_ghost))]
impl RegistryColumns for Columns<'_> {
    fn len(&self) -> usize {
        self.rows.len()
    }
    fn get(&self, row: usize, col: usize) -> Option<&str> {
        self.names
            .get(col)
            .and_then(|name| self.rows[row][*name].as_str())
    }
}

#[cfg(not(verus_keep_ghost))]
pub(crate) fn registered_row<'a>(
    rows: &'a [Value],
    columns: &[&str],
    key: &[&str],
    exclusive: bool,
) -> Option<&'a Value> {
    lookup_row(
        &Columns {
            rows,
            names: columns,
        },
        key,
        exclusive,
    )
    .map(|i| &rows[i])
}

/// CI and full visit the same registry rows in declaration order.
#[cfg(not(verus_keep_ghost))]
pub(crate) fn selected_pairs<'a>(
    registry: &'a Value,
    owners: &BTreeSet<String>,
    mut visit: impl FnMut(&'a [Value], &str, &str, &'a Value) -> Result<(), String>,
) -> Result<(), String> {
    for (rows, prefix, field) in [
        ("projects", "project", "test_project"),
        ("scripts", "script", "test_script"),
    ] {
        let rows = registry[rows].as_array().unwrap();
        for row in rows {
            if selects_owner(owners, prefix, row["id"].as_str().unwrap()) {
                visit(rows, prefix, field, row)?;
            }
        }
    }
    Ok(())
}

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
    let files = filemap["files"].as_array().unwrap();
    let registered = |path: &str, owner: &str| -> Result<(), String> {
        if registered_row(files, &["path", "owner"], &[path, owner], true).is_none()
            || !root.join(path).is_file()
        {
            return Err(format!(
                "E_TEST_PAIR: missing/exclusive owner {owner}: {path}"
            ));
        }
        Ok(())
    };
    let edge = |from: &str, kind: &str, to: &str| {
        registered_row(
            filemap["project_edges"].as_array().unwrap(),
            &["from", "kind", "to"],
            &[from, kind, to],
            false,
        )
        .is_some()
    };
    let owners: BTreeSet<String> = affected
        .iter()
        .flat_map(|node| definitions(node))
        .map(str::to_owned)
        .collect();
    selected_pairs(registry, &owners, |collection, prefix, test_field, row| {
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
                if registered_row(collection, &["path"], &[path], true).is_none() {
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
                    .any(|f| path_prefix(f["path"].as_str().unwrap().as_bytes(), path.as_bytes()))
                {
                    return Err(format!(
                        "E_TEST_PAIR: generated output contains registered input: {path}"
                    ));
                }
                for other in artifacts.iter().filter(|a| a["owner"] != owner) {
                    let other_path = other["path"].as_str().unwrap();
                    if path_prefix(path.as_bytes(), other_path.as_bytes())
                        || path_prefix(other_path.as_bytes(), path.as_bytes())
                    {
                        return Err(format!(
                            "E_TEST_PAIR: overlapping registered outputs: {path}, {other_path}"
                        ));
                    }
                }
            }
        }
        Ok(())
    })
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
