//! 执行原件的终态、完整身份和保留决策；实际 IO 由 state 所有者执行。
#![allow(unexpected_cfgs)]
use std::collections::{BTreeMap, BTreeSet};
use vstd::contrib::exec_spec::ExecSpecEq;
#[cfg(not(verus_keep_ghost))]
use vstd::prelude::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
#[path = "compiler.rs"]
pub mod compiler;
#[cfg(verus_keep_ghost)]
#[path = "routes.rs"]
pub mod operation_claims;
#[cfg(verus_keep_ghost)]
#[path = "wire.rs"]
pub mod path_components;
#[cfg(verus_keep_ghost)]
#[path = "lib.rs"]
pub mod project_dispatch;

#[cfg(verus_keep_ghost)]
#[path = "state.rs"]
pub mod operation_io;

#[cfg(verus_keep_ghost)]
#[path = "receipt.rs"]
pub mod receipt_timeout;

verus! {

/// Check the two path observations before opening either the host runner or the routes program.
pub fn admit_query_location(same_root: bool, absolute_routes: bool) -> (res: Result<(), &'static str>)
    ensures res.is_ok() == (same_root && absolute_routes),
        res matches Err(e) ==> e@ == "E_PLAN_BINDING: execute from the plan root with an absolute routes executable"@,
{
    if same_root && absolute_routes { Ok(()) } else {
        Err("E_PLAN_BINDING: execute from the plan root with an absolute routes executable")
    }
}

/// A failed execution keeps its own error. A completed execution publishes its actual
/// result together with the first trace error, and returns the publisher's write/flush result.
pub fn publish_plan<T, F>(
    work: Result<T, String>, diagnostic: Option<String>, publish: F,
) -> (out: Result<(), String>)
    where F: FnOnce(T, Option<String>) -> Result<(), String>,
    requires forall|value: T| work == Ok::<T, String>(value) ==> #[trigger] publish.requires((value, diagnostic)),
    ensures match work {
        Err(error) => out == Err::<(), String>(error),
        Ok(value) => publish.ensures((value, diagnostic), out),
    },
{
    match work { Err(error) => Err(error), Ok(value) => publish(value, diagnostic) }
}

/// A diagnostic sink may reject the message after the query already failed.
pub fn query_exit<F>(result: Result<(), String>, emit: F) -> (code: u8)
    where F: FnOnce(String) -> bool,
    requires forall|e: String| result == Err::<(), String>(e) ==> #[trigger] emit.requires((e,)),
    ensures code == (if result.is_ok() { 0u8 } else { 2u8 }),
{
    match result { Ok(()) => 0, Err(error) => { emit(error); 2 } }
}

/// A length-n sequence of distinct indices in 0..n is a permutation of the operations.
pub open spec fn dispatch_order_covers(order: Seq<usize>, count: nat) -> bool {
    order.len() == count
        && (forall|i: int| 0 <= i < order.len() ==> #[trigger] order[i] < count)
        && (forall|i: int, j: int| 0 <= i < j < order.len() ==>
            #[trigger] order[i] != #[trigger] order[j])
}

/// Admit the actual order returned by routes before any worker indexes the plan.
pub fn admit_dispatch_order(order: &[usize], count: usize) -> (result: Result<(), &'static str>)
    ensures result.is_ok() == dispatch_order_covers(order@, count as nat),
        result matches Err(message) ==> message@ ==
            "E_EXECUTION_PLAN: routes dispatch order must cover every operation once"@,
{
    let invalid = "E_EXECUTION_PLAN: routes dispatch order must cover every operation once";
    if order.len() != count {
        return Err(invalid);
    }
    let mut seen = vec![false; count];
    let mut i = 0;
    while i < order.len()
        invariant
            invalid@ == "E_EXECUTION_PLAN: routes dispatch order must cover every operation once"@,
            order.len() == count, seen.len() == count, i <= count,
            forall|j: int| 0 <= j < i ==> #[trigger] order@[j] < count,
            forall|a: int, b: int| 0 <= a < b < i ==>
                #[trigger] order@[a] != #[trigger] order@[b],
            forall|slot: int| 0 <= slot < count ==> #[trigger] seen@[slot] ==
                (exists|j: int| 0 <= j < i && #[trigger] order@[j] == slot),
        decreases count - i,
    {
        let index = order[i];
        if index >= count {
            assert(order@[i as int] >= count);
            return Err(invalid);
        }
        if seen[index] {
            assert(exists|j: int| 0 <= j < i && #[trigger] order@[j] == index);
            return Err(invalid);
        }
        seen[index] = true;
        assert(order@[i as int] == index);
        i += 1;
    }
    Ok(())
}

pub open spec fn selected_test_passed(results: Map<String, String>, test: String) -> bool {
    results.contains_key(test) && results[test]@ == "passed"@
}

/// Return the actual missing or unsuccessful test so the owning operation can name it.
pub fn uncovered_test<'a>(
    selected: &'a [String], results: &BTreeMap<String, String>,
) -> (missing: Option<&'a String>)
    requires vstd::laws_cmp::obeys_cmp::<String>(),
    ensures match missing {
        Some(test) => exists|i: int| 0 <= i < selected.len() && #[trigger] selected@[i] == *test
            && !selected_test_passed(results@, *test)
            && forall|j: int| 0 <= j < i ==> selected_test_passed(results@, #[trigger] selected@[j]),
        None => forall|i: int| 0 <= i < selected.len() ==> selected_test_passed(results@, #[trigger] selected@[i]),
    },
{
    broadcast use vstd::std_specs::btree::group_btree_axioms;
    let mut i = 0;
    while i < selected.len()
        invariant vstd::laws_cmp::obeys_cmp::<String>(), i <= selected.len(),
            forall|j: int| 0 <= j < i ==> selected_test_passed(results@, #[trigger] selected@[j]),
        decreases selected.len() - i,
    {
        let test = &selected[i];
        let passed = match results.get(test) {
            Some(status) => <&str>::exec_eq(status.as_str(), "passed"),
            None => false,
        };
        if !passed {
            assert(selected@[i as int] == *test);
            return Some(test);
        }
        i += 1;
    }
    None
}

/// A collected original can preserve an explicit retirement without a replacement.
/// Live and first-time collection require a registered downstream validator for that case.
pub fn declared_removal<'a>(
    declared: Option<&'a Option<String>>, allow_without_replacement: bool,
) -> (accepted: Option<&'a Option<String>>)
    ensures accepted == match declared {
        Some(target) if target.is_some() || allow_without_replacement => declared,
        _ => None,
    },
{
    match declared {
        Some(target) if target.is_some() || allow_without_replacement => Some(target),
        _ => None,
    }
}

/// A unit may hand an unexecuted replacement to its registered peer.
pub fn replacement_covered(status: Option<&String>, assigned_to_peer: bool) -> (ok: bool)
    ensures ok == (assigned_to_peer || match status {
        Some(s) => s@ == "passed"@, None => false,
    }),
{
    assigned_to_peer || match status {
        Some(s) => <&str>::exec_eq(s.as_str(), "passed"),
        None => false,
    }
}

pub open spec fn same_target(a: Option<String>, b: Option<String>) -> bool {
    match (a,b) {
        (Some(x), Some(y)) => x@ == y@,
        (None,None) => true,
        _ => false,
    }
}

fn same_replacement(a: &Option<String>, b: &Option<String>) -> (equal: bool)
    ensures equal == same_target(*a, *b),
{
    match (a,b) {
        (Some(x),Some(y)) => <&str>::exec_eq(x.as_str(),y.as_str()),
        (None,None) => true,
        _ => false,
    }
}

/// Merge one unit or global obligation, preserving source order and all other keys.
pub fn record_removal(
    removed: &mut BTreeMap<String, Option<String>>, sources: &mut BTreeMap<String, Vec<String>>,
    id: &String, replacement: &Option<String>, source: &str,
) -> (accepted: bool)
    requires vstd::laws_cmp::obeys_cmp::<String>(),
    ensures
        accepted == (!old(removed)@.contains_key(*id) || same_target(old(removed)@[*id], *replacement)),
        accepted ==> removed@.dom() == old(removed)@.dom().insert(*id),
        accepted ==> same_target(removed@[*id], *replacement),
        accepted ==> forall|other: String| other != *id && old(removed)@.contains_key(other) ==>
            #[trigger] removed@[other] == old(removed)@[other],
        accepted ==> sources@.dom() == old(sources)@.dom().insert(*id),
        accepted ==> sources@[*id]@.len() ==
            (if old(sources)@.contains_key(*id) { old(sources)@[*id]@.len() } else { 0 }) + 1,
        accepted ==> sources@[*id]@.last()@ == source@,
        accepted && old(sources)@.contains_key(*id) ==> sources@[*id]@.drop_last() == old(sources)@[*id]@,
        accepted ==> forall|other: String| other != *id && old(sources)@.contains_key(other) ==>
            #[trigger] sources@[other] == old(sources)@[other],
        !accepted ==> removed@ == old(removed)@ && sources@ == old(sources)@,
{
    broadcast use vstd::std_specs::btree::group_btree_axioms;
    if let Some(previous) = removed.get(id) {
        if !same_replacement(previous,replacement) { return false; }
    } else {
        let value = match replacement {
            Some(target) => Some(target.clone()),
            None => None,
        };
        removed.insert(id.clone(), value);
    }
    let mut names = sources.remove(id).unwrap_or(Vec::new());
    names.push(source.to_string());
    sources.insert(id.clone(), names);
    true
}

/// Receipt and original payloads are carried through the wire without inspecting them here.
#[cfg_attr(not(verus_keep_ghost), derive(Clone, Debug, serde::Serialize, serde::Deserialize))]
pub struct OperationRow<R, O> {
    pub operation: String,
    pub status: String,
    pub receipt: Option<R>,
    pub error: Option<String>,
    #[cfg_attr(not(verus_keep_ghost), serde(default, skip_serializing_if = "Option::is_none"))]
    pub original: Option<O>,
}

pub fn has_execution_error<R, O>(executed: &[OperationRow<R, O>]) -> (found: bool)
    ensures found == exists|i: int| 0 <= i < executed.len() && #[trigger] executed@[i].status@ == "error"@,
{
    let mut i = 0;
    while i < executed.len()
        invariant i <= executed.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] executed@[j].status@ != "error"@,
        decreases executed.len() - i,
    {
        if <&str>::exec_eq(executed[i].status.as_str(), "error") {
            return true;
        }
        i += 1;
    }
    false
}

pub open spec fn all_test_statuses_passed(results: Map<String, String>) -> bool {
    forall|status: String| #[trigger] results.values().contains(status) ==> status@ == "passed"@
}

fn test_statuses_pass(tests: &BTreeMap<String, String>) -> (passed: bool)
    requires vstd::laws_cmp::obeys_cmp::<String>(),
    ensures passed == all_test_statuses_passed(tests@),
{
    broadcast use vstd::std_specs::btree::group_btree_axioms;
    let mut statuses = tests.values();
    loop
        invariant 0 <= statuses@.0 <= statuses@.1.len(),
            statuses@.1.to_set() == tests@.values(),
            forall|j: int| 0 <= j < statuses@.0 ==> #[trigger] statuses@.1[j]@ == "passed"@,
        decreases statuses@.1.len() - statuses@.0,
    {
        let Some(status) = statuses.next() else {
            assert forall|value: String| #[trigger] tests@.values().contains(value) implies value@ == "passed"@ by {
                assert(statuses@.1.contains(value));
                let j = choose|j: int| 0 <= j < statuses@.1.len() && statuses@.1[j] == value;
                assert(statuses@.1[j]@ == "passed"@);
            }
            return true;
        };
        if !<&str>::exec_eq(status.as_str(), "passed") {
            assert(tests@.values().contains(*status));
            return false;
        }
    }
}

/// A unit report must account for exactly the tests assigned to this unit.
pub fn unit_test_results_complete(
    owned: &BTreeSet<String>, tests: &BTreeMap<String, String>,
) -> (complete: bool)
    requires vstd::laws_cmp::obeys_cmp::<String>(),
    ensures complete == (tests@.dom() == owned@
        && forall|id: String| owned@.contains(id) ==> selected_test_passed(tests@, id)),
{
    broadcast use vstd::std_specs::btree::group_btree_axioms;
    if owned.len() != tests.len() {
        return false;
    }
    let mut ids = owned.iter();
    loop
        invariant
            vstd::laws_cmp::obeys_cmp::<String>(),
            tests@.dom().len() == owned@.len(),
            ids@.1.to_set() == owned@,
            0 <= ids@.0 <= ids@.1.len(),
            forall|j: int| 0 <= j < ids@.0 ==> selected_test_passed(tests@, #[trigger] ids@.1[j]),
        decreases ids@.1.len() - ids@.0,
    {
        let Some(id) = ids.next() else {
            assert forall|id: String| owned@.contains(id) implies selected_test_passed(tests@, id) by {
                assert(ids@.1.contains(id));
                let j = choose|j: int| 0 <= j < ids@.1.len() && ids@.1[j] == id;
                assert(selected_test_passed(tests@, ids@.1[j]));
            }
            proof { vstd::set_lib::lemma_subset_equality(owned@, tests@.dom()); }
            return true;
        };
        let passed = match tests.get(id) {
            Some(status) => <&str>::exec_eq(status.as_str(), "passed"),
            None => false,
        };
        assert(passed == selected_test_passed(tests@, *id));
        assert(ids@.1[ids@.0 - 1] == *id);
        if !passed {
            assert(owned@.contains(*id));
            return false;
        }
    }
}

pub fn report_passed<R, O>(
    executed: &[OperationRow<R, O>], blocked: usize, selected: &[String], tests: &BTreeMap<String, String>,
) -> (passed: bool)
    requires vstd::laws_cmp::obeys_cmp::<String>(),
    ensures passed == (blocked == 0
        && (forall|i: int| 0 <= i < executed.len() ==> #[trigger] executed@[i].status@ == "passed"@)
        && all_test_statuses_passed(tests@)
        && (forall|i: int| 0 <= i < selected.len() ==> selected_test_passed(tests@, #[trigger] selected@[i]))),
{
    broadcast use vstd::std_specs::btree::group_btree_axioms;
    if blocked != 0 { return false; }
    let mut i = 0;
    while i < executed.len()
        invariant i <= executed.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] executed@[j].status@ == "passed"@,
        decreases executed.len() - i,
    {
        if !<&str>::exec_eq(executed[i].status.as_str(), "passed") { return false; }
        i += 1;
    }
    test_statuses_pass(tests) && uncovered_test(selected, tests).is_none()
}

/// Publish one explicit coverage diagnosis from a failed operation's own complete stream.
pub fn report_coverage_cause(complete: bool, code: &str, detail_bytes: usize) -> (report: bool)
    ensures report == (complete && code@ == "E_VERUS_COVERAGE"@ && 0 < detail_bytes <= 1024),
{
    complete && <&str>::exec_eq(code, "E_VERUS_COVERAGE") && detail_bytes > 0 && detail_bytes <= 1024
}

/// process_terminal 是现役 process_completion_known 对真实退出码／signal
/// 及全部自有工作加入结果的判断。
/// None 精确保留没有回执，与已返回但终态未知的 Some(false) 分开。
pub struct OperationObservation<'a> {
    pub status: &'a str,
    pub process_terminal: Option<bool>,
}

pub open spec fn operation_is_terminal(row: &OperationObservation) -> bool {
    row.status@ == "blocked"@ || row.process_terminal == Some(true)
}

pub fn terminal(row: &OperationObservation) -> (known: bool)
    ensures known == operation_is_terminal(row),
{
    <&str>::exec_eq(row.status, "blocked")
        || match row.process_terminal { Some(value) => value, None => false }
}

pub fn operation_state(row: &OperationObservation) -> (state: &'static str)
    ensures state@ == if operation_is_terminal(row) { "completed"@ } else { "unknown"@ },
{
    if terminal(row) { "completed" } else { "unknown" }
}

pub fn all_terminal(rows: &Vec<OperationObservation>) -> (known: bool)
    ensures known == (forall|i: int| 0 <= i < rows.len() ==>
        operation_is_terminal(#[trigger] &rows[i])),
{
    let mut i = 0;
    while i < rows.len()
        invariant 0 <= i <= rows.len(),
            forall|j: int| 0 <= j < i ==> operation_is_terminal(#[trigger] &rows[j]),
        decreases rows.len() - i,
    {
        if !terminal(&rows[i]) { return false; }
        i += 1;
    }
    true
}

/// Once the result is durable, only this operation's completed successful proof
/// may release the measured library and dep-info files.
pub fn can_release_compiler_files(status: &str, joined: bool, owned_output: bool) -> (release: bool)
    ensures release == (status@ == "passed"@ && joined && owned_output),
{
    <&str>::exec_eq(status, "passed") && joined && owned_output
}

pub open spec fn original_matches(
    digest: Seq<char>, length: u64, expected: Option<(&str, u64)>,
) -> bool {
    match expected {
        None => true,
        Some((wanted_digest, wanted_length)) => digest == wanted_digest@ && length == wanted_length,
    }
}

pub fn validate_original(
    digest: &str, length: u64, expected: Option<(&str, u64)>,
) -> (out: Result<(), &'static str>)
    ensures out.is_ok() == original_matches(digest@, length, expected),
        match out {
            Err(message) => message@ == "operation original differs from the actual process result"@,
            Ok(()) => true,
        },
{
    match expected {
        None => Ok(()),
        Some((wanted_digest, wanted_length)) => {
            if <&str>::exec_eq(digest, wanted_digest) && length == wanted_length { Ok(()) }
            else { Err("operation original differs from the actual process result") }
        },
    }
}

}
