//! 执行原件的终态、完整身份和保留决策；实际 IO 由 state 所有者执行。
#![allow(unexpected_cfgs)]
use std::collections::BTreeMap;
use vstd::contrib::exec_spec::ExecSpecEq;
#[cfg(not(verus_keep_ghost))]
use vstd::prelude::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
#[path = "state.rs"]
pub mod operation_io;

verus! {

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
