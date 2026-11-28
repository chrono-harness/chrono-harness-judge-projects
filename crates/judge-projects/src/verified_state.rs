//! 执行原件的终态、完整身份和保留决策；实际 IO 由 state 所有者执行。
#![allow(unexpected_cfgs)]
use std::collections::{BTreeMap, BTreeSet};
use vstd::contrib::exec_spec::ExecSpecEq;
#[cfg(not(verus_keep_ghost))]
use vstd::prelude::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
#[path = "commands.rs"]
pub mod commands;
#[cfg(verus_keep_ghost)]
#[path = "evidence_query.rs"]
pub mod evidence_query;
#[cfg(verus_keep_ghost)]
#[path = "execute_query.rs"]
pub mod execute_query;
#[cfg(verus_keep_ghost)]
#[path = "impact.rs"]
pub mod impact;
#[cfg(verus_keep_ghost)]
#[path = "plan_trace.rs"]
pub mod plan_trace;

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

#[cfg(verus_keep_ghost)]
#[path = "main.rs"]
pub mod entrypoint;
#[cfg(verus_keep_ghost)]
#[path = "git_reader.rs"]
pub mod git_reader;
#[cfg(verus_keep_ghost)]
#[path = "pair_checks.rs"]
pub mod pair_checks;
#[cfg(verus_keep_ghost)]
#[path = "registration.rs"]
pub mod registration;
#[cfg(verus_keep_ghost)]
#[path = "runtime_session.rs"]
pub mod runtime_session;

verus! {

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

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Prerequisites { Passed, Waiting, Blocked }

/// Missing predecessors can still complete. Any known unsuccessful predecessor
/// blocks the operation, including when an earlier predecessor is missing.
pub fn prerequisite_status(ids: &BTreeSet<String>, statuses: &BTreeMap<String, String>)
    -> (out: Prerequisites)
    requires vstd::laws_cmp::obeys_cmp::<String>(),
    ensures
        (out == Prerequisites::Blocked) == (exists|id: String| #[trigger] ids@.contains(id)
            && statuses@.contains_key(id) && !selected_test_passed(statuses@, id)),
        (out == Prerequisites::Passed) == (forall|id: String| #[trigger] ids@.contains(id)
            ==> selected_test_passed(statuses@, id)),
{
    broadcast use vstd::std_specs::btree::group_btree_axioms;
    let mut iter = ids.iter();
    let mut missing = false;
    loop
        invariant vstd::laws_cmp::obeys_cmp::<String>(),
            iter@.1.to_set() == ids@, 0 <= iter@.0 <= iter@.1.len(),
            missing == (exists|j: int| 0 <= j < iter@.0 && !statuses@.contains_key(#[trigger] iter@.1[j])),
            forall|j: int| 0 <= j < iter@.0 && statuses@.contains_key(#[trigger] iter@.1[j])
                ==> selected_test_passed(statuses@, iter@.1[j]),
        decreases iter@.1.len() - iter@.0,
    {
        let Some(id) = iter.next() else {
            assert forall|id: String| #[trigger] ids@.contains(id)
                implies (!statuses@.contains_key(id) || selected_test_passed(statuses@, id)) by {
                assert(iter@.1.contains(id));
                let j = choose|j: int| 0 <= j < iter@.1.len() && iter@.1[j] == id;
                assert(iter@.1[j] == id);
            }
            assert(missing == (exists|id: String| #[trigger] ids@.contains(id) && !statuses@.contains_key(id))) by {
                if missing {
                    let j = choose|j: int| 0 <= j < iter@.0 && !statuses@.contains_key(#[trigger] iter@.1[j]);
                    assert(ids@.contains(iter@.1[j]));
                } else {
                    assert forall|id: String| #[trigger] ids@.contains(id) implies statuses@.contains_key(id) by {
                        assert(iter@.1.contains(id));
                        let j = choose|j: int| 0 <= j < iter@.1.len() && iter@.1[j] == id;
                        assert(statuses@.contains_key(iter@.1[j]));
                    }
                }
            }
            return if missing { Prerequisites::Waiting } else { Prerequisites::Passed };
        };
        assert(iter@.1[iter@.0 - 1] == *id);
        match statuses.get(id) {
            None => { missing = true; },
            Some(s) => {
                if !<&str>::exec_eq(s.as_str(), "passed") {
                    assert(ids@.contains(*id));
                    return Prerequisites::Blocked;
                }
            },
        }
    }
}

/// Record one test's actual operations, preserving all other selected tests.
pub fn record_executed_test(tests: &mut BTreeMap<String, String>, test: &String,
    operations: &[String], statuses: &BTreeMap<String, String>)
    requires vstd::laws_cmp::obeys_cmp::<String>(),
    ensures tests@.dom() == old(tests)@.dom().insert(*test),
        tests@[*test]@ == if forall|i: int| 0 <= i < operations.len()
            ==> selected_test_passed(statuses@, #[trigger] operations@[i]) { "passed"@ } else { "failed"@ },
        forall|other: String| other != *test && old(tests)@.contains_key(other)
            ==> #[trigger] tests@[other] == old(tests)@[other],
{
    broadcast use vstd::std_specs::btree::group_btree_axioms;
    let status = if uncovered_test(operations, statuses).is_none() { "passed" } else { "failed" };
    tests.insert(test.clone(), status.to_string());
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

/// Routes decodes the JSON field as null, a string, or another value. Identity
/// takes precedence over the contents of a reply for another operation.
pub fn receipt_reply(plan: &str, wanted_plan: &str, op: &str, wanted_op: &str,
    error: Result<Option<String>, ()>) -> (out: Result<(), String>)
    ensures if plan@ != wanted_plan@ || op@ != wanted_op@ {
        out matches Err(s) && s@ == "E_RECEIPT_MISMATCH: routes response refers to another plan or operation"@
    } else {
        match error {
            Ok(None) => out.is_ok(),
            Ok(Some(s)) => out == Err::<(), String>(s),
            Err(()) => out matches Err(s) && s@ == "E_RECEIPT_MISMATCH: invalid receipt comparison"@,
        }
    },
{
    if !<&str>::exec_eq(plan, wanted_plan) || !<&str>::exec_eq(op, wanted_op) {
        return Err("E_RECEIPT_MISMATCH: routes response refers to another plan or operation".to_string());
    }
    match error {
        Ok(None) => Ok(()), Ok(Some(s)) => Err(s),
        Err(()) => Err("E_RECEIPT_MISMATCH: invalid receipt comparison".to_string()),
    }
}

/// Only the OS/Rust UTF-8 and Unicode classification observations come from
/// outside the predicate. The code and byte bound use the existing contract.
pub fn coverage_detail<V, C>(code: &str, bytes: usize, visible: V, control: C) -> (usable: bool)
    where V: FnOnce() -> bool, C: FnOnce() -> bool,
    requires visible.requires(()), control.requires(()),
    ensures if code@ != "E_VERUS_COVERAGE"@ || bytes == 0 || bytes > 1024 { !usable }
        else if usable { visible.ensures((),true) && control.ensures((),false) }
        else { visible.ensures((),false) || (visible.ensures((),true) && control.ensures((),true)) },
{
    report_coverage_cause(true, code, bytes) && visible() && !control()
}

pub open spec fn line_start(bytes: Seq<u8>, i: int) -> bool {
    i == 0 || (0 < i <= bytes.len() && bytes[i-1] == 10)
}

pub open spec fn whole_line(bytes: Seq<u8>, i: int, j: int) -> bool {
    0 <= i <= j <= bytes.len() && line_start(bytes, i)
        && (j == bytes.len() || bytes[j] == 10)
        && forall|k: int| i <= k < j ==> bytes[k] != 10
}

/// Return the first whole qualifying line from a complete byte stream.
/// The adapter interprets each bounded slice once; no line index is allocated.
pub fn first_coverage_line<T, F>(bytes: &[u8], complete: bool, inspect: F) -> (out: Option<T>)
    where F: Fn(usize, usize) -> Option<T>,
    requires forall|i: usize, j: usize| whole_line(bytes@, i as int, j as int)
        ==> #[trigger] inspect.requires((i,j)),
    ensures
        !complete ==> out.is_none(),
        complete ==> match out {
            Some(v) => exists|i: usize, j: usize| whole_line(bytes@, i as int, j as int)
                && #[trigger] inspect.ensures((i,j), Some(v))
                && forall|a: usize,b: usize| a < i && whole_line(bytes@,a as int,b as int)
                    ==> #[trigger] inspect.ensures((a,b), None),
            None => forall|a: usize,b: usize| whole_line(bytes@,a as int,b as int)
                ==> #[trigger] inspect.ensures((a,b), None),
        },
{
    if !complete { return None; }
    let mut start = 0usize;
    let mut end = 0usize;
    loop
        invariant complete, start <= end <= bytes.len(), line_start(bytes@,start as int),
            forall|k: int| start <= k < end ==> bytes@[k] != 10,
            forall|a: usize, b: usize| a < start && whole_line(bytes@,a as int,b as int)
                ==> #[trigger] inspect.ensures((a,b), None),
            forall|i: usize,j: usize| whole_line(bytes@,i as int,j as int)
                ==> #[trigger] inspect.requires((i,j)),
        decreases bytes.len() - end,
    {
        if end == bytes.len() || bytes[end] == 10 {
            assert(whole_line(bytes@,start as int,end as int));
            let observation = inspect(start,end);
            if let Some(value) = observation {
                assert(inspect.ensures((start,end),Some(value)));
                assert(exists|i: usize,j: usize| whole_line(bytes@,i as int,j as int)
                    && #[trigger] inspect.ensures((i,j),Some(value))
                    && forall|a: usize,b: usize| a < i && whole_line(bytes@,a as int,b as int)
                        ==> #[trigger] inspect.ensures((a,b),None));
                return Some(value);
            }
            assert forall|a: usize,b: usize| a <= end && whole_line(bytes@,a as int,b as int)
                implies #[trigger] inspect.ensures((a,b), None) by {
                if a > start { assert(bytes@[a as int - 1] != 10); }
                if a == start {
                    if b < end { assert(bytes@[b as int] != 10); }
                    if b > end { assert(bytes@[end as int] != 10); }
                }
            }
            if end == bytes.len() { return None; }
            start = end + 1;
        }
        end += 1;
    }
}

pub fn preferred_diagnostic<T,F>(stderr: Option<T>, stdout: F) -> (line: Option<T>)
    where F: FnOnce() -> Option<T>,
    requires stdout.requires(()),
    ensures match stderr { Some(s) => line == Some(s), None => stdout.ensures((),line) },
{
    match stderr { Some(s) => Some(s), None => stdout() }
}

/// The original receipt is carried through every comparison and exit branch.
pub fn operation_result<R, O, I, M>(
    id: String, observed: Result<R,String>, inspect: I, exit_message: M,
) -> (row: OperationRow<R, O>)
    where I: FnOnce(&R) -> (Result<(),String>, Option<String>, i32), M: FnOnce(&R,i32) -> String,
    requires forall|r: &R| inspect.requires((r,)),
        forall|r: &R,code: i32| exit_message.requires((r,code)),
    ensures row.operation == id, row.original.is_none(),
        match observed {
            Err(e) => row.receipt.is_none() && row.status@ == "error"@ && row.error == Some(e),
            Ok(r) => row.receipt == Some(r) && exists|o: (Result<(),String>,Option<String>,i32)|
                #[trigger] inspect.ensures((&r,), o) && match (o.0,o.1) {
                    (Err(e),_) | (Ok(()),Some(e)) => row.status@ == "error"@ && row.error == Some(e),
                    (Ok(()),None) => if o.2 == 0 { row.status@ == "passed"@ && row.error.is_none() }
                        else { row.status@ == "failed"@ && (row.error matches Some(e)
                               && exit_message.ensures((&r,o.2), e)) },
                },
        },
{
    let (receipt,error,status) = match observed {
        Err(e) => (None,Some(e),"error"),
        Ok(r) => {
            let (comparison,failure,code) = inspect(&r);
            let (error,status) = match (comparison,failure) {
                (Err(e),_) | (Ok(()),Some(e)) => (Some(e),"error"),
                (Ok(()),None) if code != 0 => (Some(exit_message(&r,code)),"failed"),
                (Ok(()),None) => (None,"passed"),
            };
            (Some(r),error,status)
        },
    };
    OperationRow { operation: id, status: status.to_string(), receipt, error, original: None }
}

/// Formatting an OS error is an adapter operation. The first error and the
/// publication error are passed in that order, with the original receipt intact.
pub fn published_operation<R,O,F>(row: OperationRow<R,O>, original: Result<O,String>, describe: F)
    -> (out: OperationRow<R,O>)
    where F: FnOnce(Option<String>,String) -> String,
    requires forall|old: Option<String>, e: String| describe.requires((old,e)),
    ensures out.operation == row.operation, out.receipt == row.receipt,
        match original {
            Ok(file) => out.original == Some(file) && out.status == row.status && out.error == row.error,
            Err(e) => out.original == row.original && out.status@ == "error"@ && (out.error matches Some(reason)
                && describe.ensures((row.error,e),reason)),
        },
{
    let mut out = row;
    match original {
        Ok(file) => out.original = Some(file),
        Err(e) => {
            out.error = Some(describe(out.error,e));
            out.status = "error".to_string();
        },
    }
    out
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

pub(crate) fn test_statuses_pass(tests: &BTreeMap<String, String>) -> (passed: bool)
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
