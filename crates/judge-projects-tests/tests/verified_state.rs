#[cfg(verus_keep_ghost)]
#[path = "proof_support/judge-projects/support/host.rs"]
mod project_host;

#[cfg(verus_keep_ghost)]
#[path = "proof_support/judge-projects/execution.rs"]
mod scheduler;

#[path = "../../judge-projects/src/verified_state.rs"]
mod state;

#[cfg(verus_keep_ghost)]
use state::{execute_query, plan_trace};
#[cfg(not(verus_keep_ghost))]
use chrono_judge_projects::execute_query;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use vstd::contrib::exec_spec::ExecSpecEq;

#[cfg(verus_keep_ghost)]
#[path = "proof_support/judge-routes/support/tool.rs"]
mod compiler_fixture;

#[path = "../examples/release_observation.rs"]
mod release_observation;

#[cfg(verus_keep_ghost)]
#[path = "impact_summary.rs"]
mod impact_summary;

verus! {

#[cfg(verus_keep_ghost)]
fn streams_cover_only_the_announced_bytes(stdout: usize, stderr: usize, actual: usize) {
    let bound = state::commands::stream_boundary(stdout, stderr, actual);
    proof {
        if stdout > actual || stderr as int != actual as int - stdout as int { assert(bound.is_none()); }
        else { assert(bound == Some(stdout)); }
    }
    let empty = state::commands::stream_boundary(0, 0, 0);
    assert(empty == Some(0usize));
    let overflow = state::commands::stream_boundary(usize::MAX, 1, 0);
    assert(overflow.is_none());

}


#[cfg(verus_keep_ghost)]
fn receipt_preserves_each_wide_timeout() {
    let absent = state::receipt_timeout::exact_observation_timeout(None);
    let small = state::receipt_timeout::exact_observation_timeout(Some(9007199254740991));
    let first = state::receipt_timeout::exact_observation_timeout(Some(9007199254740992));
    let last = state::receipt_timeout::exact_observation_timeout(Some(u64::MAX));
    assert(absent.is_none() && small.is_none());
    assert(first == Some(9007199254740992u64) && last == Some(u64::MAX));
}


#[cfg_attr(not(verus_keep_ghost), test)]
fn release_accepts_the_expected_observations_only() {
    let accepted = release_observation::accepts(2, 4);
    assert(accepted);
    let refused_1 = release_observation::accepts(0, 4);
    assert(!refused_1);
    let refused_2 = release_observation::accepts(2, 0);
    assert(!refused_2);
}


#[cfg(verus_keep_ghost)]
fn compiler_observation_keeps_the_method_and_the_runner_result(
    c: &state::compiler::OutputContract, argv: &[String], failure: &String, limit: usize,
) {
    use state::compiler::{Observation, observe_method};
    let ordinary = observe_method(None, argv, -1, Some(failure), limit, 41u8,
        |_name: &'static str, _r: Observation| -> (out: Result<u8, i32>)
            requires false, { Err(-1) });
    assert(ordinary == Ok::<u8,i32>(41));

    let ok = observe_method(Some(c), argv, 0, None, limit, 41u8,
        |name: &'static str, r: Observation| -> (out: Result<u8, i32>)
            requires name@ == "compiler-output-v1"@ && r.operation@ == "observe"@
                && r.contract == c && r.argv == argv && r.exit == 0
                && !r.process_failed && r.limit == limit,
            ensures out == Ok::<u8,i32>(12), { Ok(12) });
    assert(ok == Ok::<u8,i32>(12));

    let failed = observe_method(Some(c), argv, -9, Some(failure), limit, 41u8,
        |name: &'static str, r: Observation| -> (out: Result<u8, i32>)
            requires name@ == "compiler-output-v1"@ && r.operation@ == "observe"@
                && r.contract == c && r.argv == argv && r.exit == -9
                && r.process_failed && r.limit == limit,
            ensures out == Err::<u8,i32>((-77) as i32), { Err(-77) });
    assert(failed == Err::<u8,i32>((-77) as i32));
}

#[cfg(verus_keep_ghost)]
fn ancestor_runs_in_either_direction<'a, 'b, A: state::path_components::Components<'a>, B: state::path_components::Components<'b>>(first: A, second: B)
    requires first.rest().len() < second.rest().len(), first.rest() == second.rest().take(first.rest().len() as int),
{
    let nested = state::path_components::component_overlap(second, first);
    assert(nested);
}

#[cfg(verus_keep_ghost)]
fn sibling_components_do_not_conflict<'a, 'b, A: state::path_components::Components<'a>, B: state::path_components::Components<'b>>(first: A, second: B, different: usize)
    requires different < first.rest().len(), different < second.rest().len(),
        first.rest()[different as int] != second.rest()[different as int],
{
    let nested = state::path_components::component_overlap(first, second);
    assert(!nested);
}

#[cfg(verus_keep_ghost)]
fn nonfirst_output_pair_holds_worker<M: state::operation_claims::Conflict>(
    left: &state::operation_claims::Claims, right: &state::operation_claims::Claims, paths: &M,
    i: usize, j: usize,
)
    requires i < left.outputs.len(), j < right.outputs.len(),
        paths.related(&left.outputs@[i as int], &right.outputs@[j as int]),
{
    let held = left.overlaps(right, paths);
    assert(held);
    let ready = state::project_dispatch::can_dispatch(1,2,|| -> (v: bool) ensures !v { false },|| -> (v: bool) ensures v == held { held });
    assert(!ready);
}
#[cfg(verus_keep_ghost)]
fn collection_preserves_known_paths_on_rejection<M: state::operation_claims::Conflict>(
    mut known: std::collections::BTreeSet<String>, retained: &String, new_report: &String, paths: &M,
)
    requires vstd::laws_cmp::obeys_cmp::<String>(), known@.contains(*retained),
        paths.related(retained, new_report),
{
    let ghost initial = known@;
    let accepted = state::operation_claims::reserve_report(&mut known,new_report,paths);
    assert(!accepted && known@ == initial);
}
#[cfg(verus_keep_ghost)]
fn collection_adds_a_disjoint_report<M: state::operation_claims::Conflict>(
    mut known: std::collections::BTreeSet<String>, new_report: &String, paths: &M,
)
    requires vstd::laws_cmp::obeys_cmp::<String>(), !known@.contains(*new_report),
        forall|p:String| known@.contains(p) ==> !#[trigger] paths.related(&p,new_report),
{
    let ghost initial = known@;
    let accepted = state::operation_claims::reserve_report(&mut known,new_report,paths);
    assert(accepted && known@ == initial.insert(*new_report));
}

#[cfg(verus_keep_ghost)]
fn first_failed_trace_write_suppresses_every_later_write(original: u32) {
    let mut first = None;
    plan_trace::publish_frame(&mut first,
        || -> (r: Option<u32>) ensures r.is_none() { None });
    assert(first.is_none());
    plan_trace::publish_frame(&mut first,
        || -> (r: Option<u32>) ensures r == Some(original) { Some(original) });
    assert(first == Some(original));
    plan_trace::publish_frame(&mut first,
        || -> Option<u32> requires false { None });
    assert(first == Some(original));
}

fn observed_reply(value: u8, diagnostic: Option<String>) -> (out: Result<(), String>)
    ensures match diagnostic {
        Some(original) => out == Err::<(), String>(original),
        None => if value == 7 { out.is_ok() } else { out matches Err(e) && e@ == "bad result"@ },
    },
{
    match diagnostic {
        Some(original) => Err(original),
        None => if value == 7 { Ok(()) } else { Err("bad result".to_string()) },
    }
}

#[cfg_attr(not(verus_keep_ghost), test)]
fn query_keeps_execution_publication_and_error_sink_outcomes() {
    let matched = execute_query::admit_query_location(true, true);
    let other_root = execute_query::admit_query_location(false, true);
    let relative = execute_query::admit_query_location(true, false);
    assert(matched.is_ok() && other_root.is_err() && relative.is_err());

    let ok = execute_query::publish_plan(Ok(7u8), None, observed_reply);
    let diagnostic = execute_query::publish_plan(Ok(7u8), Some("trace".to_string()), observed_reply);
    let work = execute_query::publish_plan(Err("work".to_string()), Some("trace".to_string()), observed_reply);
    assert(ok.is_ok());
    assert(diagnostic matches Err(e) && e@ == "trace"@);
    assert(work matches Err(e) && e@ == "work"@);

    let done = state::query_exit(Ok(()), |_e: String| false);
    let reported = state::query_exit(Err("work".to_string()), |_e: String| true);
    let broken_pipe = state::query_exit(Err("work".to_string()), |_e: String| false);
    assert(done == 0 && reported == 2 && broken_pipe == 2);
}

#[cfg_attr(not(verus_keep_ghost), test)]
fn dispatch_admission_checks_the_entire_index_order() {
    let empty = state::admit_dispatch_order(&[], 0);
    let reordered = state::admit_dispatch_order(&[2, 0, 1], 3);
    let short = state::admit_dispatch_order(&[1, 0], 3);
    let repeated = state::admit_dispatch_order(&[0, 1, 0], 3);
    let past_end = state::admit_dispatch_order(&[0, 2], 2);
    assert(empty.is_ok());
    assert(reordered.is_ok());
    assert(short.is_err());
    assert(repeated.is_err());
    assert(past_end.is_err());
}

fn retirement_obligations_keep_the_order_and_original_target()
    requires vstd::laws_cmp::obeys_cmp::<String>(),
{
    broadcast use vstd::std_specs::btree::group_btree_axioms;
    proof { reveal_strlit("passed"); reveal_strlit("failed"); assert("passed"@[0] != "failed"@[0]); }
    let original = "test:old".to_string();
    let replacement = Some("test:new".to_string());
    let explicit_none: Option<String> = None;
    let admitted = state::declared_removal(Some(&replacement), false);
    let missing = state::declared_removal(None, true);
    let no_validator = state::declared_removal(Some(&explicit_none), false);
    let deferred = state::declared_removal(Some(&explicit_none), true);
    assert(admitted == Some(&replacement) && missing.is_none() && no_validator.is_none() && deferred == Some(&explicit_none));

    let passed = "passed".to_string();
    let failed = "failed".to_string();
    let local = state::replacement_covered(Some(&passed), false);
    let peer = state::replacement_covered(None, true);
    let absent = state::replacement_covered(None, false);
    let unsuccessful = state::replacement_covered(Some(&failed), false);
    assert(local && peer && !absent && !unsuccessful);

    let mut targets = std::collections::BTreeMap::new();
    let mut sources = std::collections::BTreeMap::new();
    let first = state::record_removal(&mut targets, &mut sources, &original, &replacement, "example");
    let same = state::record_removal(&mut targets, &mut sources, &original, &replacement, "harness");
    let wrong = state::record_removal(&mut targets, &mut sources, &original, &explicit_none, "wrong");
    let global = state::record_removal(&mut targets, &mut sources, &original, &replacement, "global-obligation");
    assert(first && same && !wrong && global);
    assert(sources@[original]@.len() == 3);
    assert(sources@[original]@[0]@ == "example"@ && sources@[original]@[1]@ == "harness"@
        && sources@[original]@[2]@ == "global-obligation"@);
    assert(state::same_target(targets@[original], replacement));
}

fn execution_row(status: &str) -> (row: state::OperationRow<(), ()>)
    ensures row.status@ == status@,
{
    state::OperationRow { operation: String::new(), status: status.to_string(), receipt: None, error: None, original: None }
}

fn unit_test_results_require_exact_ownership_and_success()
    requires vstd::laws_cmp::obeys_cmp::<String>(),
{
    broadcast use vstd::std_specs::btree::group_btree_axioms;
    let mut owned = std::collections::BTreeSet::new();
    let mut tests = std::collections::BTreeMap::new();
    let first = "first".to_string();
    let other = "second".to_string();
    proof {
        reveal_strlit("first"); reveal_strlit("second");
        reveal_strlit("passed"); reveal_strlit("failed");
        assert(first@.len() != other@.len());
        assert("passed"@[0] != "failed"@[0]);
    }
    let empty = state::unit_test_results_complete(&owned, &tests);
    assert(empty);
    owned.insert(first.clone());
    let missing = state::unit_test_results_complete(&owned, &tests);
    assert(!missing);
    tests.insert(other.clone(), "passed".to_string());
    assert(owned@.contains(first) && !tests@.contains_key(first));
    let wrong_key = state::unit_test_results_complete(&owned, &tests);
    assert(!wrong_key);
    tests.insert(first.clone(), "passed".to_string());
    assert(tests@.contains_key(other) && !owned@.contains(other));
    let extra = state::unit_test_results_complete(&owned, &tests);
    assert(!extra);
    owned.insert(other.clone());
    assert(tests@.dom() =~= owned@);
    assert forall|id: String| owned@.contains(id) implies state::selected_test_passed(tests@, id) by {
        assert(id == first || id == other);
    }
    let complete = state::unit_test_results_complete(&owned, &tests);
    assert(complete);
    tests.insert(other.clone(), "failed".to_string());
    assert(owned@.contains(other) && !state::selected_test_passed(tests@, other));
    let failed = state::unit_test_results_complete(&owned, &tests);
    assert(!failed);
}

fn whole_report_distinguishes_blocked_failed_error_and_unselected_tests()
    requires vstd::laws_cmp::obeys_cmp::<String>(),
{
    broadcast use vstd::std_specs::btree::group_btree_axioms;
    proof {
        reveal_strlit("passed"); reveal_strlit("failed"); reveal_strlit("error"); reveal_strlit("passed ");
        assert("failed"@[0] != "passed"@[0]); assert("failed"@[0] != "error"@[0]);
        assert("passed "@.len() != "passed"@.len()); assert("passed"@[0] != "error"@[0]);
    }
    let empty: [state::OperationRow<(), ()>; 0] = [];
    let mut tests = std::collections::BTreeMap::new();
    let mut selected = Vec::new();
    let ok = state::evidence_query::report_passed(&empty, 0, &selected, &tests);
    let blocked = state::evidence_query::report_passed(&empty, 1, &selected, &tests);
    let no_errors = state::has_execution_error(&empty);
    assert(ok && !blocked && !no_errors);

    let passed = [execution_row("passed")];
    let failed = [execution_row("failed")];
    let typo = [execution_row("passed ")];
    let late_error = [execution_row("failed"), execution_row("error")];
    let normal = state::evidence_query::report_passed(&passed, 0, &selected, &tests);
    let rejected = state::evidence_query::report_passed(&failed, 0, &selected, &tests);
    let nonstandard = state::evidence_query::report_passed(&typo, 0, &selected, &tests);
    let ordinary_failure = state::has_execution_error(&failed);
    let is_error = state::has_execution_error(&late_error);
    assert(normal && !rejected && !nonstandard && !ordinary_failure && is_error);

    let key = "test:actual".to_string();
    selected.push(key.clone());
    let missing = state::evidence_query::report_passed(&passed, 0, &selected, &tests);
    assert(selected@[0] == key);
    assert(!state::selected_test_passed(tests@, selected@[0]));
    assert(!missing);
    tests.insert(key.clone(), "passed".to_string());
    let covered = state::evidence_query::report_passed(&passed, 0, &selected, &tests);
    assert(covered);
    let other = "unexpected:test".to_string();
    proof { reveal_strlit("test:actual"); reveal_strlit("unexpected:test"); assert(key@.len() != other@.len()); }
    let failure = "failed".to_string();
    tests.insert(other.clone(), failure.clone());
    broadcast use vstd::map_lib::group_map_properties;
    assert(tests@.dom().contains(other));
    assert(tests@[other] == failure);
    assert(tests@.values().contains(failure));
    assert(!state::all_test_statuses_passed(tests@));
    let extra_failed = state::evidence_query::report_passed(&passed, 0, &selected, &tests);
    assert(!extra_failed);
}

fn selected_outcome_covers_only_the_selected_ids()
    requires vstd::laws_cmp::obeys_cmp::<String>(),
{
    broadcast use vstd::std_specs::btree::group_btree_axioms;
    let mut selected = Vec::new();
    let mut results = std::collections::BTreeMap::new();
    let key = "test:selected".to_string();
    let other = "test:extra".to_string();
    proof {
        reveal_strlit("test:selected"); reveal_strlit("test:extra");
        reveal_strlit("passed"); reveal_strlit("passed "); reveal_strlit("failed");
        assert(key@.len() != other@.len()); assert(key != other);
        assert("passed"@.len() != "passed "@.len());
        assert("passed"@[0] != "failed"@[0]);
    }
    results.insert(other.clone(), "failed".to_string());
    let empty = state::uncovered_test(&selected, &results);
    assert(empty.is_none());
    selected.push(key.clone());
    assert(selected@ =~= seq![key]);
    assert(!results@.contains_key(key));
    let missing = state::uncovered_test(&selected, &results);
    if missing.is_none() { assert(selected@[0] == key); }
    assert(missing == Some(&key));
    results.insert(key.clone(), "passed ".to_string());
    let suffix = state::uncovered_test(&selected, &results);
    assert(suffix == Some(&key));
    results.insert(key.clone(), "passed".to_string());
    let complete = state::uncovered_test(&selected, &results);
    assert(complete.is_none());
    selected.push(other.clone());
    assert(selected@ =~= seq![key, other]);
    assert(state::selected_test_passed(results@, key));
    assert(!state::selected_test_passed(results@, other));
    let failed = state::uncovered_test(&selected, &results);
    if failed.is_none() { assert(selected@[1] == other); }
    assert(failed == Some(&other));
}

#[cfg_attr(not(verus_keep_ghost), test)]
fn operation_diagnostic_requires_an_original_coverage_message() {
    proof {
        reveal_strlit("E_VERUS_COVERAGE"); reveal_strlit("test output");
        assert("E_VERUS_COVERAGE"@.len() != "test output"@.len());
    }
    let original = state::report_coverage_cause(true, "E_VERUS_COVERAGE", 1);
    let truncated = state::report_coverage_cause(false, "E_VERUS_COVERAGE", 1);
    let unmarked = state::report_coverage_cause(true, "test output", 1);
    let empty = state::report_coverage_cause(true, "E_VERUS_COVERAGE", 0);
    let largest = state::report_coverage_cause(true, "E_VERUS_COVERAGE", 1024);
    let oversized = state::report_coverage_cause(true, "E_VERUS_COVERAGE", 1025);
    assert(original && !truncated && !unmarked && !empty && largest && !oversized);
}

#[cfg(verus_keep_ghost)]
fn successful_execution_may_still_need_its_trace() {
    let incomplete_trace = scheduler::failure_batch::keep_scheduler_diagnostics(true, false);
    let failed_execution = scheduler::failure_batch::keep_scheduler_diagnostics(false, true);
    let complete = scheduler::failure_batch::keep_scheduler_diagnostics(true, true);
    assert(incomplete_trace && failed_execution && !complete);
    let passed = project_host::failed_command(false, Some(7u8));
    let failed = project_host::failed_command(true, Some(7u8));
    let missing = project_host::failed_command::<u8>(true, None);
    assert(passed.is_none() && failed == Some(7u8) && missing.is_none());
}


#[cfg(verus_keep_ghost)]
fn a_mismatch_between_the_two_compiler_destinations_is_rejected(count: usize, has_flag: bool) {
    let accepted = compiler_fixture::accepts_output(count, has_flag, false);
    assert(!accepted);
}

#[cfg(verus_keep_ghost)]
fn another_operations_compiler_output_cannot_be_claimed(flat: bool, canonical: bool) {
    let owned = state::operation_io::owned_compiler_output(false, flat, canonical);
    assert(!owned);
}

#[cfg_attr(not(verus_keep_ghost), test)]
fn compiler_release_needs_success_join_and_operation_ownership() {
    proof {
        reveal_strlit("passed"); reveal_strlit("error");
        assert("passed"@.len() != "error"@.len());
    }
    let completed = state::can_release_compiler_files("passed", true, true);
    let failed = state::can_release_compiler_files("error", true, true);
    let incomplete = state::can_release_compiler_files("passed", false, true);
    let external = state::can_release_compiler_files("passed", true, false);
    assert(completed && !failed && !incomplete && !external);
}

#[cfg(verus_keep_ghost)]
fn any_terminal_process_is_known_without_a_status_success_claim(status: &str) {
    let row = state::OperationObservation { status, process_terminal: Some(true) };
    let known = state::terminal(&row);
    assert(known);
}

#[cfg(verus_keep_ghost)]
fn any_other_status_needs_a_terminal_process(status: &str)
    requires status@ != "blocked"@,
{
    let absent = state::OperationObservation { status, process_terminal: None };
    let unknown = state::OperationObservation { status, process_terminal: Some(false) };
    let absent_known = state::terminal(&absent);
    let unknown_known = state::terminal(&unknown);
    assert(!absent_known && !unknown_known);
}

#[cfg_attr(not(verus_keep_ghost), test)]
fn blocked_is_terminal_without_a_process_and_unknown_receipts_stay_unknown() {
    proof {
        reveal_strlit("blocked"); reveal_strlit("passed");
        assert("blocked"@.len() != "passed"@.len());
    }
    let blocked = state::OperationObservation { status: "blocked", process_terminal: None };
    let blocked_known = state::terminal(&blocked);
    assert(blocked_known);
    let completed = state::operation_state(&blocked);
    let exact_completed = <&str>::exec_eq(completed, "completed");
    assert(exact_completed);
    let claimed_success = state::OperationObservation { status: "passed", process_terminal: None };
    let no_receipt = state::terminal(&claimed_success);
    assert(!no_receipt);
    let returned_unknown = state::OperationObservation { status: "passed", process_terminal: Some(false) };
    let unknown = state::operation_state(&returned_unknown);
    let exact_unknown = <&str>::exec_eq(unknown, "unknown");
    assert(exact_unknown);
}

#[cfg_attr(not(verus_keep_ghost), test)]
fn status_identity_preserves_case_suffix_nul_and_unicode() {
    proof {
        reveal_strlit("blocked"); reveal_strlit("Blocked"); reveal_strlit("blocked\0");
        reveal_strlit("blocked "); reveal_strlit("阻断");
        assert("blocked"@[0] != "Blocked"@[0]);
        assert("blocked"@.len() != "blocked\0"@.len());
        assert("blocked"@.len() != "blocked "@.len());
        assert("blocked"@.len() != "阻断"@.len());
    }
    let case = state::terminal(&state::OperationObservation { status: "Blocked", process_terminal: None });
    assert(!case);
    let nul = state::terminal(&state::OperationObservation { status: "blocked\0", process_terminal: None });
    assert(!nul);
    let suffix = state::terminal(&state::OperationObservation { status: "blocked ", process_terminal: None });
    assert(!suffix);
    let unicode = state::terminal(&state::OperationObservation { status: "阻断", process_terminal: None });
    assert(!unicode);
    let process = state::terminal(&state::OperationObservation { status: "阻断", process_terminal: Some(true) });
    assert(process);
}

#[cfg_attr(not(verus_keep_ghost), test)]
fn complete_execution_needs_every_operation_and_accepts_the_empty_execution() {
    proof {
        reveal_strlit("blocked"); reveal_strlit("error");
        assert("blocked"@.len() != "error"@.len());
    }
    let empty = Vec::new();
    let empty_known = state::all_terminal(&empty);
    assert(empty_known);
    let mut rows = Vec::new();
    rows.push(state::OperationObservation { status: "blocked", process_terminal: None });
    rows.push(state::OperationObservation { status: "error", process_terminal: Some(true) });
    let returned = state::all_terminal(&rows);
    assert(returned);
    rows.push(state::OperationObservation { status: "error", process_terminal: Some(false) });
    let unresolved_last = state::all_terminal(&rows);
    proof { assert(!state::operation_is_terminal(&rows[2])); }
    assert(!unresolved_last);
    let mut unresolved_first = Vec::new();
    unresolved_first.push(state::OperationObservation { status: "error", process_terminal: None });
    unresolved_first.push(state::OperationObservation { status: "blocked", process_terminal: None });
    let incomplete = state::all_terminal(&unresolved_first);
    proof { assert(!state::operation_is_terminal(&unresolved_first[0])); }
    assert(!incomplete);
}

#[cfg_attr(not(verus_keep_ghost), test)]
fn original_identity_requires_the_complete_digest_and_exact_length() {
    proof {
        reveal_strlit("aé\0"); reveal_strlit("aé"); reveal_strlit("Aé\0");
        assert("aé\0"@.len() != "aé"@.len());
        assert("aé\0"@[0] != "Aé\0"@[0]);
    }
    let same = state::validate_original("aé\0", 7, Some(("aé\0", 7)));
    assert(same.is_ok());
    let length = state::validate_original("aé\0", 8, Some(("aé\0", 7)));
    assert(length.is_err());
    let suffix = state::validate_original("aé", 7, Some(("aé\0", 7)));
    assert(suffix.is_err());
    let case = state::validate_original("Aé\0", 7, Some(("aé\0", 7)));
    assert(case.is_err());
    match case {
        Err(message) => {
            let exact = <&str>::exec_eq(message, "operation original differs from the actual process result");
            assert(exact);
        },
        Ok(()) => { assert(false); },
    }
    let unbound = state::validate_original("aé\0", u64::MAX, None);
    assert(unbound.is_ok());
}

}
