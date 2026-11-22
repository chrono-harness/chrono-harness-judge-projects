#[cfg(verus_keep_ghost)]
#[path = "proof_support/judge-projects/support/host.rs"]
mod project_host;

#[cfg(verus_keep_ghost)]
#[path = "proof_support/judge-projects/execution.rs"]
mod scheduler;

#[path = "../../judge-projects/src/verified_state.rs"]
mod state;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
extern crate chrono_identifiers as identifiers;

#[cfg(verus_keep_ghost)]
#[path = "proof_support/judge-routes/support/tool.rs"]
mod compiler_fixture;

verus! {

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
    let exact_completed = identifiers::equal_text(completed, "completed");
    assert(exact_completed);
    let claimed_success = state::OperationObservation { status: "passed", process_terminal: None };
    let no_receipt = state::terminal(&claimed_success);
    assert(!no_receipt);
    let returned_unknown = state::OperationObservation { status: "passed", process_terminal: Some(false) };
    let unknown = state::operation_state(&returned_unknown);
    let exact_unknown = identifiers::equal_text(unknown, "unknown");
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
            let exact = identifiers::equal_text(message, "operation original differs from the actual process result");
            assert(exact);
        },
        Ok(()) => { assert(false); },
    }
    let unbound = state::validate_original("aé\0", u64::MAX, None);
    assert(unbound.is_ok());
}

}
