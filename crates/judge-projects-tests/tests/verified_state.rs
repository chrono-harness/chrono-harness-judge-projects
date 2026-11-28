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
fn registry_pairs_keep_first_match_exclusivity_and_literal_prefix<T: state::pair_checks::RegistryColumns>(
    table: &T, key: &[&str], a: usize, b: usize,
)
    requires a < b < table.height(),
        state::pair_checks::matches_columns(table,a as int,key@),
        state::pair_checks::matches_columns(table,b as int,key@),
        forall|i:int| 0 <= i < a ==> !#[trigger] state::pair_checks::matches_columns(table,i,key@),
{
    let first = state::pair_checks::lookup_row(table,key,false);
    let unique = state::pair_checks::lookup_row(table,key,true);
    assert(first == Some(a));
    assert(unique.is_none());
    let exact = state::pair_checks::path_prefix(&[97,98], &[97,98]);
    let nested = state::pair_checks::path_prefix(&[97,98,99], &[97,98]);
    let reversed = state::pair_checks::path_prefix(&[97], &[97,98]);
    let other = state::pair_checks::path_prefix(&[97,99], &[97,98]);
    assert(exact && nested && !reversed && !other);
}

#[cfg(verus_keep_ghost)]
fn absent_and_unique_registry_rows<T: state::pair_checks::RegistryColumns>(table: &T, key: &[&str], row: usize)
    requires row < table.height(), state::pair_checks::matches_columns(table,row as int,key@),
        forall|i:int| 0 <= i < table.height() && i != row ==> !#[trigger] state::pair_checks::matches_columns(table,i,key@),
{
    let unique = state::pair_checks::lookup_row(table,key,true);
    assert(unique == Some(row));
    let project = state::pair_checks::owner_key("project","x");
    let script = state::pair_checks::owner_key("script","x");
    proof { reveal_strlit("project"); reveal_strlit("script"); reveal_strlit(":"); reveal_strlit("x"); }
    assert(project@.len() == 9 && script@.len() == 8);
}

#[cfg(verus_keep_ghost)]
fn collector_binds_manifest_header_pins_sources_and_unit_plan(valid: &str, other: &str)
    requires valid@ != other@,
{
    use state::project_dispatch::*;
    let full = collection_manifest("chrono-full-collection/v1");
    let ci = collection_manifest("chrono-ci-collection/v1");
    let both = executable_pins(Some(valid),Some(valid),valid,Some(valid));
    let absent = executable_pins(None,None,valid,None);
    let no_judge = executable_pins(None,Some(valid),valid,None);
    let wrong_runner = executable_pins(Some(other),None,valid,None);
    let wrong_judge = executable_pins(None,Some(other),valid,Some(valid));
    assert(full && ci && both && absent && !no_judge && !wrong_runner && !wrong_judge);
    let fields = [Some(valid),Some(valid),Some(valid),Some(valid),Some(valid)];
    let header = report_identity(fields,UnitIdentity {base:valid,candidate:valid,tree:valid,registry:valid,context:valid});
    let wrong_tree = report_identity(fields,UnitIdentity {base:valid,candidate:valid,tree:other,registry:valid,context:valid});
    let missing = source_bound(Some(valid),None,Some(valid),valid,valid,valid);
    let wrong_source = source_bound(Some(valid),Some(valid),Some(other),valid,valid,valid);
    let source = source_bound(Some(valid),Some(valid),Some(valid),valid,valid,valid);
    assert(header && !wrong_tree && !missing && !wrong_source && source);
    let observed = tool_input(true,Some(valid),|| -> (r:Option<&str>) ensures r == Some(valid) { Some(valid) },valid);
    let bad_file = tool_input(true,Some(valid),|| -> (r:Option<&str>) ensures r == Some(other) { Some(other) },valid);
    let bad_declaration = tool_input(true,Some(other),|| -> (r:Option<&str>) ensures r == Some(valid) { Some(valid) },valid);
    assert(observed && !bad_file && !bad_declaration);
    proof { reveal_strlit("unit:"); reveal_strlit("u"); reveal_strlit("unit:u"); assert("unit:u"@ =~= "unit:"@ + "u"@); }
    let unit = unit_plan_receipt(valid,valid,Some("unit:u"),"u",false,0,2,2);
    let stale = unit_plan_receipt(valid,other,Some("unit:u"),"u",false,0,2,2);
    let partial = unit_plan_receipt(valid,valid,Some("unit:u"),"u",false,0,1,2);
    assert(unit && !stale && !partial);
}

#[cfg(verus_keep_ghost)]
fn only_one_successful_operation_can_supply_a_collection_receipt(id: &str) {
    let a = state::OperationRow {operation:id.to_string(),status:"passed".to_string(),
        receipt:Some(7u8),error:None,original:None::<u8>};
    let b = state::OperationRow {operation:id.to_string(),status:"passed".to_string(),
        receipt:Some(8u8),error:None,original:None::<u8>};
    let one = [a];
    let accepted = state::operation_receipt(&one,id,Some(true));
    let missing_route = state::operation_receipt(&one,id,None);
    assert(one@.len() == 1 && one@[0].operation@ == id@ && one@[0].status@ == "passed"@ && one@[0].receipt == Some(7u8) && one@[0].error.is_none());
    assert(accepted matches Some(v) && *v == 7u8);
    assert(missing_route.is_none());
    let a2 = state::OperationRow {operation:id.to_string(),status:"passed".to_string(),
        receipt:Some(7u8),error:None,original:None::<u8>};
    let two = [a2,b];
    let ambiguous = state::operation_receipt(&two,id,Some(true));
    assert(two@.len() == 2 && two@[0].operation@ == id@ && two@[1].operation@ == id@);
    proof { if let Some(r) = ambiguous {
        let i = choose|i:int| 0 <= i < two.len() && #[trigger] two@[i].operation@ == id@ && two@[i].status@ == "passed"@
            && two@[i].error.is_none() && two@[i].receipt == Some(*r)
            && (forall|j:int| 0 <= j < two.len() && j != i ==> #[trigger] two@[j].operation@ != id@);
        if i == 0 { assert(two@[1].operation@ == id@); } else { assert(two@[0].operation@ == id@); }
    } }
    assert(ambiguous.is_none());
}

#[cfg(verus_keep_ghost)]
fn native_query_names_match_only_with_their_complete_argument_count() {
    proof {
        reveal_strlit("--protocol");
        reveal_strlit("--version");
        reveal_strlit("check-collection-v1");
        reveal_strlit("check-pairs-v1");
        reveal_strlit("chrono-judge/v1");
        reveal_strlit("evaluate-projects-v1");
        reveal_strlit("execute-plan-v1");
        reveal_strlit("extra");
        reveal_strlit("read-results-v1");
        assert("--version"@.len() == 9);
        assert("evaluate-projects-v1"@.len() == 20);
        assert("execute-plan-v1"@.len() == 15);
        assert("check-pairs-v1"@.len() == 14);
        assert("read-results-v1"@.len() == 15);
        assert("check-collection-v1"@.len() == 19);
        assert("--protocol"@.len() == 10);
        assert("chrono-judge/v1"@.len() == 15);
        assert("extra"@.len() == 5);
        assert("execute-plan-v1"@[0] != "read-results-v1"@[0]);
        assert("execute-plan-v1"@[0] != "chrono-judge/v1"@[0]);
        assert("read-results-v1"@[0] != "chrono-judge/v1"@[0]);
    }

    use state::entrypoint::{Entry, entry};
    let observed = entry(0, None, None);
    assert(observed == Entry::Usage);
    let observed = entry(1, Some("--version"), None);
    assert(observed == Entry::Version);
    let observed = entry(1, Some("evaluate-projects-v1"), None);
    assert(observed == Entry::Evaluate);
    let observed = entry(1, Some("execute-plan-v1"), None);
    assert(observed == Entry::Execute);
    let observed = entry(1, Some("check-pairs-v1"), None);
    assert(observed == Entry::Pairs);
    let observed = entry(1, Some("read-results-v1"), None);
    assert(observed == Entry::Results);
    let observed = entry(1, Some("check-collection-v1"), None);
    assert(observed == Entry::Collection);
    let observed = entry(2, Some("--protocol"), Some("chrono-judge/v1"));
    assert(observed == Entry::Protocol);
    let observed = entry(3, Some("--protocol"), Some("chrono-judge/v1"));
    assert(observed == Entry::Usage);
    let observed = entry(2, Some("--version"), Some("extra"));
    assert(observed == Entry::Usage);
    let observed = entry(2, Some("--protocol"), None);
    assert(observed == Entry::Usage);
}

#[cfg(verus_keep_ghost)]
fn native_git_reader_preserves_original_identity_and_session_outcomes() {
    proof {
        reveal_strlit("E_TOOL_BINDING: runner executable changed");
        reveal_strlit("different");
        reveal_strlit("read");
        reveal_strlit("session");
        reveal_strlit("wanted");
        assert("wanted"@.len() == 6);
        assert("different"@.len() == 9);
    }

    let open = || -> (r: Result<u8, String>) ensures r == Ok::<u8, String>(41), {Ok(41)};
    let forbidden = || -> (r: Result<u8, String>) requires false, { Ok(0) };
    let prior = state::git_reader::open_bound_reader(Err("read".to_string()), "wanted", forbidden);
    assert(prior matches Err(e) && e@ == "read"@);
    let changed = state::git_reader::open_bound_reader(Ok("different".to_string()), "wanted", forbidden);
    assert(changed matches Err(e) && e@ == "E_TOOL_BINDING: runner executable changed"@);
    let ok = state::git_reader::open_bound_reader(Ok("wanted".to_string()), "wanted", open);
    assert(ok == Ok::<u8, String>(41));
    let failed = || -> (r: Result<u8, String>) ensures r matches Err(e) && e@ == "session"@, { Err("session".to_string()) };
    let r = state::git_reader::open_bound_reader(Ok("wanted".to_string()), "wanted", failed);
    assert(r matches Err(e) && e@ == "session"@);
}

#[cfg(verus_keep_ghost)]
fn framed_runtime_receipts_preserve_wire_and_application_errors() {
    broadcast use vstd::array::group_array_axioms;
    let decoder = |_v: &[u8]| -> (r: Result<Result<u8, String>, String>) requires false, { Ok(Ok(0)) };
    let short = state::runtime_session::runner_reply(&[65u8], decoder);
    assert(short matches Err(e) && e@ == "E_PROTOCOL: incomplete runner response"@);
    let empty = state::runtime_session::runner_reply(&[], decoder);
    assert(empty matches Err(e) && e@ == "E_PROTOCOL: incomplete runner response"@);
    let original = |v: &[u8]| -> (r: Result<Result<u8, String>, String>) ensures
      (v@.len() == 2 && v@[0] == 65 && v@[1] == 10) ==> r == Ok::<_, String>(Ok::<u8, String>(7)),
    { Ok(Ok(7)) };
    let observed = state::runtime_session::runner_reply(&[65u8, 10], original);
    assert(observed == Ok::<u8, String>(7));
    let wire = |_v: &[u8]| -> (r: Result<Result<u8, String>, String>) ensures r matches Err(e) && e@ == "decode"@, {Err("decode".to_string())};
    let invalid = state::runtime_session::runner_reply(&[10u8], wire);
    assert(invalid matches Err(e) && e@ == "decode"@);
    let app = |_v: &[u8]| -> (r: Result<Result<u8, String>, String>) ensures r matches Ok(Err(e)) && e@ == "remote"@, {Ok(Err("remote".to_string()))};
    let failed = state::runtime_session::runner_reply(&[10u8], app);
    assert(failed matches Err(e) && e@ == "remote"@);
}

#[cfg(verus_keep_ghost)]
fn registration_view_prioritizes_identity_then_observations_and_consumes_the_remaining_reply() {
    let no_observation = |_r: u8| -> (o: (u8, Result<(), String>)) requires false, { (0, Ok(())) };
    let no_consumption = |_r: u8| -> (o: Result<u8, String>) requires false, { Ok(0) };
    let record = |r: u8| -> (o: (u8, Result<(), String>)) ensures o.0 == r && (o.1 matches Err(e) && e@ == "binding"@), {(r, Err("binding".to_string()))};
    let take = |r: u8| -> (o: Result<u8, String>) ensures o == Ok::<u8, String>(r), {Ok(r)};
    let a = state::registration::admit_project_view(8u8, false, true, no_observation, no_consumption);
    assert(a matches Err(e) && e@ == "E_PROTOCOL: registration project views identity"@);
    let b = state::registration::admit_project_view(8u8, true, false, no_observation, no_consumption);
    assert(b matches Err(e) && e@ == "E_PROTOCOL: registration project views identity"@);
    let c = state::registration::admit_project_view(8u8, true, true, record, no_consumption);
    assert(c matches Err(e) && e@ == "binding"@);
    let updated = |_r: u8| -> (o: (u8, Result<(), String>)) ensures o == (31u8, Ok::<(), String>(())), {(31, Ok(()))};
    let observed = state::registration::admit_project_view(8u8, true, true, updated, take);
    assert(observed == Ok::<u8, String>(31));
    let reject = |_r: u8| -> (o: Result<u8, String>) ensures o matches Err(e) && e@ == "view"@, {Err("view".to_string())};
    let e = state::registration::admit_project_view(8u8, true, true, updated, reject);
    assert(e matches Err(msg) && msg@ == "view"@);
}

#[cfg(verus_keep_ghost)]
fn reciprocal_pair_lookup_chooses_the_forward_link_and_preserves_both_row_identities() {
    proof {
        reveal_strlit("missing");
        reveal_strlit("other");
        reveal_strlit("test");
        assert("test"@.len() == 4);
        assert("missing"@.len() == 7);
        assert("other"@.len() == 5);
    }

    use state::pair_checks::{lookup_pair, PairLookupError};
    let lookup = |id: &str| -> (r: Option<u8>) ensures r == (if id@ == "test"@ {Some(17u8)} else {None}), {
        if <&str>::exec_eq(id, "test") {Some(17)} else {None}
    };
    let observed = lookup_pair(2u8, Some("test"), Some("other"), lookup);
    assert(observed == Ok::<_, PairLookupError>((2u8, 17u8)));
    let observed = lookup_pair(2u8, None, Some("test"), lookup);
    assert(observed == Ok::<_, PairLookupError>((17u8, 2u8)));
    let observed = lookup_pair(2u8, None, None, lookup);
    assert(observed == Err::<(u8, u8), _>(PairLookupError::MissingProductionLink));
    let a = lookup_pair(2u8, Some("missing"), Some("test"), lookup);
    assert(a matches Err(PairLookupError::MissingTest(id)) && id@ == "missing"@);
    let b = lookup_pair(2u8, None, Some("other"), lookup);
    assert(b matches Err(PairLookupError::MissingProduction(id)) && id@ == "other"@);
}


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
    broadcast use vstd::array::group_array_axioms;
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
    assert(passed@[0].status@ == "passed"@);
    assert(failed@[0].status@ == "failed"@);
    assert(typo@[0].status@ == "passed "@);
    assert(late_error@[1].status@ == "error"@);
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

#[cfg(verus_keep_ghost)]
fn receipt_replies_and_operation_rows_preserve_the_actual_reason(
    id: String, other: String, check: Result<(), String>, failure: Option<String>, exit: i32,
    message: String, publish: Result<u8, String>,
)
    requires id@ != other@,
{
    let good = state::receipt_reply(id.as_str(),id.as_str(),id.as_str(),id.as_str(),Ok(None));
    assert(good.is_ok());
    let mismatch = state::receipt_reply(id.as_str(),id.as_str(),id.as_str(),other.as_str(),Ok(Some(message.clone())));
    assert(mismatch matches Err(s) && s@ == "E_RECEIPT_MISMATCH: routes response refers to another plan or operation"@);
    let invalid = state::receipt_reply(id.as_str(),id.as_str(),id.as_str(),id.as_str(),Err(()));
    assert(invalid matches Err(s) && s@ == "E_RECEIPT_MISMATCH: invalid receipt comparison"@);
    let schema = state::receipt_reply(id.as_str(),id.as_str(),id.as_str(),id.as_str(),Ok(Some(message.clone())));
    assert(schema == Err::<(),String>(message));
    let inspect = |_r: &u8| -> (v: (Result<(),String>,Option<String>,i32))
        ensures v == (check,failure,exit),
    { (check, failure, exit) };
    let diagnose = |_r: &u8,_code: i32| -> (v: String) ensures v@ == message@, { message.clone() };
    let row: state::OperationRow<u8,u8> = state::operation_result(id.clone(),Ok(3u8),inspect,diagnose);
    assert(row.operation == id && row.receipt == Some(3u8) && row.original.is_none());
    proof {
        let o = choose|o: (Result<(),String>,Option<String>,i32)|
            #[trigger] inspect.ensures((&3u8,), o) && match (o.0,o.1) {
                (Err(e),_) | (Ok(()),Some(e)) => row.status@ == "error"@ && row.error == Some(e),
                (Ok(()),None) => if o.2 == 0 { row.status@ == "passed"@ && row.error.is_none() }
                    else { row.status@ == "failed"@ && (row.error matches Some(e)
                           && diagnose.ensures((&3u8,o.2), e)) },
            };
        assert(o == (check,failure,exit));
        if check.is_ok() && failure.is_none() && exit != 0 {
            assert(row.error.is_some());
            assert(diagnose.ensures((&3u8,exit),row.error.unwrap()));
            assert(row.error.unwrap()@ == message@);
        }
    }
    assert(match check {
        Err(e) => row.status@ == "error"@ && row.error == Some(e),
        Ok(()) => match failure {
            Some(e) => row.status@ == "error"@ && row.error == Some(e),
            None => if exit == 0 { row.status@ == "passed"@ && row.error.is_none() }
                else { row.status@ == "failed"@ && (row.error matches Some(e) && e@ == message@) },
        },
    });
    let describe = |previous: Option<String>, e: String| -> (text: String)
        ensures text == if previous.is_some() { previous.unwrap() } else { e },
    { match previous { Some(old) => old, None => e } };
    let ghost before = row;
    let ghost retained = publish;
    let out = state::published_operation(row,publish,describe);
    assert(out.receipt == Some(3u8) && out.operation == id);
    proof { match retained {
        Ok(file) => { assert(out.original == Some(file) && out.status == before.status && out.error == before.error); },
        Err(error) => { assert(out.status@ == "error"@ && out.original.is_none()
            && out.error == if before.error.is_some() { before.error } else { Some(error) }); },
    } }
}

#[cfg(verus_keep_ghost)]
fn coverage_stream_selection_observes_order_bounds_and_completeness() {
    let bytes: [u8;5] = [65u8,10u8,66u8,10u8,67u8];
    assert(bytes@ =~= seq![65u8,10u8,66u8,10u8,67u8]);
    let inspect = |a: usize,b: usize| -> (v: Option<usize>)
        ensures v == if a == 0 { None } else { Some(a) },
    { if a == 0 { None } else { Some(a) } };
    let incomplete = state::first_coverage_line(&bytes,false,inspect);
    assert(incomplete.is_none());
    let observed = state::first_coverage_line(&bytes,true,inspect);
    assert(state::whole_line(bytes@,2,3));
    assert forall|a: usize,b: usize| state::whole_line(bytes@,a as int,b as int)
        implies (a == 0 || a == 2 || a == 4) by {};
    proof {
        if let Some(value) = observed {
            let (a,b) = choose|a: usize,b: usize| state::whole_line(bytes@,a as int,b as int)
                && #[trigger] inspect.ensures((a,b),Some(value))
                && forall|i: usize,j: usize| i < a && state::whole_line(bytes@,i as int,j as int)
                    ==> #[trigger] inspect.ensures((i,j),None);
            if a > 2 { assert(inspect.ensures((2usize,3usize),None)); }
            assert(a == 2);
            assert(inspect.ensures((a,b),Some(value)));
        } else {
            assert(inspect.ensures((2usize,3usize),None));
        }
    }
    assert(observed == Some(2usize));
    let alternate = || -> (v: Option<usize>) ensures v == Some(7usize), { Some(7usize) };
    let err = state::preferred_diagnostic(observed,alternate);
    let fallback = state::preferred_diagnostic(incomplete,alternate);
    assert(err == Some(2usize) && fallback == Some(7usize));
    let yes = || -> (r: bool) ensures r, { true };
    let no = || -> (r: bool) ensures !r, { false };
    let valid = state::coverage_detail("E_VERUS_COVERAGE",1024,yes,no);
    let space = state::coverage_detail("E_VERUS_COVERAGE",1,no,no);
    let control = state::coverage_detail("E_VERUS_COVERAGE",9,yes,yes);
    assert(valid && !space && !control);
}

#[cfg(verus_keep_ghost)]
fn prerequisite_and_test_outcomes_use_only_the_named_operations(
    first: String, second: String, foreign: String, test: String, other: String, failure: String,
)
    requires vstd::laws_cmp::obeys_cmp::<String>(), first != second, first != foreign,
        second != foreign, test != other, failure@ != "passed"@,
{
    use state::Prerequisites::{Blocked, Passed, Waiting};
    broadcast use vstd::std_specs::btree::group_btree_axioms;
    let mut statuses = std::collections::BTreeMap::new();
    let mut tests = std::collections::BTreeMap::new();
    let empty: [String; 0] = [];
    let required = [first.clone(), second.clone(), first.clone()];
    let mut predecessors = std::collections::BTreeSet::new();
    let observed = state::prerequisite_status(&predecessors, &statuses);
    assert(observed == Passed);
    predecessors.insert(first.clone());
    predecessors.insert(second.clone());
    let shared = [first.clone()];
    assert(required@ =~= seq![first, second, first]);
    assert(shared@ =~= seq![first]);
    assert(predecessors@ =~= set![first, second]);
    assert(predecessors@.contains(first) && predecessors@.contains(second));
    statuses.insert(foreign.clone(), failure.clone());
    assert(!statuses@.contains_key(first) && !statuses@.contains_key(second));
    state::record_executed_test(&mut tests, &other, &empty, &statuses);
    assert(tests@[other]@ == "passed"@);
    let observed = state::prerequisite_status(&predecessors, &statuses);
    assert(!state::selected_test_passed(statuses@, first) && predecessors@.contains(first));
    assert forall|id: String| #[trigger] predecessors@.contains(id) implies
        (!statuses@.contains_key(id) || state::selected_test_passed(statuses@, id)) by {
        assert(id == first || id == second);
    }
    assert(observed == Waiting);
    statuses.insert(second.clone(), failure.clone());
    assert(statuses@[second]@ != "passed"@ && predecessors@.contains(second));
    let observed = state::prerequisite_status(&predecessors, &statuses);
    assert(observed == Blocked);
    state::record_executed_test(&mut tests, &test, &required, &statuses);
    assert(tests@[test]@ == "failed"@ && tests@[other]@ == "passed"@);
    statuses.insert(second.clone(), "passed".to_string());
    let observed = state::prerequisite_status(&predecessors, &statuses);
    assert(!state::selected_test_passed(statuses@, first) && predecessors@.contains(first));
    assert forall|id: String| #[trigger] predecessors@.contains(id) implies
        (!statuses@.contains_key(id) || state::selected_test_passed(statuses@, id)) by {
        assert(id == first || id == second);
    }
    assert(observed == Waiting);
    state::record_executed_test(&mut tests, &other, &shared, &statuses);
    assert(tests@[other]@ == "failed"@ && tests@[test]@ == "failed"@);
    statuses.insert(first.clone(), "passed".to_string());
    let observed = state::prerequisite_status(&predecessors, &statuses);
    assert(observed == Passed);
    state::record_executed_test(&mut tests, &test, &required, &statuses);
    assert(tests@[test]@ == "passed"@ && tests@[other]@ == "failed"@);
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
