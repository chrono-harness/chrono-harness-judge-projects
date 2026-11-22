#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

verus! {
pub fn keep_scheduler_diagnostics(execution_passed: bool, trace_complete: bool) -> (keep: bool)
    ensures keep == !(execution_passed && trace_complete),
{
    !execution_passed || !trace_complete
}
}
