#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

verus! {
/// The mock may write only when both compiler destination declarations agree.
pub fn accepts_output(argument_count: usize, output_flag: bool, emit_matches: bool) -> (valid: bool)
    ensures valid == (argument_count == 12 && output_flag && emit_matches),
{
    argument_count == 12 && output_flag && emit_matches
}
}
