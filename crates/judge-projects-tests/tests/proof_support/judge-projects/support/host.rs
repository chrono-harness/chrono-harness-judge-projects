#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

verus! {
pub fn failed_command<T>(panicked: bool, last_command: Option<T>) -> (evidence: Option<T>)
    ensures evidence == (if panicked { last_command } else { None }),
{
    if panicked { last_command } else { None }
}
}
