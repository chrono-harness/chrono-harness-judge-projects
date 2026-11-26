//! Release acceptance for the original project-pair error exit and nonempty diagnostic.
#![allow(unexpected_cfgs)]
#[cfg(not(verus_keep_ghost))]
use vstd::prelude::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

verus! {
pub fn accepts(exit: i32, error_bytes: u64) -> (accepted: bool)
    ensures accepted == (exit == 2 && error_bytes > 0),
{
    exit == 2 && error_bytes > 0
}
}

#[cfg(not(verus_keep_ghost))]
fn main() -> Result<(), String> {
    let arguments: Vec<_> = std::env::args().skip(1).collect();
    let [exit, error_file] = arguments.as_slice() else {
        return Err("usage: release_observation EXIT ERROR_FILE".into());
    };
    let exit = exit.parse::<i32>().map_err(|e| e.to_string())?;
    let error_bytes = std::fs::metadata(error_file)
        .map_err(|e| e.to_string())?
        .len();
    let admitted = accepts(exit, error_bytes);
    if admitted {
        Ok(())
    } else {
        Err(format!("unexpected release observation for {arguments:?}"))
    }
}
