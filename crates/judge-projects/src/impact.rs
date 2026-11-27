#![allow(unexpected_cfgs)]
#[cfg(not(verus_keep_ghost))]
use vstd::prelude::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

verus! {
/// A successful command supplies the decoder bytes. Its error supplies the original diagnostic.
pub(crate) fn reply_stream<'a>(code: i32, stdout: &'a [u8], stderr: &'a [u8])
    -> (reply: Result<&'a [u8], &'a [u8]>)
    ensures if code == 0 { reply == Ok::<&[u8], &[u8]>(stdout) }
        else { reply == Err::<&[u8], &[u8]>(stderr) },
{
    if code == 0 { Ok(stdout) } else { Err(stderr) }
}
}

#[cfg(not(verus_keep_ghost))]
use crate::commands::Spec as CommandSpec;
#[cfg(not(verus_keep_ghost))]
use serde::Deserialize;
#[cfg(not(verus_keep_ghost))]
use serde_json::Value;
#[cfg(not(verus_keep_ghost))]
use std::collections::{BTreeMap, BTreeSet};

#[cfg(not(verus_keep_ghost))]
#[derive(Debug, Deserialize)]
pub struct ProjectImpact {
    pub reached: BTreeSet<String>,
    pub retired_tests: Vec<String>,
}

/// FILEMAP owns the decoder for the complete impact, including fields projects never reads.
#[cfg(not(verus_keep_ghost))]
pub fn decode(
    impact: &Value,
    protocol: &Value,
    environment: &BTreeMap<String, String>,
    run: impl FnOnce(&CommandSpec, &[u8]) -> Result<(i32, Vec<u8>, Vec<u8>), String>,
) -> Result<ProjectImpact, String> {
    let command = CommandSpec {
        program: "chrono-judge-filemap".into(),
        args: vec!["impact-summary".into()],
        env: environment.clone(),
        timeout_seconds: protocol["timeout_seconds"]
            .as_u64()
            .ok_or("invalid protocol timeout")?,
        output_limit_bytes: protocol["stdout_limit_bytes"]
            .as_u64()
            .and_then(|n| usize::try_from(n).ok())
            .ok_or("invalid protocol output bound")?,
    };
    let (code, output, diagnostic) = run(
        &command,
        &serde_json::to_vec(impact).map_err(|e| e.to_string())?,
    )?;
    match reply_stream(code, &output, &diagnostic) {
        Ok(stdout) => serde_json::from_slice(stdout).map_err(|error| error.to_string()),
        Err(stderr) => {
            let text = std::str::from_utf8(stderr).map_err(|error| error.to_string())?;
            let text = text.strip_suffix('\n').unwrap_or(text);
            Err(if text.is_empty() {
                format!("FILEMAP impact-summary exited with {code}")
            } else {
                text.into()
            })
        }
    }
}
