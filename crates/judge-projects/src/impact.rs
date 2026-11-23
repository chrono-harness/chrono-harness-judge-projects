use crate::commands::Spec as CommandSpec;
use serde::Deserialize;
use serde_json::Value;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Deserialize)]
pub struct ProjectImpact {
    pub reached: BTreeSet<String>,
    pub retired_tests: Vec<String>,
}

/// FILEMAP owns the decoder for the complete impact, including fields projects never reads.
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
    if code != 0 {
        let text = String::from_utf8(diagnostic).map_err(|e| e.to_string())?;
        let text = text.strip_suffix('\n').unwrap_or(&text);
        return Err(if text.is_empty() {
            format!("FILEMAP impact-summary exited with {code}")
        } else {
            text.into()
        });
    }
    serde_json::from_slice(&output).map_err(|e| e.to_string())
}
