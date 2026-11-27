//! Invoke bounded host commands through the installed runner's binary stream protocol.
#![allow(unexpected_cfgs)]
#[cfg(not(verus_keep_ghost))]
use vstd::prelude::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

verus! {
/// The announced stream lengths must exhaust the payload at a valid split point.
pub(crate) fn stream_boundary(stdout: usize, stderr: usize, payload: usize) -> (end: Option<usize>)
    ensures end == if stdout as int + stderr as int == payload as int { Some(stdout) } else { None },
        end matches Some(i) ==> i <= payload,
{
    if stdout <= payload && stderr == payload - stdout { Some(stdout) } else { None }
}
}

#[cfg(not(verus_keep_ghost))]
use serde::{Deserialize, Serialize};
#[cfg(not(verus_keep_ghost))]
use serde_json::json;
#[cfg(not(verus_keep_ghost))]
use std::{
    collections::BTreeMap,
    io::Write,
    path::Path,
    process::{Command, Stdio},
};

#[cfg(not(verus_keep_ghost))]
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Spec {
    pub program: String,
    #[serde(default)]
    pub args: Vec<String>,
    #[serde(default)]
    pub env: BTreeMap<String, String>,
    pub timeout_seconds: u64,
    pub output_limit_bytes: usize,
}

#[cfg(not(verus_keep_ghost))]
pub(crate) type Streams = (i32, Vec<u8>, Vec<u8>);

#[cfg(not(verus_keep_ghost))]
pub(crate) fn invoke(
    root: &Path,
    runner: &Path,
    spec: &Spec,
    digest: Option<&str>,
    input: &[u8],
) -> Result<Streams, String> {
    let mut request = serde_json::to_value(spec).map_err(|e| e.to_string())?;
    if let Some(digest) = digest {
        request["expected_sha256"] = json!(digest);
    }
    let mut command = Command::new(runner);
    command
        .arg("exec-with-descriptors-v1")
        .arg(runner)
        .arg("run-command-v1")
        .current_dir(root)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let mut child = command.spawn().map_err(|e| e.to_string())?;
    let mut stdin = child.stdin.take().expect("piped stdin");
    let (reply, written) = std::thread::scope(|scope| {
        let writer = scope.spawn(move || -> Result<(), String> {
            serde_json::to_writer(&mut stdin, &request).map_err(|e| e.to_string())?;
            stdin
                .write_all(b"\n")
                .and_then(|()| stdin.write_all(input))
                .map_err(|e| e.to_string())
        });
        (child.wait_with_output(), writer.join())
    });
    let reply = reply.map_err(|e| e.to_string())?;
    if !reply.status.success() {
        return Err(String::from_utf8_lossy(&reply.stderr).trim_end().into());
    }
    written.map_err(|_| "runner input writer panicked")??;
    let end = reply
        .stdout
        .iter()
        .position(|b| *b == b'\n')
        .ok_or("runner response header missing")?;
    #[derive(Deserialize)]
    struct Lengths {
        exit_code: i32,
        stdout_length: usize,
        stderr_length: usize,
    }
    let lengths: Lengths =
        serde_json::from_slice(&reply.stdout[..end]).map_err(|e| e.to_string())?;
    let bytes = &reply.stdout[end + 1..];
    let boundary = stream_boundary(lengths.stdout_length, lengths.stderr_length, bytes.len())
        .ok_or("runner response length mismatch")?;
    let (stdout, stderr) = bytes.split_at(boundary);
    Ok((lengths.exit_code, stdout.to_vec(), stderr.to_vec()))
}

/// Call one installed runner query while retaining the original caller's descriptors and cwd.
#[cfg(not(verus_keep_ghost))]
pub(crate) fn query<T: serde::de::DeserializeOwned>(
    root: &Path,
    runner: &Path,
    operation: &str,
    request: &serde_json::Value,
) -> Result<T, String> {
    let mut child = Command::new(runner)
        .arg("exec-with-descriptors-v1")
        .arg(runner)
        .arg(operation)
        .current_dir(root)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| e.to_string())?;
    let stdin = child.stdin.take().expect("piped stdin");
    let (output, written) = std::thread::scope(|scope| {
        let writer = scope.spawn(|| serde_json::to_writer(stdin, request));
        (child.wait_with_output(), writer.join())
    });
    let output = output.map_err(|e| e.to_string())?;
    if !output.status.success() {
        let message = String::from_utf8(output.stderr).map_err(|e| e.to_string())?;
        return Err(if message.is_empty() {
            format!("{operation} {}", output.status)
        } else {
            message.strip_suffix('\n').unwrap_or(&message).into()
        });
    }
    written
        .map_err(|_| "installed runner input writer panicked")?
        .map_err(|e| e.to_string())?;
    let mut evidence = crate::runtime_session::Session::open(root, runner, "judge-evidence-v1")?;
    let reply = evidence.decode(&output.stdout)?;
    evidence.close()?;
    Ok(reply)
}
