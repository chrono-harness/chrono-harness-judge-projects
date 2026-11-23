//! Invoke bounded host commands through the installed runner's binary stream protocol.
use serde::{Deserialize, Serialize};
use serde_json::json;
use std::{
    collections::BTreeMap,
    io::Write,
    path::Path,
    process::{Command, Stdio},
};

#[derive(Serialize)]
pub struct Spec {
    pub program: String,
    pub args: Vec<String>,
    pub env: BTreeMap<String, String>,
    pub timeout_seconds: u64,
    pub output_limit_bytes: usize,
}

pub(crate) type Streams = (i32, Vec<u8>, Vec<u8>);

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
        .arg("run-command-v1")
        .current_dir(root)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    chrono_harness::process_fds::forward_command(&mut command, &[])?;
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
    if lengths.stdout_length.checked_add(lengths.stderr_length) != Some(bytes.len()) {
        return Err("runner response length mismatch".into());
    }
    let (stdout, stderr) = bytes.split_at(lengths.stdout_length);
    Ok((lengths.exit_code, stdout.to_vec(), stderr.to_vec()))
}
