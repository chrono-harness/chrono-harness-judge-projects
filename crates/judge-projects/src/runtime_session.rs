//! Blocking JSON lines connection to a single native runner capability.
#![allow(unexpected_cfgs)]
#[cfg(not(verus_keep_ghost))]
use vstd::prelude::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

verus! {
/// Decode the entire JSON line and propagate the original wire or application error.
pub fn runner_reply<T, D>(line: &[u8], decode: D) -> (out: Result<T, String>)
    where D: FnOnce(&[u8]) -> Result<Result<T, String>, String>,
    requires (line@.len() > 0 && line@.last() == 10) ==> decode.requires((line,)),
    ensures if line@.len() == 0 || line@.last() != 10 {
        out matches Err(error) && error@ == "E_PROTOCOL: incomplete runner response"@
    } else {
        exists|decoded: Result<Result<T, String>, String>| #[trigger] decode.ensures((line,), decoded)
            && match decoded { Ok(value) => out == value, Err(error) => out == Err::<T, String>(error) }
    },
{
    if line.len() == 0 || line[line.len() - 1] != 10 {
        return Err("E_PROTOCOL: incomplete runner response".to_string());
    }
    let decoded = decode(line);
    assert(decode.ensures((line,), decoded));
    match decoded { Ok(value) => value, Err(error) => Err(error) }
}
}

#[cfg(not(verus_keep_ghost))]
use serde::de::DeserializeOwned;
#[cfg(not(verus_keep_ghost))]
use serde_json::Value;
#[cfg(not(verus_keep_ghost))]
use std::{
    io::{BufRead, BufReader, Write},
    path::Path,
    process::{Child, ChildStdin, ChildStdout, Command, Stdio},
};

#[cfg(not(verus_keep_ghost))]
pub(crate) struct Session {
    child: Child,
    input: Option<ChildStdin>,
    output: BufReader<ChildStdout>,
    name: &'static str,
}
#[cfg(not(verus_keep_ghost))]
impl Session {
    pub fn open(root: &Path, program: &Path, name: &'static str) -> Result<Self, String> {
        let mut command = Command::new(program);
        command
            .arg("exec-with-descriptors-v1")
            .arg(program)
            .arg(name)
            .current_dir(root)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped());
        let mut child = command
            .spawn()
            .map_err(|e| format!("{} {name}: {e}", program.display()))?;
        let input = child.stdin.take();
        let output = BufReader::new(child.stdout.take().expect("piped stdout"));
        Ok(Self {
            child,
            input,
            output,
            name,
        })
    }
    pub fn call<T: DeserializeOwned>(&mut self, command: Value) -> Result<T, String> {
        let stdin = self.input.as_mut().unwrap();
        serde_json::to_writer(&mut *stdin, &command).map_err(|e| e.to_string())?;
        stdin
            .write_all(b"\n")
            .and_then(|_| stdin.flush())
            .map_err(|e| e.to_string())?;
        let mut line = Vec::new();
        self.output
            .read_until(b'\n', &mut line)
            .map_err(|e| e.to_string())?;
        runner_reply(&line, |bytes| {
            serde_json::from_slice::<Result<T, String>>(bytes)
                .map_err(|e| format!("E_PROTOCOL: {e}"))
        })
    }
    pub fn decode<T: DeserializeOwned>(&mut self, bytes: &[u8]) -> Result<T, String> {
        let text = std::str::from_utf8(bytes).map_err(|e| e.to_string())?;
        self.call(serde_json::json!({"operation":"decode-json","text":text}))
    }

    pub fn close(mut self) -> Result<(), String> {
        drop(self.input.take());
        let status = self.child.wait().map_err(|e| e.to_string())?;
        if status.success() {
            Ok(())
        } else {
            Err(format!("{} exited {status}", self.name))
        }
    }
}
#[cfg(not(verus_keep_ghost))]
impl Drop for Session {
    fn drop(&mut self) {
        drop(self.input.take());
        let _ = self.child.wait();
    }
}
