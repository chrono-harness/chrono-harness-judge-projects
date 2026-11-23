//! Observe both endpoints and both working-tree checks through the same installed Git reader.
use chrono_harness::wire::Request;
use serde::Deserialize;
use serde::de::DeserializeOwned;
use serde_json::{Value, json};
use std::{
    collections::BTreeMap,
    io::{BufRead, BufReader, Write},
    process::{Child, ChildStdin, ChildStdout, Command, Stdio},
};

#[derive(Deserialize)]
pub(crate) struct Snapshot {
    pub values: BTreeMap<String, Value>,
    pub originals: BTreeMap<String, String>,
    pub effective_path: String,
}

pub(crate) struct Reader {
    child: Child,
    input: Option<ChildStdin>,
    output: BufReader<ChildStdout>,
    pub bound: bool,
}
impl Reader {
    pub fn open(request: &Request) -> Result<Self, String> {
        let root = &request.candidate.root;
        let program = chrono_harness::resolve_program(root, &request.runner.path, None)?;
        if chrono_harness::file_identity(&program)?.0 != request.runner.sha256 {
            return Err("E_TOOL_BINDING: runner executable changed".into());
        }
        let mut command = Command::new(&program);
        command
            .arg("git-facts-v1")
            .current_dir(root)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped());
        chrono_harness::process_fds::forward_command(&mut command, &[])?;
        let mut child = command
            .spawn()
            .map_err(|e| format!("chrono-harness git-facts-v1: {e}"))?;
        let input = child.stdin.take();
        let output = BufReader::new(child.stdout.take().unwrap());
        let mut reader = Self {
            child,
            input,
            output,
            bound: false,
        };
        #[derive(Deserialize)]
        struct Opened {
            bound: bool,
        }
        reader.bound = reader
            .call::<Opened>(json!({"mode":"request","request":request}))?
            .bound;
        Ok(reader)
    }
    fn call<T: DeserializeOwned>(&mut self, command: Value) -> Result<T, String> {
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
        if line.last() != Some(&b'\n') {
            return Err("E_PROTOCOL: incomplete Git facts response".into());
        }
        serde_json::from_slice::<Result<T, String>>(&line)
            .map_err(|e| format!("E_PROTOCOL: {e}"))?
    }
    pub fn snapshot(&mut self, endpoint: &str) -> Result<Snapshot, String> {
        self.call(json!({"op":"registry-snapshot","endpoint":endpoint}))
    }
    pub fn checkout(&mut self, artifacts: &[String]) -> Result<Checkout, String> {
        self.call(json!({"op":"checkout-excluding","artifacts":artifacts}))
    }
    pub fn observation(&mut self) -> Result<Value, String> {
        self.call(json!({"op":"observation"}))
    }
    pub fn close(mut self) -> Result<(), String> {
        drop(self.input.take());
        let status = self.child.wait().map_err(|e| e.to_string())?;
        if status.success() {
            Ok(())
        } else {
            Err(format!("git-facts-v1 exited {status}"))
        }
    }
}
impl Drop for Reader {
    fn drop(&mut self) {
        drop(self.input.take());
        let _ = self.child.wait();
    }
}

#[derive(Deserialize)]
pub(crate) struct Checkout {
    pub head: String,
    pub tracked: Vec<String>,
    pub untracked: Vec<String>,
    pub index_flags: Vec<IndexFlag>,
}

#[derive(Deserialize)]
pub(crate) struct IndexFlag {
    pub tag: String,
}
