//! Blocking JSON lines connection to a single native runner capability.
use serde::de::DeserializeOwned;
use serde_json::Value;
use std::{
    io::{BufRead, BufReader, Write},
    path::Path,
    process::{Child, ChildStdin, ChildStdout, Command, Stdio},
};

pub(crate) struct Session {
    child: Child,
    input: Option<ChildStdin>,
    output: BufReader<ChildStdout>,
    name: &'static str,
}
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
        if line.last() != Some(&b'\n') {
            return Err("E_PROTOCOL: incomplete runner response".into());
        }
        serde_json::from_slice::<Result<T, String>>(&line)
            .map_err(|e| format!("E_PROTOCOL: {e}"))?
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
impl Drop for Session {
    fn drop(&mut self) {
        drop(self.input.take());
        let _ = self.child.wait();
    }
}
