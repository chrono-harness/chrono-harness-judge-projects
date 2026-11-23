//! Read registration projections for the executor and replay original declarations.
use crate::git_reader::Reader;
use crate::routes::Scheduling;
use chrono_harness::wire::Request;
use serde::Deserialize;
use serde_json::{Value, json};
use std::{
    collections::BTreeMap,
    path::{Path, PathBuf},
    process::{Command, Stdio},
};

#[derive(Deserialize)]
pub(crate) struct Binding {
    pub owner: String,
    pub operation: String,
}

#[derive(Deserialize)]
pub(crate) struct Registry {
    config_path: String,
    pub filemap: Value,
    pub definitions: BTreeMap<String, Vec<String>>,
    pub bindings: BTreeMap<String, Vec<Binding>>,
    pub retirements: Result<BTreeMap<String, Option<String>>, String>,
    pub downstream: bool,
    pub scheduling: Result<Option<Scheduling>, String>,
    pub effective_inputs: Option<Result<Value, String>>,
    view: Value,
}

const NAME: &str = "chrono-judge-registration";

fn installed(root: &Path, config: &Value) -> Result<PathBuf, String> {
    let tool = config["tools"]
        .as_array()
        .into_iter()
        .flatten()
        .find(|t| t["id"] == NAME);
    let program = match tool {
        Some(tool) => tool["program"]
            .as_str()
            .ok_or("missing registration tool program")?,
        None => NAME,
    };
    chrono_harness::resolve_program(root, program, None)
}

pub(super) fn host_config(root: &Path) -> Result<Value, String> {
    let entry = ".chrono-harness/config.json";
    if root.join(entry).try_exists().map_err(|e| e.to_string())? {
        chrono_harness::load_selected_config(root, entry)
    } else {
        Ok(Value::Null)
    }
}

pub(super) fn standalone(root: &Path, registry: &Value) -> Result<(), String> {
    let config = host_config(root)?;
    let program = installed(root, &config)?;
    if !query(root, &program, "check-project-registry-v1", registry)?.is_null() {
        return Err("E_PROTOCOL: invalid project registry response".into());
    }
    Ok(())
}

/// Send JSON and drain the reply concurrently. Native requests can contain relative coordinates;
/// the caller selects the directory in which the registration query must interpret them.
fn query(root: &Path, program: &Path, operation: &str, input: &Value) -> Result<Value, String> {
    let program = program.canonicalize().map_err(|err| err.to_string())?;
    let runner = crate::host_runner(root)?;
    let mut command = Command::new(&runner);
    command
        .current_dir(root)
        .arg("exec-with-descriptors-v1")
        .arg(&runner)
        .arg("installed-query-v1")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let request = json!({"root":root,"environment":"inherited","program":program,"operation":operation,"input":input});
    let mut process = command.spawn().map_err(|e| e.to_string())?;
    let stdin = process.stdin.take().expect("piped stdin");
    let (output, written) = std::thread::scope(|scope| {
        let sender = scope.spawn(move || serde_json::to_writer(stdin, &request));
        (process.wait_with_output(), sender.join())
    });
    let out = output.map_err(|e| e.to_string())?;
    if !out.status.success() {
        let reason = String::from_utf8(out.stderr).map_err(|e| e.to_string())?;
        return Err(if reason.is_empty() {
            format!("registration {operation} {}", out.status)
        } else {
            reason.strip_suffix('\n').unwrap_or(&reason).into()
        });
    }
    written
        .map_err(|_| "registration input writer panicked")?
        .map_err(|e| e.to_string())?;
    chrono_harness::decode(&out.stdout)
}
impl Registry {
    pub fn runner(&self, root: &Path) -> Result<PathBuf, String> {
        let name = self.config()["runner"]["path"]
            .as_str()
            .ok_or("missing registered runner path")?;
        chrono_harness::resolve_program(root, name, None)
    }
    pub fn config(&self) -> &Value {
        &self.view["candidate"][&self.config_path]
    }
    pub fn projects(&self) -> &Value {
        self.document("projects")
    }
    pub fn judges(&self) -> &Value {
        self.document("judges")
    }
    fn document(&self, id: &str) -> &Value {
        let path = self.config()["registries"][id]
            .as_str()
            .expect("validated registry path");
        &self.view["candidate"][path]
    }
    fn validate_documents(&self) -> Result<(), String> {
        let docs = &self.view["candidate"];
        let config = &docs[&self.config_path];
        for field in ["judges", "projects"] {
            if !config["registries"][field]
                .as_str()
                .and_then(|path| docs.get(path))
                .is_some_and(Value::is_object)
            {
                return Err(format!(
                    "E_PROTOCOL: registration project view missing {field}"
                ));
            }
        }
        Ok(())
    }

    pub fn evidence(&self, root: &Path, req: &Request, evidence: Value) -> Result<Value, String> {
        let program = installed(root, self.config())?;
        let launch_directory;
        let cwd = if evidence["mode"] == "live" {
            launch_directory = std::env::current_dir().map_err(|e| e.to_string())?;
            launch_directory.as_path()
        } else {
            root
        };
        let reply = query(
            cwd,
            &program,
            "project-evidence-v1",
            &json!({"request":req,"view":self.view,"evidence":evidence}),
        )?;
        if reply["request_id"] != req.request_id {
            return Err("E_PROTOCOL: registration project evidence identity".into());
        }
        reply
            .get("effective_inputs")
            .cloned()
            .ok_or("registration effective inputs missing".into())
    }
}

#[derive(Default)]
pub(super) struct Observations {
    extra: Option<(usize, Vec<Value>)>,
}

impl Observations {
    fn record(&mut self, reader: &mut Reader, mut external: Value) -> Result<(), String> {
        let mut original = reader.observation()?;
        let local = original
            .as_object_mut()
            .ok_or("E_GIT_FACTS: missing projects binding")?;
        let remote = external
            .as_object_mut()
            .ok_or("E_GIT_FACTS: missing registration binding")?;
        let Some(Value::Array(local_rows)) = local.remove("processes") else {
            return Err("E_GIT_FACTS: missing projects processes".into());
        };
        let Some(Value::Array(remote_rows)) = remote.remove("processes") else {
            return Err("E_GIT_FACTS: missing registration processes".into());
        };
        if local != remote {
            return Err("E_GIT_FACTS: registration and projects bindings differ".into());
        }
        self.extra = Some((local_rows.len(), remote_rows));
        Ok(())
    }
    pub fn finish(self, reader: &mut Reader) -> Result<Value, String> {
        let mut original = reader.observation()?;
        if let (Some((offset, extra)), Some(processes)) =
            (self.extra, original["processes"].as_array_mut())
        {
            processes.splice(offset..offset, extra);
        }
        Ok(original)
    }
}

pub(super) fn views(
    req: &Request,
    reader: &mut Reader,
    observations: &mut Observations,
    validate_inputs: bool,
) -> Result<Registry, String> {
    let root = &req.candidate.root;
    let base = reader.snapshot("base")?;
    let candidate = reader.snapshot("candidate")?;
    let program = installed(root, &candidate.values[&candidate.effective_path])?;
    let request = json!({"request":req,"validate_inputs":validate_inputs,"originals":[base.originals,candidate.originals]});
    let cwd = std::env::current_dir().map_err(|e| e.to_string())?;
    let mut reply = query(&cwd, &program, "project-views-v1", &request)?;
    if reply["request_id"] != req.request_id
        || reply["commits"] != json!([req.base.commit, req.candidate.commit])
    {
        return Err("E_PROTOCOL: registration project views identity".into());
    }
    if let Some(extra) = reply
        .as_object_mut()
        .and_then(|v| v.remove("git_facts"))
        .filter(|v| !v.is_null())
    {
        observations.record(reader, extra)?;
    }
    if let Some(error) = reply.get("error") {
        return Err(error
            .as_str()
            .ok_or("invalid project registration error")?
            .into());
    }
    let registry: Registry = serde_json::from_value(reply).map_err(|e| e.to_string())?;
    registry.validate_documents()?;
    Ok(registry)
}
