//! Read registration projections for the executor and replay original declarations.
#![allow(unexpected_cfgs)]
#[cfg(not(verus_keep_ghost))]
use vstd::prelude::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

verus! {
/// Check the response identity, record its Git observation, then consume its registration data.
pub fn admit_project_view<R, T, O, D>(
    reply: R, request_matches: bool, commits_match: bool, observe: O, consume: D,
) -> (out: Result<T, String>)
    where O: FnOnce(R) -> (R, Result<(), String>), D: FnOnce(R) -> Result<T, String>,
    requires
        (request_matches && commits_match) ==> observe.requires((reply,)),
        forall|next: R, result: Result<(), String>|
            (request_matches && commits_match && result.is_ok()
                && #[trigger] observe.ensures((reply,), (next, result))) ==> consume.requires((next,)),
    ensures if !request_matches || !commits_match {
        out matches Err(error) && error@ == "E_PROTOCOL: registration project views identity"@
    } else {
        exists|next: R, result: Result<(), String>| #[trigger] observe.ensures((reply,), (next, result))
            && match result { Err(error) => out == Err::<T, String>(error), Ok(()) => consume.ensures((next,), out) }
    },
{
    if !request_matches || !commits_match {
        return Err("E_PROTOCOL: registration project views identity".to_string());
    }
    let (next, result) = observe(reply);
    assert(observe.ensures((reply,), (next, result)));
    match result {
        Err(error) => Err(error),
        Ok(()) => {
            assert(consume.requires((next,)));
            consume(next)
        }
    }
}
}

#[cfg(not(verus_keep_ghost))]
use crate::git_reader::Reader;
#[cfg(not(verus_keep_ghost))]
use crate::routes::Scheduling;
#[cfg(not(verus_keep_ghost))]
use crate::wire::Request;
#[cfg(not(verus_keep_ghost))]
use serde::Deserialize;
#[cfg(not(verus_keep_ghost))]
use serde_json::{Value, json};
#[cfg(not(verus_keep_ghost))]
use std::{
    collections::BTreeMap,
    path::{Path, PathBuf},
};

#[cfg(not(verus_keep_ghost))]
#[derive(Deserialize)]
pub(crate) struct Binding {
    pub owner: String,
    pub operation: String,
}

#[cfg(not(verus_keep_ghost))]
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

#[cfg(not(verus_keep_ghost))]
const NAME: &str = "chrono-judge-registration";

#[cfg(not(verus_keep_ghost))]
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
    crate::wire::resolve_program(root, program, None)
}

#[cfg(not(verus_keep_ghost))]
const ENTRY: &str = ".chrono-harness/config.json";

/// Most hosts provide a standard installed runner. An explicitly installed custom path may
/// itself be supplied by a native platform profile before that runner can read its full policy.
#[cfg(not(verus_keep_ghost))]
fn declared_runtime(root: &Path) -> Result<PathBuf, String> {
    fn document(root: &Path, name: &str) -> Result<Value, String> {
        use std::path::Component;
        let mut path = root.to_path_buf();
        for component in Path::new(name).components() {
            let Component::Normal(name) = component else {
                return Err("invalid host configuration path".into());
            };
            path.push(name);
            if path
                .symlink_metadata()
                .map_err(|e| e.to_string())?
                .is_symlink()
            {
                return Err(format!("host configuration symlink: {}", path.display()));
            }
        }
        serde_json::from_reader(std::fs::File::open(path).map_err(|e| e.to_string())?)
            .map_err(|e| e.to_string())
    }
    let config = document(root, ENTRY)?;
    let config = match config["schema"].as_str() {
        Some("chrono-git-configs/v1" | "chrono-git-configs/v2" | "chrono-git-configs/v3") => {
            let platform = format!("{}-{}", std::env::consts::OS, std::env::consts::ARCH);
            let host = &config["platforms"][platform];
            let path = if let Some(path) = host.as_str() {
                path
            } else {
                let program = host["program"]
                    .as_str()
                    .map(Path::new)
                    .filter(|p| p.is_absolute())
                    .ok_or("Git selector program required")?;
                let hash = crate::wire::file_identity(program)?.0;
                host["configurations"]
                    .as_array()
                    .into_iter()
                    .flatten()
                    .find(|row| row["sha256"] == hash)
                    .and_then(|row| row["path"].as_str())
                    .ok_or("Git config selector has no registered executable identity")?
            };
            document(root, path)?
        }
        _ => config,
    };
    let path = config["runner"]["path"]
        .as_str()
        .unwrap_or("chrono-harness");
    crate::wire::resolve_program(root, path, None)
}

#[cfg(not(verus_keep_ghost))]
pub(super) fn host_config(root: &Path) -> Result<Value, String> {
    if !root.join(ENTRY).try_exists().map_err(|e| e.to_string())? {
        return Ok(Value::Null);
    }
    let runner = [".chrono-harness/bin/chrono-harness", "chrono-harness"]
        .into_iter()
        .find_map(|name| crate::wire::resolve_program(root, name, None).ok())
        .map(Ok)
        .unwrap_or_else(|| declared_runtime(root))?;
    crate::commands::query(root, &runner, "selected-host-config-v1", &json!(ENTRY))
}

#[cfg(not(verus_keep_ghost))]
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
#[cfg(not(verus_keep_ghost))]
fn query(root: &Path, program: &Path, operation: &str, input: &Value) -> Result<Value, String> {
    let program = program.canonicalize().map_err(|err| err.to_string())?;
    let runner = crate::host_runner(root)?;
    crate::commands::query(
        root,
        &runner,
        "installed-query-v1",
        &json!({
            "root":root,"environment":"inherited","program":program,"operation":operation,"input":input
        }),
    )
}
#[cfg(not(verus_keep_ghost))]
impl Registry {
    pub fn runner(&self, root: &Path) -> Result<PathBuf, String> {
        let name = self.config()["runner"]["path"]
            .as_str()
            .ok_or("missing registered runner path")?;
        crate::wire::resolve_program(root, name, None)
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

#[cfg(not(verus_keep_ghost))]
#[derive(Default)]
pub(super) struct Observations {
    extra: Option<(usize, Vec<Value>)>,
}

#[cfg(not(verus_keep_ghost))]
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

#[cfg(not(verus_keep_ghost))]
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
    let reply = query(&cwd, &program, "project-views-v1", &request)?;
    let request_matches = reply["request_id"] == req.request_id;
    let commits_match =
        request_matches && reply["commits"] == json!([req.base.commit, req.candidate.commit]);
    admit_project_view(
        reply,
        request_matches,
        commits_match,
        |mut reply| {
            let observation = reply
                .as_object_mut()
                .and_then(|v| v.remove("git_facts"))
                .filter(|v| !v.is_null());
            let result = match observation {
                Some(extra) => observations.record(reader, extra),
                None => Ok(()),
            };
            (reply, result)
        },
        |reply| {
            if let Some(error) = reply.get("error") {
                return Err(error
                    .as_str()
                    .ok_or("invalid project registration error")?
                    .into());
            }
            let registry: Registry = serde_json::from_value(reply).map_err(|e| e.to_string())?;
            registry.validate_documents()?;
            Ok(registry)
        },
    )
}
