//! Observe both endpoints and both working-tree checks through the same installed Git reader.
use crate::runtime_session::Session;
use crate::wire::Request;
use serde::Deserialize;
use serde_json::{Value, json};
use std::collections::BTreeMap;

#[derive(Deserialize)]
pub(crate) struct Snapshot {
    pub values: BTreeMap<String, Value>,
    pub originals: BTreeMap<String, String>,
    pub effective_path: String,
}

pub(crate) struct Reader {
    session: Session,
    pub bound: bool,
}
impl Reader {
    pub fn open(request: &Request) -> Result<Self, String> {
        let root = &request.candidate.root;
        let program = chrono_harness::resolve_program(root, &request.runner.path, None)?;
        if chrono_harness::file_identity(&program)?.0 != request.runner.sha256 {
            return Err("E_TOOL_BINDING: runner executable changed".into());
        }
        let mut session = Session::open(root, &program, "git-facts-v1")?;
        #[derive(Deserialize)]
        struct Opened {
            bound: bool,
        }
        let bound = session
            .call::<Opened>(json!({"mode":"request","request":request}))?
            .bound;
        Ok(Self { session, bound })
    }
    pub fn snapshot(&mut self, endpoint: &str) -> Result<Snapshot, String> {
        self.session
            .call(json!({"op":"registry-snapshot","endpoint":endpoint}))
    }
    pub fn checkout(&mut self, artifacts: &[String]) -> Result<Checkout, String> {
        self.session
            .call(json!({"op":"checkout-excluding","artifacts":artifacts}))
    }
    pub fn observation(&mut self) -> Result<Value, String> {
        self.session.call(json!({"op":"observation"}))
    }
    pub fn close(self) -> Result<(), String> {
        self.session.close()
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
