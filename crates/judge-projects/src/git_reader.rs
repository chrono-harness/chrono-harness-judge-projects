//! Observe both endpoints and both working-tree checks through the same installed Git reader.
#![allow(unexpected_cfgs)]
use vstd::contrib::exec_spec::ExecSpecEq;
#[cfg(not(verus_keep_ghost))]
use vstd::prelude::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

verus! {
/// A session can open only after the on-disk executable matches the requested digest.
pub fn open_bound_reader<T, F>(observed: Result<String, String>, required: &str, open: F)
    -> (out: Result<T, String>)
    where F: FnOnce() -> Result<T, String>,
    requires (observed matches Ok(digest) && digest@ == required@) ==> open.requires(()),
    ensures match observed {
        Err(error) => out == Err::<T, String>(error),
        Ok(digest) if digest@ == required@ => open.ensures((), out),
        Ok(_) => out matches Err(error) && error@ == "E_TOOL_BINDING: runner executable changed"@,
    },
{
    let digest = match observed { Ok(digest) => digest, Err(error) => return Err(error) };
    if <&str>::exec_eq(digest.as_str(), required) {
        open()
    } else {
        Err("E_TOOL_BINDING: runner executable changed".to_string())
    }
}
}

#[cfg(not(verus_keep_ghost))]
use crate::runtime_session::Session;
#[cfg(not(verus_keep_ghost))]
use crate::wire::Request;
#[cfg(not(verus_keep_ghost))]
use serde::Deserialize;
#[cfg(not(verus_keep_ghost))]
use serde_json::{Value, json};
#[cfg(not(verus_keep_ghost))]
use std::collections::BTreeMap;

#[cfg(not(verus_keep_ghost))]
#[derive(Deserialize)]
pub(crate) struct Snapshot {
    pub values: BTreeMap<String, Value>,
    pub originals: BTreeMap<String, String>,
    pub effective_path: String,
}

#[cfg(not(verus_keep_ghost))]
pub(crate) struct Reader {
    session: Session,
    pub bound: bool,
}
#[cfg(not(verus_keep_ghost))]
impl Reader {
    pub fn open(request: &Request) -> Result<Self, String> {
        let root = &request.candidate.root;
        let program = crate::wire::resolve_program(root, &request.runner.path, None)?;
        let observed = crate::wire::file_identity(&program).map(|(sha256, _)| sha256);
        open_bound_reader(observed, &request.runner.sha256, || {
            let mut session = Session::open(root, &program, "git-facts-v1")?;
            #[derive(Deserialize)]
            struct Opened {
                bound: bool,
            }
            let bound = session
                .call::<Opened>(json!({"mode":"request","request":request}))?
                .bound;
            Ok(Self { session, bound })
        })
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

#[cfg(not(verus_keep_ghost))]
#[derive(Deserialize)]
pub(crate) struct Checkout {
    pub head: String,
    pub tracked: Vec<String>,
    pub untracked: Vec<String>,
    pub index_flags: Vec<IndexFlag>,
}

#[cfg(not(verus_keep_ghost))]
#[derive(Deserialize)]
pub(crate) struct IndexFlag {
    pub tag: String,
}
