//! 专属测试的语言配对；直接消费登记中的完整文本。
#![allow(unexpected_cfgs)]
#[cfg(not(verus_keep_ghost))]
use vstd::prelude::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

use vstd::contrib::exec_spec::ExecSpecEq;

verus! {

/// Pair links are supplied by the registry's decoded project or script rows.
pub trait PairTable {
    spec fn size(&self) -> nat;
    spec fn target(&self, index: int, forward: bool) -> Option<Seq<char>>;
    fn len(&self) -> (n: usize) ensures n == self.size();
    fn link(&self, index: usize, forward: bool) -> (v: Option<&str>)
        requires index < self.size(),
        ensures self.target(index as int,forward) == text(v);
}

pub open spec fn text(v: Option<&str>) -> Option<Seq<char>> {
    match v { Some(s) => Some(s@), None => None }
}

pub open spec fn claims<T: PairTable>(table: &T, n: nat, key: Seq<char>, forward: bool) -> nat
    decreases n,
{
    if n == 0 { 0 } else {
        claims(table,(n-1) as nat,key,forward) +
            if table.target(n-1,forward) == Some(key) { 1nat } else { 0nat }
    }
}

fn equals_option(v: Option<&str>, expected: &str) -> (matches: bool)
    ensures matches == (text(v) == Some(expected@)),
{
    match v { Some(s) => <&str>::exec_eq(s, expected), None => false }
}

fn unique_link<T: PairTable>(table: &T, key: &str, forward: bool) -> (unique: bool)
    ensures unique == (claims(table,table.size(),key@,forward) == 1),
{
    let n=table.len();
    let mut i=0;
    let mut count=0usize;
    while i<n
        invariant i<=n, n==table.size(), count<=i, count==claims(table,i as nat,key@,forward),
        decreases n-i,
    {
        if equals_option(table.link(i,forward),key) { count+=1; }
        i+=1;
    }
    count==1
}

pub fn dedicated_pair<T: PairTable>(table: &T, prefix: &str, prod: &str, test: &str,
    prod_link: Option<&str>, test_link: Option<&str>, prod_kind: Option<&str>, test_kind: Option<&str>)
    -> (valid: bool)
    ensures valid == (text(prod_link) == Some(test@) && text(test_link) == Some(prod@) && prod@ != test@ &&
        claims(table,table.size(),test@,true)==1 && claims(table,table.size(),prod@,false)==1 &&
        (prefix@ != "project"@ || (text(prod_kind)==Some("production"@) && text(test_kind)==Some("test"@)))),
{
    equals_option(prod_link,test) && equals_option(test_link,prod) && !<&str>::exec_eq(prod,test)
        && unique_link(table,test,true) && unique_link(table,prod,false)
        && (!<&str>::exec_eq(prefix,"project") ||
            (equals_option(prod_kind,"production") && equals_option(test_kind,"test")))
}

pub open spec fn language_pair(implementation: Seq<char>, testing: Seq<char>) -> bool {
    implementation == testing || implementation == "shell"@ && testing == "python"@
}

pub fn dedicated_test_language(implementation: &str, testing: &str) -> (accepted: bool)
    ensures accepted == language_pair(implementation@, testing@),
{
    <&str>::exec_eq(implementation, testing)
        || <&str>::exec_eq(implementation, "shell")
            && <&str>::exec_eq(testing, "python")
}

}
