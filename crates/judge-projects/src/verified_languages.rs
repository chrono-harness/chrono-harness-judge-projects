//! 专属测试的语言配对；直接消费登记中的完整文本。
#![allow(unexpected_cfgs)]
#[cfg(not(verus_keep_ghost))]
use vstd::prelude::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

use vstd::contrib::exec_spec::ExecSpecEq;

verus! {

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
