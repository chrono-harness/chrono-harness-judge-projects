//! 独立预期直接消费实际语言配对源码；不按语言名或文件扩展名推断。
#![allow(unexpected_cfgs)]
#[path = "../../judge-projects/src/verified_languages.rs"]
mod languages;
#[cfg(not(verus_keep_ghost))]
use vstd::prelude::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::vpanic as panic;

verus! {

pub struct PairRows<'a> { pub rows: &'a [(Option<&'a str>, Option<&'a str>)] }
impl<'a> languages::PairTable for PairRows<'a> {
    open spec fn size(&self) -> nat { self.rows@.len() }
    open spec fn target(&self, i: int, forward: bool) -> Option<Seq<char>> {
        languages::text(if forward { self.rows@[i].0 } else { self.rows@[i].1 })
    }
    fn len(&self) -> usize { self.rows.len() }
    fn link(&self,i: usize,forward: bool) -> Option<&str> {
        if forward { self.rows[i].0 } else { self.rows[i].1 }
    }
}

fn expect_pair(b: bool) requires b { if !b { panic!(); } }

#[cfg_attr(not(verus_keep_ghost), test)]
fn a_dedicated_pair_has_exactly_one_link_each_way_and_project_kinds() {
    proof {
        reveal_strlit("p"); reveal_strlit("t");
        assert("p"@[0]=='p' && "t"@[0]=='t');
        reveal_strlit("production"); reveal_strlit("test");
        assert("production"@.len()!="test"@.len());
        reveal_with_fuel(languages::claims,4);
    }
    let rows=[(Some("t"),None),(None,Some("p"))];
    let table=PairRows{rows:&rows};
    expect_pair(languages::dedicated_pair(&table,"project","p","t",Some("t"),Some("p"),Some("production"),Some("test")));
    expect_pair(!languages::dedicated_pair(&table,"project","p","t",Some("t"),None,Some("production"),Some("test")));
    expect_pair(!languages::dedicated_pair(&table,"project","p","p",Some("p"),Some("p"),Some("production"),Some("test")));
    expect_pair(!languages::dedicated_pair(&table,"project","p","t",Some("t"),Some("p"),Some("test"),Some("test")));
    let repeated=[(Some("t"),None),(None,Some("p")),(Some("t"),None)];
    let shared=PairRows{rows:&repeated};
    expect_pair(!languages::dedicated_pair(&shared,"project","p","t",Some("t"),Some("p"),Some("production"),Some("test")));
}

// 任意完整字符串相等都接受；非空约束由登记 schema 的既有所有者负责。
#[cfg(verus_keep_ghost)]
fn equal_languages_are_allowed(language: &str) {
    let accepted = languages::dedicated_test_language(language, language);
    assert(accepted);
}

#[cfg(verus_keep_ghost)]
fn different_languages_need_the_exact_directional_exception(implementation: &str, testing: &str)
    requires implementation@ != testing@,
        implementation@ != "shell"@ || testing@ != "python"@,
{
    let accepted = languages::dedicated_test_language(implementation, testing);
    assert(!accepted);
}

#[cfg_attr(not(verus_keep_ghost), test)]
fn exact_shell_python_exception_is_directional() {
    proof {
        reveal_strlit("shell"); reveal_strlit("python");
        assert("shell"@.len() != "python"@.len());
    }
    let allowed = languages::dedicated_test_language("shell", "python");
    assert(allowed);
    let reversed = languages::dedicated_test_language("python", "shell");
    assert(!reversed);
}

#[cfg_attr(not(verus_keep_ghost), test)]
fn actual_languages_require_complete_case_sensitive_identity() {
    proof {
        reveal_strlit("rust"); reveal_strlit("Rust"); reveal_strlit("go");
        reveal_strlit("typescript"); reveal_strlit("python"); reveal_strlit("shell");
        assert("rust"@[0] != "Rust"@[0]);
        assert("rust"@.len() != "shell"@.len());
        assert("rust"@.len() != "go"@.len());
        assert("typescript"@.len() != "python"@.len());
        assert("typescript"@.len() != "shell"@.len());
    }
    let rust = languages::dedicated_test_language("rust", "rust");
    assert(rust);
    let case = languages::dedicated_test_language("rust", "Rust");
    assert(!case);
    let mismatch = languages::dedicated_test_language("rust", "go");
    assert(!mismatch);
    let no_general_python_exception = languages::dedicated_test_language("typescript", "python");
    assert(!no_general_python_exception);
}

#[cfg_attr(not(verus_keep_ghost), test)]
fn exception_does_not_normalize_case_prefix_nul_or_unicode() {
    proof {
        reveal_strlit("shell"); reveal_strlit("python"); reveal_strlit("Shell");
        reveal_strlit("Python"); reveal_strlit("shell\0"); reveal_strlit("python\0");
        reveal_strlit("shell "); reveal_strlit("python3"); reveal_strlit("壳");
        assert("shell"@.len() != "python"@.len());
        assert("Shell"@.len() != "python"@.len());
        assert("shell"@[0] != "Shell"@[0]);
        assert("shell"@.len() != "Python"@.len());
        assert("python"@[0] != "Python"@[0]);
        assert("shell\0"@[0] != "python"@[0]);
        assert("shell"@.len() != "shell\0"@.len());
        assert("shell"@.len() != "python\0"@.len());
        assert("python"@.len() != "python\0"@.len());
        assert("shell "@[0] != "python"@[0]);
        assert("shell"@.len() != "shell "@.len());
        assert("shell"@.len() != "python3"@.len());
        assert("python"@.len() != "python3"@.len());
        assert("壳"@.len() != "shell"@.len());
        assert("壳"@.len() != "python"@.len());
    }
    let implementation_case = languages::dedicated_test_language("Shell", "python");
    assert(!implementation_case);
    let testing_case = languages::dedicated_test_language("shell", "Python");
    assert(!testing_case);
    let implementation_nul = languages::dedicated_test_language("shell\0", "python");
    assert(!implementation_nul);
    let testing_nul = languages::dedicated_test_language("shell", "python\0");
    assert(!testing_nul);
    let space = languages::dedicated_test_language("shell ", "python");
    assert(!space);
    let suffix = languages::dedicated_test_language("shell", "python3");
    assert(!suffix);
    let unicode = languages::dedicated_test_language("壳", "python");
    assert(!unicode);
}

#[cfg_attr(not(verus_keep_ghost), test)]
fn equality_keeps_arbitrary_unicode_and_nul_text() {
    proof {
        reveal_strlit(""); reveal_strlit("语言"); reveal_strlit("语言\0");
        reveal_strlit("shell");
        assert("语言"@.len() != "语言\0"@.len());
        assert("语言"@.len() != "shell"@.len());
    }
    let empty = languages::dedicated_test_language("", "");
    assert(empty);
    let unicode = languages::dedicated_test_language("语言", "语言");
    assert(unicode);
    let nul = languages::dedicated_test_language("语言\0", "语言\0");
    assert(nul);
    let different = languages::dedicated_test_language("语言", "语言\0");
    assert(!different);
}

fn version_one_preserves_pairs_without_language_fields() {
    let accepted = languages::registered_test_language(Some(1), None, None);
    assert(accepted);
}

fn version_two_requires_both_fields(implementation: &str, testing: &str) {
    let missing_test = languages::registered_test_language(Some(2), Some(implementation), None);
    let missing_product = languages::registered_test_language(Some(2), None, Some(testing));
    assert(!missing_test && !missing_product);
}

fn version_two_checks_the_declared_pair(implementation: &str, testing: &str) {
    let accepted = languages::registered_test_language(Some(2), Some(implementation), Some(testing));
    assert(accepted == (implementation@ == testing@ ||
        implementation@ == "shell"@ && testing@ == "python"@));
}

fn unsupported_versions_cannot_disable_language_admission(version: u64, language: &str)
    requires version != 1, version != 2,
{
    let absent = languages::registered_test_language(None, Some(language), Some(language));
    let unknown = languages::registered_test_language(Some(version), Some(language), Some(language));
    assert(!absent && !unknown);
}

}
