#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p target
scratch=$(mktemp -d "$(pwd -P)/target/check.XXXXXXXX")
trap 'rm -rf -- "$scratch"' EXIT
export TMPDIR="$scratch"
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$scratch/cargo}"
cargo fmt --check --manifest-path crates/judge-projects/Cargo.toml
product=crates/judge-projects/Cargo.toml
cargo build --locked --message-format=json-render-diagnostics --manifest-path "$product" > "$scratch/build.jsonl"
cargo fmt --check --manifest-path crates/judge-projects-tests/Cargo.toml
cargo test --locked --manifest-path crates/judge-projects-tests/Cargo.toml
coverage_failure() {
  echo "E_VERUS_COVERAGE: $*" >&2
  exit 1
}

verifier=$(command -v "${VERUS:-verus}") || coverage_failure "registered verifier was not found"

prove() {
  chrono-host-bootstrap run-compiler-proof "$scratch" "$1" "$verifier" "$2" ||
    coverage_failure "$1: verifier failed"
}

admit_proof() {
  local operation=$1
  shift
  chrono-host-bootstrap collect-compiler-proof "$scratch" "$operation" "$verifier" \
    0.2026.04.24.f8e1704 f8e17045c4ac17a02e566b8997070f2eecc255be "$@" ||
    coverage_failure "$operation: required proof result was not admitted"
}

# Read the exact library selected by Cargo in the build of the tested executable.
metadata=$(jq -ers --arg manifest "$(pwd -P)/$product" '
  [.[] | select(.reason == "compiler-artifact" and .manifest_path == $manifest
                 and .target.kind == ["lib"]) | .filenames[] | select(endswith(".rmeta"))]
  | if length == 1 then .[0] else error("expected the product library") end
' "$scratch/build.jsonl") || coverage_failure "native library was not identified"
filename=${metadata##*/}
stem=${filename#lib}
stem=${metadata%/*}/${stem%.rmeta}
chrono-host-bootstrap check-compiler-sources native "$stem" src/lib.rs src/evidence_query.rs src/verified_languages.rs src/pair_checks.rs src/verified_state.rs src/state.rs ||
  coverage_failure "native library differs from required sources"

src=crates/judge-projects/src
tests=crates/judge-projects-tests/tests
include=$tests/../../judge-projects/src
support=$tests/proof_support

language_operation=verify.project-languages
state_operation=verify.project-state
language_tests=verify.project-languages-tests
state_tests=verify.project-state-tests

prove "$language_operation" "$src/verified_languages.rs"
prove "$state_operation" "$src/verified_state.rs"
prove "$language_tests" "$tests/verified_languages.rs"
prove "$state_tests" "$tests/verified_state.rs"

admit_proof "$language_operation" "$src/verified_languages.rs"
admit_proof "$state_operation" "$src/verified_state.rs" "$src/state.rs"
admit_proof "$language_tests" "$tests/verified_languages.rs" "$include/verified_languages.rs"
admit_proof "$state_tests" "$tests/verified_state.rs" \
  "$support/judge-projects/support/host.rs" "$support/judge-projects/execution.rs" \
  "$support/judge-projects/support/failure_batch.rs" "$include/verified_state.rs" "$include/state.rs" \
  "$support/judge-routes/support/tool.rs"
