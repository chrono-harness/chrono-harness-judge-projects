#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
if [[ $# -eq 0 ]]; then
  /bin/sh .chrono-harness/ci/install.sh
  export PATH="$PWD/.chrono-harness/bin:$PATH"
  export CHRONO_CHECK_SOURCE=${CHRONO_CHECK_SOURCE:-local}
  exec .chrono-harness/bin/chrono-harness check
fi
if [[ $# == 1 && $1 == --native ]]; then
  exec chrono-host-bootstrap native-scratch run /bin/bash ./check.sh --native-in-directory
fi
if [[ $# -ne 1 || $1 != --native-in-directory ]]; then
  echo 'usage: ./check.sh [--native]' >&2
  exit 2
fi
scratch=${CHRONO_NATIVE_SCRATCH:?missing native check directory}
export TMPDIR="$scratch"
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$scratch/cargo}"
cargo fmt --check --manifest-path crates/judge-projects/Cargo.toml
product=crates/judge-projects/Cargo.toml
cargo build --locked --message-format=json-render-diagnostics --manifest-path "$product" > "$scratch/build.jsonl"
cargo fmt --check --manifest-path crates/judge-projects-tests/Cargo.toml
cargo test --color never --locked --manifest-path crates/judge-projects-tests/Cargo.toml -- --format pretty | tee "$scratch/tests.log"
coverage_failure() {
  echo "E_VERUS_COVERAGE: $*" >&2
  exit 1
}

for consumer in result_queries_keep_the_native_wire_shape_and_outcome incomplete_collection_query_is_rejected_before_reading_the_checkout; do
  grep -Fxq "test $consumer ... ok" "$scratch/tests.log" ||
    coverage_failure "required evidence consumer did not execute: $consumer"
done

# Read the exact library selected by Cargo in the build of the tested executable.
metadata=$(jq -ers --arg manifest "$(pwd -P)/$product" '
  [.[] | select(.reason == "compiler-artifact" and .manifest_path == $manifest
                 and .target.kind == ["lib"]) | .filenames[] | select(endswith(".rmeta"))]
  | if length == 1 then .[0] else error("expected the product library") end
' "$scratch/build.jsonl") || coverage_failure "native library was not identified"
filename=${metadata##*/}
stem=${filename#lib}
stem=${metadata%/*}/${stem%.rmeta}
chrono-host-bootstrap check-compiler-sources native "$stem" src/lib.rs src/evidence_query.rs src/verified_languages.rs src/pair_checks.rs src/verified_state.rs src/state.rs src/routes.rs ||
  coverage_failure "native library differs from required sources"
