#!/usr/bin/env bash
#
# Level 2 Validation: Crate ecosystem compatibility smoke runner.
#
# This script builds temporary Cargo projects that depend on selected crates,
# using `cargo trust build --no-verify` (tRust compiler, verification disabled).
#
# Logs: reports/validation/level2_logs/<crate>.log
#
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
LOG_DIR="$ROOT/reports/validation/level2_logs"

export PATH="$ROOT/bin:$PATH"
mkdir -p "$LOG_DIR"

usage() {
  cat <<'EOF'
Usage:
  tools/validation/run_level2_crate_compat.sh [--crates a,b,c] [--keep-workdir]

Defaults:
  Runs the Level 2 Tier-1 list from VALIDATION_PLAN.md.
EOF
}

KEEP_WORKDIR=0
CRATES_CSV=""

while [[ $# -gt 0 ]]; do
  case "$1" in
    --crates)
      shift
      CRATES_CSV="${1:-}"
      shift || true
      ;;
    --crates=*)
      CRATES_CSV="${1#*=}"
      shift
      ;;
    --keep-workdir)
      KEEP_WORKDIR=1
      shift
      ;;
    --help|-h)
      usage
      exit 0
      ;;
    *)
      echo "error: unknown argument: $1" >&2
      usage >&2
      exit 2
      ;;
  esac
done

default_crates=(
  serde
  tokio
  rand
  syn
  quote
  proc-macro2
  clap
  regex
  log
  thiserror
)

CRATES=()
if [[ -n "$CRATES_CSV" ]]; then
  IFS=',' read -r -a CRATES <<<"$CRATES_CSV"
else
  CRATES=("${default_crates[@]}")
fi

dependency_spec() {
  local crate="$1"
  case "$crate" in
    serde)
      echo 'serde = { version = "1", features = ["derive"] }'
      ;;
    tokio)
      echo 'tokio = { version = "1", features = ["macros", "rt-multi-thread"] }'
      ;;
    rand)
      echo 'rand = "0.8"'
      ;;
    syn)
      echo 'syn = "2"'
      ;;
    quote)
      echo 'quote = "1"'
      ;;
    proc-macro2)
      echo 'proc-macro2 = "1"'
      ;;
    clap)
      echo 'clap = { version = "4", features = ["derive"] }'
      ;;
    regex)
      echo 'regex = "1"'
      ;;
    log)
      echo 'log = "0.4"'
      ;;
    thiserror)
      echo 'thiserror = "2"'
      ;;
    # Tier 2 crates
    hyper)
      echo 'hyper = { version = "1", features = ["full"] }'
      ;;
    reqwest)
      echo 'reqwest = { version = "0.12", features = ["json"] }'
      ;;
    actix-web)
      echo 'actix-web = "4"'
      ;;
    diesel)
      echo 'diesel = { version = "2", features = ["sqlite"] }'
      ;;
    sqlx)
      echo 'sqlx = { version = "0.8", features = ["runtime-tokio", "sqlite"] }'
      ;;
    tracing)
      echo 'tracing = "0.1"'
      ;;
    bytes)
      echo 'bytes = "1"'
      ;;
    futures)
      echo 'futures = "0.3"'
      ;;
    crossbeam)
      echo 'crossbeam = "0.8"'
      ;;
    rayon)
      echo 'rayon = "1"'
      ;;
    # Tier 3 crates (top 100)
    hashbrown)
      echo 'hashbrown = "0.15"'
      ;;
    bitflags)
      echo 'bitflags = "2"'
      ;;
    libc)
      echo 'libc = "0.2"'
      ;;
    base64)
      echo 'base64 = "0.22"'
      ;;
    getrandom)
      echo 'getrandom = "0.2"'
      ;;
    rand_core)
      echo 'rand_core = "0.6"'
      ;;
    regex-syntax)
      echo 'regex-syntax = "0.8"'
      ;;
    indexmap)
      echo 'indexmap = "2"'
      ;;
    itertools)
      echo 'itertools = "0.13"'
      ;;
    cfg-if)
      echo 'cfg-if = "1"'
      ;;
    autocfg)
      echo 'autocfg = "1"'
      ;;
    memchr)
      echo 'memchr = "2"'
      ;;
    rand_chacha)
      echo 'rand_chacha = "0.3"'
      ;;
    itoa)
      echo 'itoa = "1"'
      ;;
    unicode-ident)
      echo 'unicode-ident = "1"'
      ;;
    serde_json)
      echo 'serde_json = "1"'
      ;;
    heck)
      echo 'heck = "0.5"'
      ;;
    regex-automata)
      echo 'regex-automata = "0.4"'
      ;;
    once_cell)
      echo 'once_cell = "1"'
      ;;
    cc)
      echo 'cc = "1"'
      ;;
    ryu)
      echo 'ryu = "1"'
      ;;
    aho-corasick)
      echo 'aho-corasick = "1"'
      ;;
    smallvec)
      echo 'smallvec = "1"'
      ;;
    strsim)
      echo 'strsim = "0.11"'
      ;;
    socket2)
      echo 'socket2 = "0.5"'
      ;;
    lazy_static)
      echo 'lazy_static = "1"'
      ;;
    num-traits)
      echo 'num-traits = "0.2"'
      ;;
    version_check)
      echo 'version_check = "0.9"'
      ;;
    either)
      echo 'either = "1"'
      ;;
    semver)
      echo 'semver = "1"'
      ;;
    idna)
      echo 'idna = "1"'
      ;;
    lock_api)
      echo 'lock_api = "0.4"'
      ;;
    digest)
      echo 'digest = "0.10"'
      ;;
    mio)
      echo 'mio = { version = "1", features = ["os-poll", "net"] }'
      ;;
    time)
      echo 'time = { version = "0.3", features = ["macros"] }'
      ;;
    pin-project-lite)
      echo 'pin-project-lite = "0.2"'
      ;;
    scopeguard)
      echo 'scopeguard = "1"'
      ;;
    anyhow)
      echo 'anyhow = "1"'
      ;;
    http)
      echo 'http = "1"'
      ;;
    miniz_oxide)
      echo 'miniz_oxide = "0.8"'
      ;;
    block-buffer)
      echo 'block-buffer = "0.10"'
      ;;
    ppv-lite86)
      echo 'ppv-lite86 = "0.2"'
      ;;
    percent-encoding)
      echo 'percent-encoding = "2"'
      ;;
    fastrand)
      echo 'fastrand = "2"'
      ;;
    url)
      echo 'url = "2"'
      ;;
    toml)
      echo 'toml = "0.8"'
      ;;
    memoffset)
      echo 'memoffset = "0.9"'
      ;;
    rustls)
      echo 'rustls = "0.23"'
      ;;
    byteorder)
      echo 'byteorder = "1"'
      ;;
    slab)
      echo 'slab = "0.4"'
      ;;
    generic-array)
      echo 'generic-array = "0.14"'
      ;;
    futures-core)
      echo 'futures-core = "0.3"'
      ;;
    futures-util)
      echo 'futures-util = "0.3"'
      ;;
    http-body)
      echo 'http-body = "1"'
      ;;
    futures-task)
      echo 'futures-task = "0.3"'
      ;;
    tracing-core)
      echo 'tracing-core = "0.1"'
      ;;
    sha2)
      echo 'sha2 = "0.10"'
      ;;
    ahash)
      echo 'ahash = "0.8"'
      ;;
    chrono)
      echo 'chrono = "0.4"'
      ;;
    futures-sink)
      echo 'futures-sink = "0.3"'
      ;;
    typenum)
      echo 'typenum = "1"'
      ;;
    h2)
      echo 'h2 = "0.4"'
      ;;
    fnv)
      echo 'fnv = "1"'
      ;;
    unicode-width)
      echo 'unicode-width = "0.2"'
      ;;
    futures-channel)
      echo 'futures-channel = "0.3"'
      ;;
    clap_lex)
      echo 'clap_lex = "0.7"'
      ;;
    tempfile)
      echo 'tempfile = "3"'
      ;;
    pin-utils)
      echo 'pin-utils = "0.1"'
      ;;
    tokio-util)
      echo 'tokio-util = "0.7"'
      ;;
    uuid)
      echo 'uuid = { version = "1", features = ["v4"] }'
      ;;
    futures-io)
      echo 'futures-io = "0.3"'
      ;;
    parking_lot)
      echo 'parking_lot = "0.12"'
      ;;
    parking_lot_core)
      echo 'parking_lot_core = "0.9"'
      ;;
    rustix)
      echo 'rustix = { version = "0.38", features = ["fs"] }'
      ;;
    linux-raw-sys)
      echo 'linux-raw-sys = "0.4"'
      ;;
    *)
      echo "${crate} = \"*\""
      ;;
  esac
}

extract_locked_version() {
  local lockfile="$1"
  local crate="$2"
  if [[ ! -f "$lockfile" ]]; then
    return 0
  fi

  awk -v crate="$crate" '
    $1 == "name" && $3 == "\""crate"\"" { in_pkg=1; next }
    in_pkg && $1 == "version" { gsub(/"/, "", $3); print $3; exit }
    $0 == "" { in_pkg=0 }
  ' "$lockfile" 2>/dev/null || true
}

run_one() {
  local crate="$1"
  local log_file="$LOG_DIR/${crate}.log"

  local workdir
  workdir="$(mktemp -d "${TMPDIR:-/tmp}/trust_level2_${crate}_XXXXXX")"

  mkdir -p "$workdir/src"
  cat >"$workdir/Cargo.toml" <<EOF
[package]
name = "trust_level2_${crate//-/_}"
version = "0.1.0"
edition = "2021"

[dependencies]
$(dependency_spec "$crate")
EOF

  cat >"$workdir/src/main.rs" <<'EOF'
fn main() {}
EOF

  local status="PASS"
  (
    cd "$workdir"
    cargo trust build --no-verify
  ) >"$log_file" 2>&1 || status="FAIL"

  local locked_version
  locked_version="$(extract_locked_version "$workdir/Cargo.lock" "$crate")"

  if [[ "$KEEP_WORKDIR" -eq 0 ]]; then
    rm -rf "$workdir"
  else
    {
      echo
      echo "[debug] kept workdir: $workdir"
    } >>"$log_file"
  fi

  printf "%-14s %-6s %s\n" "$crate" "$status" "${locked_version:-unknown}"
}

echo "crate           status version"
echo "------------------------------"
for crate in "${CRATES[@]}"; do
  run_one "$crate"
done
