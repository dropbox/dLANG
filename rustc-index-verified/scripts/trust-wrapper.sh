#!/usr/bin/env bash
set -euo pipefail

# RUSTC_WRAPPER for trustc that enables verification only for rustc_index_verified
#
# Cargo invokes RUSTC_WRAPPER as:
#   <wrapper> <rustc> [rustc args...]
#
# We enable trust_verify config only for our crate, and disable verification for all others.

RUSTC_BIN="${1:?missing rustc path}"
shift

CRATE_NAME=""
ARGS=("$@")

STAGE1_RUSTC=""
if [[ "$(basename "$RUSTC_BIN")" == "trustc" ]]; then
  TRUST_ROOT="$(cd "$(dirname "$RUSTC_BIN")/.." && pwd)"
  STAGE1_RUSTC="$TRUST_ROOT/build/host/stage1/bin/rustc"
fi

# Parse args to find crate name
for ((i = 0; i < ${#ARGS[@]}; i++)); do
  case "${ARGS[$i]}" in
    --crate-name)
      CRATE_NAME="${ARGS[$((i + 1))]:-}"
      ;;
    --crate-name=*)
      CRATE_NAME="${ARGS[$i]#--crate-name=}"
      ;;
  esac
done

if [[ "$CRATE_NAME" == "rustc_index_verified" ]]; then
  # Enable verification and trust_verify config for our crate
  exec "$RUSTC_BIN" "${ARGS[@]}" --cfg trust_verify
else
  # Avoid running trustc for dependencies/version probes when possible.
  if [[ -n "$STAGE1_RUSTC" && -x "$STAGE1_RUSTC" ]]; then
    exec "$STAGE1_RUSTC" "${ARGS[@]}"
  else
    # Fallback: disable verification for dependencies (trustc enables it by default)
    exec "$RUSTC_BIN" --no-verify "${ARGS[@]}"
  fi
fi
