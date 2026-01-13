#!/usr/bin/env bash
set -euo pipefail

# Cargo invokes RUSTC_WORKSPACE_WRAPPER as:
#   <wrapper> <rustc> [rustc args...]
#
# We disable verification for dependencies, and enable `cfg(trust_verify)` only for this crate.

RUSTC_BIN="${1:?missing rustc path}"
shift

CRATE_NAME=""
CRATE_TYPES=()
ARGS=("$@")

STAGE1_RUSTC=""
if [[ "$(basename "$RUSTC_BIN")" == "trustc" ]]; then
  TRUST_ROOT="$(cd "$(dirname "$RUSTC_BIN")/.." && pwd)"
  STAGE1_RUSTC="$TRUST_ROOT/build/host/stage1/bin/rustc"
fi

for ((i = 0; i < ${#ARGS[@]}; i++)); do
  case "${ARGS[$i]}" in
    --crate-name)
      CRATE_NAME="${ARGS[$((i + 1))]:-}"
      ;;
    --crate-name=*)
      CRATE_NAME="${ARGS[$i]#--crate-name=}"
      ;;
    --crate-type)
      CRATE_TYPES+=("${ARGS[$((i + 1))]:-}")
      ;;
  esac
done

if [[ "$CRATE_NAME" == "rustc_index_verified" ]]; then
  # Enable specs: all verification attributes are behind `cfg(trust_verify)`.
  exec "$RUSTC_BIN" "${ARGS[@]}" --cfg trust_verify
else
  # Avoid running trustc for dependencies/version probes when possible.
  # This keeps verification scoped to this crate and prevents trustc from
  # interfering with cargo's rustc version probing.
  if [[ -n "$STAGE1_RUSTC" && -x "$STAGE1_RUSTC" ]]; then
    exec "$STAGE1_RUSTC" "${ARGS[@]}"
  else
    # Fallback: disable verification for dependencies (trustc enables it by default).
    exec "$RUSTC_BIN" --no-verify "${ARGS[@]}"
  fi
fi
