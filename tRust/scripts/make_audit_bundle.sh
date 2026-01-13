#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_DIR="${1:-"$ROOT_DIR/dist"}"

mkdir -p "$OUT_DIR"

GIT_SHA_SHORT="$(git -C "$ROOT_DIR" rev-parse --short HEAD 2>/dev/null || echo unknown)"
GIT_SHA_FULL="$(git -C "$ROOT_DIR" rev-parse HEAD 2>/dev/null || echo unknown)"
DATE_UTC="$(date -u +%Y-%m-%d)"

BUNDLE_NAME="tRust-audit-${DATE_UTC}-${GIT_SHA_SHORT}"
TMP_DIR="$(mktemp -d "${TMPDIR:-/tmp}/trust_audit_bundle.XXXXXX")"
trap 'rm -rf "$TMP_DIR"' EXIT

BUNDLE_ROOT="$TMP_DIR/$BUNDLE_NAME"
mkdir -p "$BUNDLE_ROOT"

copy_file() {
  local src="$1"
  local dst="$2"

  mkdir -p "$(dirname "$dst")"
  cp -p "$src" "$dst"
}

copy_tree_excluding_dotlake() {
  local src_dir="$1"
  local dst_dir="$2"

  mkdir -p "$dst_dir"
  if command -v rsync >/dev/null 2>&1; then
    rsync -a --delete --exclude "/.lake/" "$src_dir/" "$dst_dir/"
  else
    (cd "$src_dir" && find . -type d -name ".lake" -prune -o -type f -print) | while IFS= read -r rel; do
      mkdir -p "$dst_dir/$(dirname "$rel")"
      cp -p "$src_dir/$rel" "$dst_dir/$rel"
    done
  fi
}

checksum_cmd() {
  if command -v sha256sum >/dev/null 2>&1; then
    echo "sha256sum"
  elif command -v shasum >/dev/null 2>&1; then
    echo "shasum -a 256"
  else
    echo ""
  fi
}

CHECKSUM_CMD="$(checksum_cmd)"
if [[ -z "$CHECKSUM_CMD" ]]; then
  echo "error: need sha256sum (linux) or shasum (macOS)" >&2
  exit 1
fi

cat >"$BUNDLE_ROOT/MANIFEST.txt" <<EOF
tRust External Audit Bundle

Date (UTC): $DATE_UTC
Git commit: $GIT_SHA_FULL

Included:
- docs/design/AUDIT_OVERVIEW.md
- docs/design/VERIFICATION_SEMANTICS.md
- docs/design/COMPILER_COMPARISON.md
- proofs/lean5/* (excluding proofs/lean5/.lake)

Build proofs:
  cd proofs/lean5 && lake update && lake build
EOF

copy_file "$ROOT_DIR/docs/design/AUDIT_OVERVIEW.md" "$BUNDLE_ROOT/docs/design/AUDIT_OVERVIEW.md"
copy_file "$ROOT_DIR/docs/design/VERIFICATION_SEMANTICS.md" "$BUNDLE_ROOT/docs/design/VERIFICATION_SEMANTICS.md"
copy_file "$ROOT_DIR/docs/design/COMPILER_COMPARISON.md" "$BUNDLE_ROOT/docs/design/COMPILER_COMPARISON.md"

copy_tree_excluding_dotlake "$ROOT_DIR/proofs/lean5" "$BUNDLE_ROOT/proofs/lean5"

(cd "$BUNDLE_ROOT" && LC_ALL=C find . -type f ! -name "SHA256SUMS" -print | LC_ALL=C sort | while IFS= read -r f; do
  bash -c "$CHECKSUM_CMD \"\$1\"" _ "$f"
done) >"$BUNDLE_ROOT/SHA256SUMS"

ARCHIVE_PATH="$OUT_DIR/tRust_audit_bundle_${DATE_UTC}_${GIT_SHA_SHORT}.tar.gz"
tar -C "$TMP_DIR" -czf "$ARCHIVE_PATH" "$BUNDLE_NAME"

bash -c "$CHECKSUM_CMD \"\$1\"" _ "$ARCHIVE_PATH" >"${ARCHIVE_PATH}.sha256"

echo "wrote: $ARCHIVE_PATH"
echo "wrote: ${ARCHIVE_PATH}.sha256"
