#!/usr/bin/env bash
set -euo pipefail

# Unset git environment variables that may be set during hooks (e.g., pre-commit)
# These can interfere with git commands run in submodules
unset GIT_INDEX_FILE GIT_DIR GIT_WORK_TREE GIT_PREFIX 2>/dev/null || true

QUIET=0
if [[ "${1:-}" == "--quiet" ]]; then
  QUIET=1
  shift
fi

TOPLEVEL="$(git rev-parse --show-toplevel)"
cd "$TOPLEVEL"

SUBMODULE_PATHS="$(git config -f .gitmodules --get-regexp '^submodule\..*\.path$' | awk '{print $2}' || true)"
if [[ -z "$SUBMODULE_PATHS" ]]; then
  exit 0
fi

fail() {
  echo "ERROR: $*" >&2
  exit 1
}

while IFS= read -r path; do
  if [[ ! -e "$path" ]]; then
    (( QUIET )) || echo "WARN: submodule path missing: $path (not initialized?)" >&2
    continue
  fi

  if ! git -C "$path" rev-parse --git-dir >/dev/null 2>&1; then
    (( QUIET )) || echo "WARN: not a git repo: $path (submodule not initialized?)" >&2
    continue
  fi

  if git -C "$path" remote get-url origin >/dev/null 2>&1; then
    git -C "$path" fetch -q origin
  else
    (( QUIET )) || echo "WARN: $path has no 'origin' remote; skipping push check" >&2
    continue
  fi

  default_remote_ref="$(git -C "$path" symbolic-ref -q --short refs/remotes/origin/HEAD || true)"
  if [[ -z "$default_remote_ref" ]]; then
    default_remote_ref="origin/main"
  fi

  if ! git -C "$path" show-ref --verify --quiet "refs/remotes/${default_remote_ref}"; then
    if git -C "$path" show-ref --verify --quiet "refs/remotes/origin/main"; then
      default_remote_ref="origin/main"
    else
      (( QUIET )) || echo "WARN: $path has no remote default branch ref; skipping push check" >&2
      continue
    fi
  fi

  ahead_count="$(git -C "$path" rev-list --count "${default_remote_ref}..HEAD")"
  if [[ "$ahead_count" != "0" ]]; then
    default_branch="${default_remote_ref#origin/}"
    echo "ERROR: submodule '$path' has $ahead_count unpushed commit(s) (HEAD is ahead of ${default_remote_ref})." >&2
    git -C "$path" log --oneline --decorate "${default_remote_ref}..HEAD" >&2
    echo "To fix: git -C '$path' push origin '$default_branch'" >&2
    exit 1
  fi
done <<< "$SUBMODULE_PATHS"
