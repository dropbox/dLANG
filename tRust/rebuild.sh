#!/bin/bash
# Rebuild tRust with latest dependencies
set -e
cd "$(dirname "$0")"
echo "=== Updating kani_fast submodule ==="
git submodule update --remote deps/kani_fast
echo "=== Rebuilding tRust stage 1 ==="
cd upstream/rustc && ./x.py build --stage 1
echo "=== Done ==="
