#!/bin/bash
# Install tRust git hooks
#
# Usage: ./scripts/install-hooks.sh

set -e

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"

echo "Installing tRust git hooks..."

# Install pre-commit hook
cp scripts/pre-commit.hook .git/hooks/pre-commit
chmod +x .git/hooks/pre-commit

echo "Installed pre-commit hook"
echo ""
echo "Hooks installed successfully!"
echo ""
echo "Environment variables:"
echo "  TRUST_SKIP_HOOKS=1    - Skip pre-commit checks (emergency use)"
echo "  TRUST_FULL_BUILD=1    - Include full stage 1 build check"
