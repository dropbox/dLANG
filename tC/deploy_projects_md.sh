#!/bin/bash
# Deploy PROJECTS.md to all repos in ayates_dbx org
# Usage: ./deploy_projects_md.sh

set -euo pipefail

PROJECTS_MD="/Users/ayates/ai_template/mail/PROJECTS.md"
TEMP_DIR="/tmp/deploy_projects_md_$$"
LOG_FILE="/tmp/deploy_projects_md_$$.log"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
RESET='\033[0m'

mkdir -p "$TEMP_DIR"

echo "Fetching repo list..."
REPOS=$(gh repo list ayates_dbx --limit 100 --json name -q '.[].name')

success=0
failed=0
skipped=0

deploy_to_repo() {
    local repo="$1"
    local local_path="$HOME/$repo"
    local work_dir=""
    local cloned=false

    # Skip ai_template (source)
    if [ "$repo" = "ai_template" ]; then
        echo -e "${YELLOW}SKIP${RESET} $repo (source)"
        return 2
    fi

    # Use local if exists, otherwise clone
    if [ -d "$local_path/.git" ]; then
        work_dir="$local_path"
    else
        work_dir="$TEMP_DIR/$repo"
        if ! git clone --depth 1 "git@github.com:dropbox/$repo.git" "$work_dir" 2>/dev/null; then
            echo -e "${RED}FAIL${RESET} $repo (clone failed)"
            return 1
        fi
        cloned=true
    fi

    # Run git operations in subshell to avoid cd leaking out
    (
        cd "$work_dir"

        # Ensure we're on default branch and up to date
        if [ "$cloned" = false ]; then
            git fetch origin 2>/dev/null || true
            git pull --ff-only 2>/dev/null || true
        fi

        # Create mail directory
        mkdir -p mail

        # Copy PROJECTS.md
        cp "$PROJECTS_MD" mail/PROJECTS.md

        # Check if there are changes
        if git diff --quiet mail/PROJECTS.md 2>/dev/null && [ -z "$(git ls-files --others --exclude-standard mail/PROJECTS.md)" ]; then
            echo -e "${YELLOW}SKIP${RESET} $repo (no changes)"
            exit 2
        fi

        # Commit and push
        git add mail/PROJECTS.md
        if git commit -m "[MANAGER] Add shared PROJECTS.md address book

Source of truth: github.com/dropbox/ai_template/mail/PROJECTS.md
Sync with: curl -s https://raw.githubusercontent.com/dropbox/ai_template/main/mail/PROJECTS.md > mail/PROJECTS.md" 2>/dev/null; then
            if git push origin HEAD 2>/dev/null; then
                echo -e "${GREEN}OK${RESET}   $repo"
                exit 0
            else
                echo -e "${RED}FAIL${RESET} $repo (push failed)"
                exit 1
            fi
        else
            echo -e "${YELLOW}SKIP${RESET} $repo (commit failed - no changes?)"
            exit 2
        fi
    )
    local result=$?

    # Clean up cloned repos (now safe since we're not inside the directory)
    [ "$cloned" = true ] && rm -rf "$work_dir"

    return $result
}

echo ""
echo "Deploying PROJECTS.md to all repos..."
echo "========================================"
echo ""

for repo in $REPOS; do
    deploy_to_repo "$repo" && result=0 || result=$?
    if [ $result -eq 0 ]; then
        success=$((success + 1))
    elif [ $result -eq 1 ]; then
        failed=$((failed + 1))
    else
        skipped=$((skipped + 1))
    fi
done

echo ""
echo "========================================"
echo -e "Done: ${GREEN}$success OK${RESET}, ${RED}$failed failed${RESET}, ${YELLOW}$skipped skipped${RESET}"
echo ""

# Cleanup
rm -rf "$TEMP_DIR"

exit 0
