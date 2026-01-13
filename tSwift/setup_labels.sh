#!/bin/bash
# setup_labels.sh - Create standard GitHub labels for a new repo
#
# Run this once when initializing a new project from ai_template.
# Safe to re-run - will update existing labels.

set -e

echo "Setting up standard labels..."

# Priority labels
gh label create "P0" --description "Critical - drop everything" --color "B60205" --force
gh label create "P1" --description "High priority - do soon" --color "D93F0B" --force
gh label create "P2" --description "Medium priority - normal queue" --color "FBCA04" --force
gh label create "P3" --description "Low priority - when time permits" --color "0E8A16" --force

# Type labels
gh label create "task" --description "Work item" --color "1D76DB" --force
gh label create "bug" --description "Something is broken" --color "B60205" --force
gh label create "enhancement" --description "Improvement to existing feature" --color "A2EEEF" --force

# Status labels
gh label create "in-progress" --description "Currently being worked on" --color "FBCA04" --force
gh label create "blocked" --description "Waiting on something" --color "D93F0B" --force

# Communication labels (for cross-project issues)
gh label create "from-external" --description "Issue from another project" --color "C5DEF5" --force

echo ""
echo "✓ Labels created. View at: $(gh repo view --json url -q .url)/labels"
