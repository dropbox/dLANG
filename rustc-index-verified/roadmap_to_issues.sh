#!/bin/bash
# roadmap_to_issues.sh - Convert markdown roadmap to GitHub Issues
#
# Workflow:
#   1. ./roadmap_to_issues.sh --current          # Get current issues (if updating)
#   2. Write/edit ROADMAP.md, git commit
#   3. ./roadmap_to_issues.sh ROADMAP.md         # Parse and produce draft for AI review
#   4. AI reviews draft, fixes any warnings in ROADMAP.md
#   5. ./roadmap_to_issues.sh ROADMAP.md --publish  # Create issues in GitHub
#
# Expected markdown format (see ROADMAP_TEMPLATE.md):
#   ## <Issue Title>
#   **Labels:** label1, label2
#   **Milestone:** v1.0 (optional)
#   **Priority:** P0|P1|P2|P3 (optional, adds label)
#   **Depends:** #1, #2 (optional, noted in body)
#
#   Issue body text here.
#
#   ---

set -e

# Colors for output
RED='\033[0;31m'
YELLOW='\033[1;33m'
GREEN='\033[0;32m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

warn() { echo -e "${YELLOW}WARNING:${NC} $1" >&2; }
error() { echo -e "${RED}ERROR:${NC} $1" >&2; }
info() { echo -e "${BLUE}INFO:${NC} $1"; }
success() { echo -e "${GREEN}✓${NC} $1"; }

# Help
if [[ "$1" == "--help" ]] || [[ "$1" == "-h" ]]; then
    echo "roadmap_to_issues.sh - Convert markdown roadmap to GitHub Issues"
    echo ""
    echo "Usage:"
    echo "  ./roadmap_to_issues.sh --help                 Show this help"
    echo "  ./roadmap_to_issues.sh --current              Get current open issues"
    echo "  ./roadmap_to_issues.sh ROADMAP.md             Parse and show draft for review"
    echo "  ./roadmap_to_issues.sh ROADMAP.md --publish   Create issues in GitHub"
    echo ""
    echo "Workflow:"
    echo "  1. ./roadmap_to_issues.sh --current           # See existing issues"
    echo "  2. Write ROADMAP.md, git commit"
    echo "  3. ./roadmap_to_issues.sh ROADMAP.md          # Parse, fix warnings"
    echo "  4. ./roadmap_to_issues.sh ROADMAP.md --publish"
    echo ""
    echo "See ROADMAP_TEMPLATE.md for markdown format."
    exit 0
fi

# Show current issues
if [[ "$1" == "--current" ]]; then
    echo "=== Current Open Issues ==="
    echo ""
    gh issue list --state open --limit 50 --json number,title,labels,milestone \
        --jq '.[] | "#\(.number) [\(.labels | map(.name) | join(", "))] \(.title)"'
    echo ""
    echo "=== By Priority ==="
    for p in P0 P1 P2 P3; do
        count=$(gh issue list --state open --label "$p" --json number --jq 'length' 2>/dev/null || echo "0")
        echo "  $p: $count issues"
    done
    exit 0
fi

# Parse arguments
ROADMAP_FILE="${1:-ROADMAP.md}"
PUBLISH=false

if [[ "$1" == "--publish" ]]; then
    ROADMAP_FILE="${2:-ROADMAP.md}"
    PUBLISH=true
elif [[ "$2" == "--publish" ]]; then
    PUBLISH=true
fi

if [[ ! -f "$ROADMAP_FILE" ]]; then
    error "Roadmap file '$ROADMAP_FILE' not found"
    echo "Usage:"
    echo "  ./roadmap_to_issues.sh --current              # Get current issues"
    echo "  ./roadmap_to_issues.sh ROADMAP.md             # Parse and draft"
    echo "  ./roadmap_to_issues.sh ROADMAP.md --publish   # Create issues"
    exit 1
fi

# Temporary file for parsed issues
PARSED_FILE=$(mktemp)
trap "rm -f $PARSED_FILE" EXIT

# Parse the markdown
WARNINGS=0
awk -v warn_count=0 '
BEGIN {
    in_issue = 0
    issue_count = 0
    title = ""
    labels = ""
    milestone = ""
    priority = ""
    depends = ""
    body = ""
}

function output_issue() {
    if (title == "") return
    issue_count++
    # Check for empty body
    check_body(title, body)
    print "<<<ISSUE_" issue_count ">>>"
    print "TITLE: " title
    print "LABELS: " labels
    if (milestone != "") print "MILESTONE: " milestone
    if (priority != "") print "PRIORITY: " priority
    if (depends != "") print "DEPENDS: " depends
    print "---BODY---"
    # Trim body
    gsub(/^[[:space:]]+|[[:space:]]+$/, "", body)
    print body
    print "<<<END_ISSUE>>>"
    print ""
}

/^## / {
    output_issue()
    # Reset for new issue
    title = substr($0, 4)
    labels = "task"
    milestone = ""
    priority = ""
    depends = ""
    body = ""
    in_issue = 1

    # Validate title
    if (length(title) < 5) {
        print "<<<WARNING>>> Issue title too short: \"" title "\"" > "/dev/stderr"
        warn_count++
    }
    if (length(title) > 100) {
        print "<<<WARNING>>> Issue title too long (>100 chars): \"" title "\"" > "/dev/stderr"
        warn_count++
    }
    next
}

function check_body(t, b) {
    gsub(/^[[:space:]]+|[[:space:]]+$/, "", b)
    if (length(b) < 10) {
        print "<<<WARNING>>> Issue has empty or very short body: \"" t "\"" > "/dev/stderr"
        return 1
    }
    return 0
}

/^\*\*Labels:\*\*/ {
    gsub(/^\*\*Labels:\*\*[[:space:]]*/, "")
    labels = $0
    next
}

/^\*\*Milestone:\*\*/ {
    gsub(/^\*\*Milestone:\*\*[[:space:]]*/, "")
    milestone = $0
    next
}

/^\*\*Priority:\*\*/ {
    gsub(/^\*\*Priority:\*\*[[:space:]]*/, "")
    priority = $0
    if (priority !~ /^P[0-3]$/) {
        print "<<<WARNING>>> Invalid priority \"" priority "\" (use P0, P1, P2, or P3)" > "/dev/stderr"
        warn_count++
    }
    next
}

/^\*\*Depends:\*\*/ {
    gsub(/^\*\*Depends:\*\*[[:space:]]*/, "")
    depends = $0
    next
}

/^---$/ { next }
/^# / { next }  # Skip top-level headers
/^>/ { next }   # Skip blockquotes (instructions)

{
    if (in_issue) {
        if (body != "") body = body "\n"
        body = body $0
    }
}

END {
    output_issue()
    print "<<<TOTAL:" issue_count ">>>"
    if (warn_count > 0) {
        print "<<<WARNINGS:" warn_count ">>>" > "/dev/stderr"
    }
}
' "$ROADMAP_FILE" > "$PARSED_FILE" 2>&1

# Check for warnings in stderr portion
WARNING_COUNT=$(grep -c "<<<WARNING>>>" "$PARSED_FILE" 2>/dev/null || echo "0")

# Extract total
TOTAL=$(grep "<<<TOTAL:" "$PARSED_FILE" | sed 's/<<<TOTAL:\([0-9]*\)>>>/\1/')

echo "=========================================="
echo "ROADMAP PARSER - $(date '+%Y-%m-%d %H:%M')"
echo "=========================================="
echo "File: $ROADMAP_FILE"
echo "Issues found: $TOTAL"
echo "Warnings: $WARNING_COUNT"
echo ""

if [[ "$WARNING_COUNT" -gt 0 ]]; then
    echo "=== WARNINGS (fix these in $ROADMAP_FILE) ==="
    grep "<<<WARNING>>>" "$PARSED_FILE" | sed 's/<<<WARNING>>> /  ⚠ /'
    echo ""
fi

echo "=== DRAFT ISSUES FOR REVIEW ==="
echo ""

# Process each issue
issue_num=0
while IFS= read -r line; do
    if [[ "$line" =~ ^\<\<\<ISSUE_([0-9]+)\>\>\>$ ]]; then
        issue_num="${BASH_REMATCH[1]}"
        echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
        echo "ISSUE $issue_num"
        echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
    elif [[ "$line" =~ ^TITLE:\ (.*)$ ]]; then
        echo "Title: ${BASH_REMATCH[1]}"
        current_title="${BASH_REMATCH[1]}"
    elif [[ "$line" =~ ^LABELS:\ (.*)$ ]]; then
        echo "Labels: ${BASH_REMATCH[1]}"
        current_labels="${BASH_REMATCH[1]}"
    elif [[ "$line" =~ ^MILESTONE:\ (.*)$ ]]; then
        echo "Milestone: ${BASH_REMATCH[1]}"
        current_milestone="${BASH_REMATCH[1]}"
    elif [[ "$line" =~ ^PRIORITY:\ (.*)$ ]]; then
        priority="${BASH_REMATCH[1]}"
        current_labels="$current_labels,$priority"
        echo "Priority: $priority (added to labels)"
    elif [[ "$line" =~ ^DEPENDS:\ (.*)$ ]]; then
        current_depends="${BASH_REMATCH[1]}"
        echo "Depends: $current_depends"
    elif [[ "$line" == "---BODY---" ]]; then
        echo "Body:"
        in_body=true
        current_body=""
    elif [[ "$line" == "<<<END_ISSUE>>>" ]]; then
        in_body=false

        # Add depends to body if present
        if [[ -n "$current_depends" ]]; then
            current_body="$current_body

**Depends on:** $current_depends"
        fi

        if [[ "$PUBLISH" == "true" ]]; then
            echo ""
            echo "Publishing..."

            cmd_args=(--title "$current_title" --label "$current_labels" --body "$current_body")
            [[ -n "$current_milestone" ]] && cmd_args+=(--milestone "$current_milestone")

            if gh issue create "${cmd_args[@]}"; then
                success "Created issue: $current_title"
            else
                error "Failed to create issue: $current_title"
            fi
            sleep 0.5  # Rate limiting
        fi

        echo ""
        current_title=""
        current_labels=""
        current_milestone=""
        current_depends=""
        current_body=""
    elif [[ "$in_body" == "true" ]]; then
        echo "  $line"
        if [[ -n "$current_body" ]]; then
            current_body="$current_body
$line"
        else
            current_body="$line"
        fi
    fi
done < "$PARSED_FILE"

echo "=========================================="
if [[ "$PUBLISH" == "true" ]]; then
    success "Published $TOTAL issues to GitHub"
else
    echo ""
    if [[ "$WARNING_COUNT" -gt 0 ]]; then
        warn "Fix $WARNING_COUNT warnings in $ROADMAP_FILE before publishing"
        echo ""
    fi
    echo "To publish these issues:"
    echo "  ./roadmap_to_issues.sh $ROADMAP_FILE --publish"
fi
echo "=========================================="
