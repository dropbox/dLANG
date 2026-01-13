#!/usr/bin/env bash
#
# init.sh - Initialize development environment for ai_template
#
# Installs all required tools for code complexity analysis and development.
#
# Usage:
#   ./init.sh           # Install everything
#   ./init.sh --check   # Check what's installed without installing
#
# Copyright 2026 Dropbox, Inc.
# Licensed under the Apache License, Version 2.0

set -euo pipefail

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Track what we installed
INSTALLED=()
FAILED=()
SKIPPED=()

log_info() { echo -e "${BLUE}[INFO]${NC} $1"; }
log_ok() { echo -e "${GREEN}[OK]${NC} $1"; }
log_warn() { echo -e "${YELLOW}[WARN]${NC} $1"; }
log_error() { echo -e "${RED}[ERROR]${NC} $1"; }

# Detect platform
detect_platform() {
    case "$(uname -s)" in
        Darwin*) echo "macos" ;;
        Linux*)  echo "linux" ;;
        *)       echo "unknown" ;;
    esac
}

# Check if a command exists
has_cmd() {
    command -v "$1" &> /dev/null
}

# Check prerequisites
check_prerequisites() {
    log_info "Checking prerequisites..."
    local missing=()

    if ! has_cmd python3; then
        missing+=("python3")
    fi

    if ! has_cmd pip3 && ! has_cmd pip; then
        missing+=("pip")
    fi

    if [[ ${#missing[@]} -gt 0 ]]; then
        log_error "Missing required tools: ${missing[*]}"
        log_error "Please install Python 3 with pip first."
        exit 1
    fi

    log_ok "Prerequisites satisfied (python3, pip)"
}

# Get pip command (pip3 or pip)
get_pip() {
    if has_cmd pip3; then
        echo "pip3"
    else
        echo "pip"
    fi
}

# Install Python packages
install_python_tools() {
    log_info "Installing Python tools..."
    local pip_cmd
    pip_cmd=$(get_pip)

    # radon - Python complexity analysis (best-in-class)
    if has_cmd radon; then
        log_ok "radon already installed"
        SKIPPED+=("radon")
    else
        log_info "Installing radon (Python complexity analyzer)..."
        if $pip_cmd install --quiet radon; then
            log_ok "radon installed"
            INSTALLED+=("radon")
        else
            log_error "Failed to install radon"
            FAILED+=("radon")
        fi
    fi

    # lizard - Multi-language complexity (Rust, TS, Swift, ObjC, C/C++ fallback)
    if has_cmd lizard; then
        log_ok "lizard already installed"
        SKIPPED+=("lizard")
    else
        log_info "Installing lizard (multi-language complexity analyzer)..."
        if $pip_cmd install --quiet lizard; then
            log_ok "lizard installed"
            INSTALLED+=("lizard")
        else
            log_error "Failed to install lizard"
            FAILED+=("lizard")
        fi
    fi
}

# Install Go tools
install_go_tools() {
    log_info "Installing Go tools..."

    if ! has_cmd go; then
        log_warn "Go not installed - skipping Go tools (gocyclo)"
        log_warn "  Install Go from https://go.dev/dl/ if you need Go analysis"
        SKIPPED+=("gocyclo")
        return
    fi

    # gocyclo - Go cyclomatic complexity (best-in-class)
    if has_cmd gocyclo; then
        log_ok "gocyclo already installed"
        SKIPPED+=("gocyclo")
    else
        log_info "Installing gocyclo (Go complexity analyzer)..."
        if go install github.com/fzipp/gocyclo/cmd/gocyclo@latest 2>/dev/null; then
            # Add GOPATH/bin to PATH hint
            if [[ -d "$HOME/go/bin" ]] && [[ ":$PATH:" != *":$HOME/go/bin:"* ]]; then
                log_warn "Add \$HOME/go/bin to your PATH to use gocyclo"
            fi
            log_ok "gocyclo installed"
            INSTALLED+=("gocyclo")
        else
            log_error "Failed to install gocyclo"
            FAILED+=("gocyclo")
        fi
    fi
}

# Install C/C++ tools
install_c_tools() {
    log_info "Installing C/C++ tools..."
    local platform
    platform=$(detect_platform)

    # pmccabe - C/C++ McCabe complexity (best-in-class)
    if has_cmd pmccabe; then
        log_ok "pmccabe already installed"
        SKIPPED+=("pmccabe")
    else
        log_info "Installing pmccabe (C/C++ complexity analyzer)..."
        case "$platform" in
            macos)
                if has_cmd brew; then
                    if brew install pmccabe 2>/dev/null; then
                        log_ok "pmccabe installed via Homebrew"
                        INSTALLED+=("pmccabe")
                    else
                        log_warn "Failed to install pmccabe - will use lizard as fallback"
                        SKIPPED+=("pmccabe")
                    fi
                else
                    log_warn "Homebrew not installed - skipping pmccabe"
                    log_warn "  lizard will be used as fallback for C/C++"
                    SKIPPED+=("pmccabe")
                fi
                ;;
            linux)
                if has_cmd apt-get; then
                    log_info "Installing pmccabe via apt (may require sudo)..."
                    if sudo apt-get install -y pmccabe 2>/dev/null; then
                        log_ok "pmccabe installed via apt"
                        INSTALLED+=("pmccabe")
                    else
                        log_warn "Failed to install pmccabe - will use lizard as fallback"
                        SKIPPED+=("pmccabe")
                    fi
                elif has_cmd yum; then
                    log_warn "pmccabe not available via yum - will use lizard as fallback"
                    SKIPPED+=("pmccabe")
                else
                    log_warn "Unknown package manager - skipping pmccabe"
                    SKIPPED+=("pmccabe")
                fi
                ;;
            *)
                log_warn "Unknown platform - skipping pmccabe"
                SKIPPED+=("pmccabe")
                ;;
        esac
    fi
}

# Verify installations
verify_installations() {
    log_info "Verifying installations..."
    echo ""

    local tools=("radon" "lizard" "gocyclo" "pmccabe")
    local tool_descriptions=(
        "radon:Python complexity (best-in-class)"
        "lizard:Multi-language (Rust, TS, Swift, ObjC)"
        "gocyclo:Go complexity (best-in-class)"
        "pmccabe:C/C++ complexity (best-in-class)"
    )

    echo "Tool Status:"
    echo "------------"
    for desc in "${tool_descriptions[@]}"; do
        local tool="${desc%%:*}"
        local description="${desc#*:}"
        if has_cmd "$tool"; then
            echo -e "  ${GREEN}✓${NC} $tool - $description"
        else
            echo -e "  ${RED}✗${NC} $tool - $description"
        fi
    done
    echo ""
}

# Print summary
print_summary() {
    echo ""
    echo "========================================"
    echo "Installation Summary"
    echo "========================================"

    if [[ ${#INSTALLED[@]} -gt 0 ]]; then
        echo -e "${GREEN}Installed:${NC} ${INSTALLED[*]}"
    fi

    if [[ ${#SKIPPED[@]} -gt 0 ]]; then
        echo -e "${YELLOW}Skipped (already installed or unavailable):${NC} ${SKIPPED[*]}"
    fi

    if [[ ${#FAILED[@]} -gt 0 ]]; then
        echo -e "${RED}Failed:${NC} ${FAILED[*]}"
    fi

    echo ""
    echo "Run './code_stats.py .' to analyze your codebase."
    echo ""
}

# Check mode - just report what's installed
check_mode() {
    log_info "Checking installed tools (no installation)..."
    echo ""
    verify_installations

    # Also run code_stats.py to show what would be analyzed
    if [[ -f "./code_stats.py" ]]; then
        log_info "Running code_stats.py to check tool availability..."
        python3 ./code_stats.py . --quiet 2>&1 | grep -E "(Missing tools|lizard|radon|gocyclo|pmccabe)" || true
    fi
}

# Main
main() {
    echo ""
    echo "========================================"
    echo "ai_template Development Environment Setup"
    echo "========================================"
    echo ""

    # Check for --check flag
    if [[ "${1:-}" == "--check" ]]; then
        check_mode
        exit 0
    fi

    check_prerequisites
    echo ""

    install_python_tools
    echo ""

    install_go_tools
    echo ""

    install_c_tools
    echo ""

    verify_installations
    print_summary
}

main "$@"
