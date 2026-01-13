#!/usr/bin/env python3
"""
code_stats.py - Code complexity analysis using best-in-class tools

Uses an ensemble of language-specific tools:
- Rust: lizard
- Python: radon (best-in-class)
- Go: gocyclo (best-in-class)
- C/C++: pmccabe (preferred) or lizard
- TypeScript/JavaScript: lizard
- Swift: lizard
- Objective-C: lizard
- Bash: line count only (no complexity tool exists)

Outputs standardized JSON for aggregation across projects.

Install required tools:
    ./init.sh

Copyright 2026 Dropbox, Inc.
Licensed under the Apache License, Version 2.0
"""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import sys
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

# Complexity thresholds
THRESHOLD_CYCLOMATIC = 10
THRESHOLD_COGNITIVE = 15
THRESHOLD_HIGH = 20  # "high" severity above this

# Directories to skip
SKIP_DIRS = {
    ".git", "__pycache__", "node_modules", "target", "build",
    "dist", ".venv", "venv", "env", ".tox", ".pytest_cache",
    "vendor", "third_party", ".build",
}

# File extensions by language
LANG_EXTENSIONS = {
    "rust": [".rs"],
    "python": [".py"],
    "go": [".go"],
    "cpp": [".cpp", ".cc", ".cxx", ".hpp"],
    "c": [".c", ".h"],
    "typescript": [".ts", ".tsx"],
    "javascript": [".js", ".jsx"],
    "swift": [".swift"],
    "objc": [".m", ".mm"],
    "bash": [".sh", ".bash"],
}


@dataclass
class FunctionMetric:
    """Metrics for a single function."""
    file: str
    name: str
    line: int
    lang: str
    complexity: int
    complexity_type: str  # cyclomatic, cognitive
    sloc: int = 0


@dataclass
class LanguageSummary:
    """Summary stats for a language."""
    files: int = 0
    code_lines: int = 0
    functions: int = 0
    total_complexity: int = 0
    max_complexity: int = 0

    @property
    def avg_complexity(self) -> float:
        return self.total_complexity / self.functions if self.functions else 0.0


@dataclass
class AnalysisResult:
    """Complete analysis result."""
    project: str
    commit: str
    timestamp: str
    tools: dict[str, str] = field(default_factory=dict)
    by_language: dict[str, LanguageSummary] = field(default_factory=dict)
    functions: list[FunctionMetric] = field(default_factory=list)
    warnings: list[dict[str, Any]] = field(default_factory=list)
    errors: list[str] = field(default_factory=list)

    def to_dict(self) -> dict:
        """Convert to JSON-serializable dict."""
        summary = {
            "total_files": sum(ls.files for ls in self.by_language.values()),
            "total_code_lines": sum(ls.code_lines for ls in self.by_language.values()),
            "total_functions": sum(ls.functions for ls in self.by_language.values()),
            "by_language": {
                lang: {
                    "files": ls.files,
                    "code_lines": ls.code_lines,
                    "functions": ls.functions,
                    "avg_complexity": round(ls.avg_complexity, 2),
                    "max_complexity": ls.max_complexity,
                }
                for lang, ls in self.by_language.items()
            },
        }
        return {
            "version": "1.0",
            "timestamp": self.timestamp,
            "project": self.project,
            "commit": self.commit,
            "tools": self.tools,
            "summary": summary,
            "functions": [
                {
                    "file": f.file,
                    "name": f.name,
                    "line": f.line,
                    "lang": f.lang,
                    "complexity": f.complexity,
                    "type": f.complexity_type,
                    "sloc": f.sloc,
                }
                for f in self.functions
            ],
            "warnings": self.warnings,
            "errors": self.errors,
        }


def run_cmd(cmd: list[str], cwd: Path | None = None) -> tuple[bool, str, str]:
    """Run command, return (success, stdout, stderr)."""
    try:
        result = subprocess.run(
            cmd,
            cwd=cwd,
            capture_output=True,
            text=True,
            timeout=300,
        )
        return result.returncode == 0, result.stdout, result.stderr
    except (subprocess.TimeoutExpired, FileNotFoundError) as e:
        return False, "", str(e)


def get_git_info(root: Path) -> tuple[str, str]:
    """Get project name and commit hash."""
    project = root.resolve().name

    ok, stdout, _ = run_cmd(["git", "rev-parse", "--short", "HEAD"], cwd=root)
    commit = stdout.strip() if ok else "unknown"

    return project, commit


def find_files(root: Path, extensions: list[str]) -> list[Path]:
    """Find files with given extensions, excluding skip dirs."""
    files = []
    for path in root.rglob("*"):
        if any(skip in path.parts for skip in SKIP_DIRS):
            continue
        if path.is_file() and path.suffix.lower() in extensions:
            files.append(path)
    return files


def has_tool(name: str) -> bool:
    """Check if a tool is available."""
    return shutil.which(name) is not None


# =============================================================================
# Rust: lizard (rust-code-analysis has compilation issues)
# =============================================================================

def analyze_rust(root: Path, result: AnalysisResult) -> None:
    """Analyze Rust code using lizard."""
    if not has_tool("lizard"):
        result.errors.append("lizard not installed (pip install lizard)")
        return

    files = find_files(root, LANG_EXTENSIONS["rust"])
    if not files:
        return

    result.tools["rust"] = "lizard"
    _analyze_with_lizard(root, files, ["rust"], result)


# =============================================================================
# Python: radon
# =============================================================================

def analyze_python(root: Path, result: AnalysisResult) -> None:
    """Analyze Python code using radon."""
    if not has_tool("radon"):
        result.errors.append("radon not installed (pip install radon)")
        return

    files = find_files(root, LANG_EXTENSIONS["python"])
    if not files:
        return

    result.tools["python"] = "radon"
    lang_summary = LanguageSummary()
    lang_summary.files = len(files)

    # Get cyclomatic complexity
    ok, stdout, _ = run_cmd(["radon", "cc", "-j", "-a", str(root)])
    if ok and stdout.strip():
        try:
            data = json.loads(stdout)
            for filepath, functions in data.items():
                if isinstance(functions, list):
                    rel_path = str(Path(filepath).relative_to(root)) if filepath.startswith(str(root)) else filepath
                    for func in functions:
                        name = func.get("name", "")
                        line = func.get("lineno", 0)
                        complexity = func.get("complexity", 0)

                        lang_summary.functions += 1
                        lang_summary.total_complexity += complexity
                        lang_summary.max_complexity = max(lang_summary.max_complexity, complexity)

                        fm = FunctionMetric(
                            file=rel_path,
                            name=name,
                            line=line,
                            lang="python",
                            complexity=complexity,
                            complexity_type="cyclomatic",
                        )
                        result.functions.append(fm)

                        if complexity > THRESHOLD_CYCLOMATIC:
                            result.warnings.append({
                                "file": rel_path,
                                "name": name,
                                "line": line,
                                "complexity": complexity,
                                "threshold": THRESHOLD_CYCLOMATIC,
                                "type": "cyclomatic",
                                "severity": "high" if complexity > THRESHOLD_HIGH else "medium",
                            })
        except json.JSONDecodeError:
            result.errors.append("Failed to parse radon cc output")

    # Get raw metrics (SLOC)
    ok, stdout, _ = run_cmd(["radon", "raw", "-j", str(root)])
    if ok and stdout.strip():
        try:
            data = json.loads(stdout)
            for metrics in data.values():
                if isinstance(metrics, dict):
                    lang_summary.code_lines += metrics.get("sloc", 0)
        except json.JSONDecodeError:
            pass

    if lang_summary.files > 0:
        result.by_language["python"] = lang_summary


# =============================================================================
# Go: gocyclo + gocognit
# =============================================================================

def analyze_go(root: Path, result: AnalysisResult) -> None:
    """Analyze Go code using gocyclo and gocognit."""
    has_gocyclo = has_tool("gocyclo")
    has_gocognit = has_tool("gocognit")

    if not has_gocyclo and not has_gocognit:
        result.errors.append("Go tools not installed (go install github.com/fzipp/gocyclo/cmd/gocyclo@latest)")
        return

    files = find_files(root, LANG_EXTENSIONS["go"])
    if not files:
        return

    tools_used = []
    if has_gocyclo:
        tools_used.append("gocyclo")
    if has_gocognit:
        tools_used.append("gocognit")
    result.tools["go"] = "+".join(tools_used)

    lang_summary = LanguageSummary()
    lang_summary.files = len(files)
    seen_functions: set[tuple[str, str, int]] = set()

    # gocyclo output: "complexity package/path/file.go:line:col func_name"
    if has_gocyclo:
        ok, stdout, _ = run_cmd(["gocyclo", "-avg", "."], cwd=root)
        if ok:
            for line in stdout.strip().split("\n"):
                if not line or line.startswith("Average"):
                    continue
                parts = line.split()
                if len(parts) >= 3:
                    try:
                        complexity = int(parts[0])
                        location = parts[1]  # file:line:col
                        name = parts[2] if len(parts) > 2 else ""

                        # Parse location
                        loc_parts = location.split(":")
                        filepath = loc_parts[0]
                        lineno = int(loc_parts[1]) if len(loc_parts) > 1 else 0

                        key = (filepath, name, lineno)
                        if key in seen_functions:
                            continue
                        seen_functions.add(key)

                        lang_summary.functions += 1
                        lang_summary.total_complexity += complexity
                        lang_summary.max_complexity = max(lang_summary.max_complexity, complexity)

                        fm = FunctionMetric(
                            file=filepath,
                            name=name,
                            line=lineno,
                            lang="go",
                            complexity=complexity,
                            complexity_type="cyclomatic",
                        )
                        result.functions.append(fm)

                        if complexity > THRESHOLD_CYCLOMATIC:
                            result.warnings.append({
                                "file": filepath,
                                "name": name,
                                "line": lineno,
                                "complexity": complexity,
                                "threshold": THRESHOLD_CYCLOMATIC,
                                "type": "cyclomatic",
                                "severity": "high" if complexity > THRESHOLD_HIGH else "medium",
                            })
                    except (ValueError, IndexError):
                        continue

    # Count SLOC simply
    for filepath in files:
        try:
            content = filepath.read_text(errors="ignore")
            sloc = sum(1 for line in content.split("\n") if line.strip() and not line.strip().startswith("//"))
            lang_summary.code_lines += sloc
        except Exception:
            pass

    if lang_summary.files > 0:
        result.by_language["go"] = lang_summary


# =============================================================================
# C/C++: pmccabe or lizard
# =============================================================================

def analyze_c_cpp(root: Path, result: AnalysisResult) -> None:
    """Analyze C/C++ code using pmccabe or lizard."""
    has_pmccabe = has_tool("pmccabe")
    has_lizard = has_tool("lizard")

    if not has_pmccabe and not has_lizard:
        result.errors.append("C/C++ tools not installed (apt install pmccabe or pip install lizard)")
        return

    c_files = find_files(root, LANG_EXTENSIONS["c"])
    cpp_files = find_files(root, LANG_EXTENSIONS["cpp"])
    all_files = c_files + cpp_files

    if not all_files:
        return

    # Prefer pmccabe for C/C++
    if has_pmccabe:
        result.tools["c"] = "pmccabe"
        result.tools["cpp"] = "pmccabe"
        _analyze_with_pmccabe(root, all_files, result)
    else:
        result.tools["c"] = "lizard"
        result.tools["cpp"] = "lizard"
        _analyze_with_lizard(root, all_files, ["c", "cpp"], result)


def _analyze_with_pmccabe(root: Path, files: list[Path], result: AnalysisResult) -> None:
    """Run pmccabe on files."""
    c_summary = LanguageSummary()
    cpp_summary = LanguageSummary()

    for filepath in files:
        is_cpp = filepath.suffix.lower() in LANG_EXTENSIONS["cpp"]
        summary = cpp_summary if is_cpp else c_summary
        lang = "cpp" if is_cpp else "c"
        summary.files += 1

        # Count SLOC
        try:
            content = filepath.read_text(errors="ignore")
            sloc = sum(1 for line in content.split("\n") if line.strip() and not line.strip().startswith("//"))
            summary.code_lines += sloc
        except Exception:
            pass

        # Run pmccabe
        ok, stdout, _ = run_cmd(["pmccabe", str(filepath)])
        if not ok:
            continue

        # pmccabe output: "complexity statements line function file"
        for line in stdout.strip().split("\n"):
            if not line:
                continue
            parts = line.split("\t")
            if len(parts) >= 5:
                try:
                    complexity = int(parts[0])
                    lineno = int(parts[2])
                    name = parts[3]
                    rel_path = str(filepath.relative_to(root))

                    summary.functions += 1
                    summary.total_complexity += complexity
                    summary.max_complexity = max(summary.max_complexity, complexity)

                    fm = FunctionMetric(
                        file=rel_path,
                        name=name,
                        line=lineno,
                        lang=lang,
                        complexity=complexity,
                        complexity_type="cyclomatic",
                    )
                    result.functions.append(fm)

                    if complexity > THRESHOLD_CYCLOMATIC:
                        result.warnings.append({
                            "file": rel_path,
                            "name": name,
                            "line": lineno,
                            "complexity": complexity,
                            "threshold": THRESHOLD_CYCLOMATIC,
                            "type": "cyclomatic",
                            "severity": "high" if complexity > THRESHOLD_HIGH else "medium",
                        })
                except (ValueError, IndexError):
                    continue

    if c_summary.files > 0:
        result.by_language["c"] = c_summary
    if cpp_summary.files > 0:
        result.by_language["cpp"] = cpp_summary


# =============================================================================
# Lizard fallback (TypeScript, JavaScript, Swift, Objective-C)
# =============================================================================

def _analyze_with_lizard(
    root: Path,
    files: list[Path],
    langs: list[str],
    result: AnalysisResult,
) -> None:
    """Use lizard for languages without better tools."""
    if not files:
        return

    # Build language args (map our lang names to lizard's)
    lang_args = []
    for lang in langs:
        if lang in ("typescript", "javascript"):
            lang_args.extend(["-l", "javascript"])  # lizard uses 'javascript' for both
        elif lang == "cpp":
            lang_args.extend(["-l", "cpp"])
        elif lang == "c":
            lang_args.extend(["-l", "c"])
        elif lang == "objc":
            lang_args.extend(["-l", "objectivec"])
        elif lang == "swift":
            lang_args.extend(["-l", "swift"])
        elif lang == "rust":
            lang_args.extend(["-l", "rust"])

    # Run lizard with XML output (more structured than default)
    file_args = [str(f) for f in files]
    ok, stdout, _ = run_cmd(["lizard", "--csv"] + lang_args + file_args)

    if not ok:
        return

    summaries: dict[str, LanguageSummary] = {lang: LanguageSummary() for lang in langs}
    seen_files: dict[str, set[str]] = {lang: set() for lang in langs}

    # CSV format: NLOC,CCN,token,PARAM,length,location,file,function,start,end
    for line in stdout.strip().split("\n"):
        if not line or line.startswith("NLOC"):
            continue
        parts = line.split(",")
        if len(parts) < 10:
            continue

        try:
            sloc = int(parts[0])
            complexity = int(parts[1])
            filepath = parts[6]
            name = parts[7]
            start_line = int(parts[8])

            # Determine language from extension
            ext = Path(filepath).suffix.lower()
            lang = None
            for lang_key, exts in LANG_EXTENSIONS.items():
                if ext in exts and lang_key in langs:
                    lang = lang_key
                    break

            if not lang:
                continue

            summary = summaries[lang]

            # Track files
            if filepath not in seen_files[lang]:
                seen_files[lang].add(filepath)
                summary.files += 1

            summary.functions += 1
            summary.total_complexity += complexity
            summary.max_complexity = max(summary.max_complexity, complexity)
            summary.code_lines += sloc

            rel_path = str(Path(filepath).relative_to(root)) if filepath.startswith(str(root)) else filepath

            fm = FunctionMetric(
                file=rel_path,
                name=name,
                line=start_line,
                lang=lang,
                complexity=complexity,
                complexity_type="cyclomatic",
                sloc=sloc,
            )
            result.functions.append(fm)

            if complexity > THRESHOLD_CYCLOMATIC:
                result.warnings.append({
                    "file": rel_path,
                    "name": name,
                    "line": start_line,
                    "complexity": complexity,
                    "threshold": THRESHOLD_CYCLOMATIC,
                    "type": "cyclomatic",
                    "severity": "high" if complexity > THRESHOLD_HIGH else "medium",
                })
        except (ValueError, IndexError):
            continue

    for lang, summary in summaries.items():
        if summary.files > 0:
            result.by_language[lang] = summary


def analyze_typescript(root: Path, result: AnalysisResult) -> None:
    """Analyze TypeScript/JavaScript using lizard."""
    if not has_tool("lizard"):
        result.errors.append("lizard not installed (pip install lizard)")
        return

    ts_files = find_files(root, LANG_EXTENSIONS["typescript"])
    js_files = find_files(root, LANG_EXTENSIONS["javascript"])
    all_files = ts_files + js_files

    if not all_files:
        return

    result.tools["typescript"] = "lizard"
    result.tools["javascript"] = "lizard"
    _analyze_with_lizard(root, all_files, ["typescript", "javascript"], result)


def analyze_swift(root: Path, result: AnalysisResult) -> None:
    """Analyze Swift using lizard."""
    if not has_tool("lizard"):
        result.errors.append("lizard not installed for Swift (pip install lizard)")
        return

    files = find_files(root, LANG_EXTENSIONS["swift"])
    if not files:
        return

    result.tools["swift"] = "lizard"
    _analyze_with_lizard(root, files, ["swift"], result)


def analyze_objc(root: Path, result: AnalysisResult) -> None:
    """Analyze Objective-C using lizard."""
    if not has_tool("lizard"):
        result.errors.append("lizard not installed for Objective-C (pip install lizard)")
        return

    files = find_files(root, LANG_EXTENSIONS["objc"])
    if not files:
        return

    result.tools["objc"] = "lizard"
    _analyze_with_lizard(root, files, ["objc"], result)


def analyze_bash(root: Path, result: AnalysisResult) -> None:
    """Analyze Bash (LOC only, no complexity tool exists)."""
    files = find_files(root, LANG_EXTENSIONS["bash"])
    if not files:
        return

    result.tools["bash"] = "line-count"  # No real complexity tool
    summary = LanguageSummary()
    summary.files = len(files)

    for filepath in files:
        try:
            content = filepath.read_text(errors="ignore")
            sloc = sum(1 for line in content.split("\n") if line.strip() and not line.strip().startswith("#"))
            summary.code_lines += sloc
        except Exception:
            pass

    if summary.files > 0:
        result.by_language["bash"] = summary


# =============================================================================
# Main
# =============================================================================

def analyze(root: Path) -> AnalysisResult:
    """Run full analysis on codebase."""
    project, commit = get_git_info(root)
    result = AnalysisResult(
        project=project,
        commit=commit,
        timestamp=datetime.now(timezone.utc).isoformat(),
    )

    # Run all analyzers
    analyze_rust(root, result)
    analyze_python(root, result)
    analyze_go(root, result)
    analyze_c_cpp(root, result)
    analyze_typescript(root, result)
    analyze_swift(root, result)
    analyze_objc(root, result)
    analyze_bash(root, result)

    # Sort warnings by severity and complexity
    severity_order = {"high": 0, "medium": 1, "low": 2}
    result.warnings.sort(key=lambda w: (severity_order.get(w.get("severity", "low"), 2), -w.get("complexity", 0)))

    return result


def print_summary(result: AnalysisResult) -> None:
    """Print human-readable summary to stderr."""
    print("=" * 60, file=sys.stderr)
    print("CODE COMPLEXITY ANALYSIS", file=sys.stderr)
    print(f"Project: {result.project} @ {result.commit}", file=sys.stderr)
    print("=" * 60, file=sys.stderr)

    if result.errors:
        print("\nMissing tools:", file=sys.stderr)
        for err in result.errors:
            print(f"  - {err}", file=sys.stderr)

    if not result.by_language:
        print("\nNo source files found.", file=sys.stderr)
        return

    print("\n## Summary by Language\n", file=sys.stderr)
    print(f"{'Language':<12} {'Files':>6} {'SLOC':>8} {'Funcs':>6} {'AvgCC':>6} {'MaxCC':>6}", file=sys.stderr)
    print("-" * 52, file=sys.stderr)

    for lang in sorted(result.by_language.keys()):
        ls = result.by_language[lang]
        tool = result.tools.get(lang, "?")
        print(
            f"{lang:<12} {ls.files:>6} {ls.code_lines:>8} {ls.functions:>6} "
            f"{ls.avg_complexity:>6.1f} {ls.max_complexity:>6}  [{tool}]",
            file=sys.stderr,
        )

    totals = result.to_dict()["summary"]
    print("-" * 52, file=sys.stderr)
    print(
        f"{'TOTAL':<12} {totals['total_files']:>6} {totals['total_code_lines']:>8} "
        f"{totals['total_functions']:>6}",
        file=sys.stderr,
    )

    if result.warnings:
        high_warnings = [w for w in result.warnings if w.get("severity") == "high"]
        med_warnings = [w for w in result.warnings if w.get("severity") == "medium"]

        print(f"\n## Warnings: {len(high_warnings)} high, {len(med_warnings)} medium\n", file=sys.stderr)

        # Show top 10 by complexity
        for w in result.warnings[:10]:
            sev = w.get("severity", "?")[0].upper()
            print(
                f"  [{sev}] {w['complexity']:>3} {w['file']}:{w['line']} {w['name']}",
                file=sys.stderr,
            )

        if len(result.warnings) > 10:
            print(f"  ... and {len(result.warnings) - 10} more", file=sys.stderr)

    print(file=sys.stderr)


def main() -> int:
    global THRESHOLD_CYCLOMATIC

    parser = argparse.ArgumentParser(description="Code complexity analysis")
    parser.add_argument("path", nargs="?", default=".", help="Path to analyze")
    parser.add_argument("-j", "--json", action="store_true", help="Output JSON only (no summary)")
    parser.add_argument("-o", "--output", help="Write JSON to file")
    parser.add_argument("-q", "--quiet", action="store_true", help="Suppress summary output")
    parser.add_argument("--threshold", type=int, default=10, help="Complexity threshold for warnings (default: 10)")
    args = parser.parse_args()

    THRESHOLD_CYCLOMATIC = args.threshold

    root = Path(args.path).resolve()
    if not root.exists():
        print(f"Path not found: {root}", file=sys.stderr)
        return 1

    result = analyze(root)

    # Output
    if not args.quiet and not args.json:
        print_summary(result)

    json_output = json.dumps(result.to_dict(), indent=2)

    if args.output:
        Path(args.output).write_text(json_output)
        print(f"JSON written to {args.output}", file=sys.stderr)
    elif args.json:
        print(json_output)

    # Exit code: 1 if high-severity warnings
    high_count = sum(1 for w in result.warnings if w.get("severity") == "high")
    return 1 if high_count > 0 else 0


if __name__ == "__main__":
    sys.exit(main())
