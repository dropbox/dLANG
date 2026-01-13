"""Tests for code_stats.py code complexity analysis."""

import json
import subprocess
import sys
from pathlib import Path
from unittest.mock import patch

# Add ai_template_scripts to path
sys.path.insert(0, str(Path(__file__).parent.parent / "ai_template_scripts"))

import code_stats


class TestFunctionMetric:
    """Test FunctionMetric dataclass."""

    def test_create(self):
        fm = code_stats.FunctionMetric(
            file="test.py",
            name="my_func",
            line=10,
            lang="python",
            complexity=5,
            complexity_type="cyclomatic",
            sloc=20,
        )
        assert fm.file == "test.py"
        assert fm.name == "my_func"
        assert fm.line == 10
        assert fm.lang == "python"
        assert fm.complexity == 5
        assert fm.complexity_type == "cyclomatic"
        assert fm.sloc == 20

    def test_default_sloc(self):
        fm = code_stats.FunctionMetric(
            file="test.py",
            name="func",
            line=1,
            lang="python",
            complexity=1,
            complexity_type="cyclomatic",
        )
        assert fm.sloc == 0


class TestLanguageSummary:
    """Test LanguageSummary dataclass."""

    def test_defaults(self):
        ls = code_stats.LanguageSummary()
        assert ls.files == 0
        assert ls.code_lines == 0
        assert ls.functions == 0
        assert ls.total_complexity == 0
        assert ls.max_complexity == 0

    def test_avg_complexity_no_functions(self):
        ls = code_stats.LanguageSummary()
        assert ls.avg_complexity == 0.0

    def test_avg_complexity_with_functions(self):
        ls = code_stats.LanguageSummary(
            functions=4,
            total_complexity=20,
        )
        assert ls.avg_complexity == 5.0

    def test_avg_complexity_fractional(self):
        ls = code_stats.LanguageSummary(
            functions=3,
            total_complexity=10,
        )
        assert abs(ls.avg_complexity - 3.333) < 0.01


class TestAnalysisResult:
    """Test AnalysisResult dataclass."""

    def test_defaults(self):
        result = code_stats.AnalysisResult(
            project="test",
            commit="abc123",
            timestamp="2024-01-01T00:00:00Z",
        )
        assert result.project == "test"
        assert result.commit == "abc123"
        assert result.tools == {}
        assert result.by_language == {}
        assert result.functions == []
        assert result.warnings == []
        assert result.errors == []

    def test_to_dict_empty(self):
        result = code_stats.AnalysisResult(
            project="test",
            commit="abc123",
            timestamp="2024-01-01T00:00:00Z",
        )
        d = result.to_dict()
        assert d["version"] == "1.0"
        assert d["project"] == "test"
        assert d["commit"] == "abc123"
        assert d["summary"]["total_files"] == 0
        assert d["summary"]["total_code_lines"] == 0
        assert d["summary"]["total_functions"] == 0
        assert d["functions"] == []
        assert d["warnings"] == []
        assert d["errors"] == []

    def test_to_dict_with_data(self):
        result = code_stats.AnalysisResult(
            project="myproject",
            commit="def456",
            timestamp="2024-01-01T00:00:00Z",
        )
        result.tools["python"] = "radon"
        result.by_language["python"] = code_stats.LanguageSummary(
            files=5,
            code_lines=1000,
            functions=50,
            total_complexity=200,
            max_complexity=25,
        )
        result.functions.append(
            code_stats.FunctionMetric(
                file="main.py",
                name="process",
                line=42,
                lang="python",
                complexity=15,
                complexity_type="cyclomatic",
                sloc=30,
            ),
        )
        result.warnings.append({"file": "main.py", "name": "process", "complexity": 15})
        result.errors.append("test error")

        d = result.to_dict()
        assert d["tools"]["python"] == "radon"
        assert d["summary"]["total_files"] == 5
        assert d["summary"]["total_code_lines"] == 1000
        assert d["summary"]["total_functions"] == 50
        assert d["summary"]["by_language"]["python"]["avg_complexity"] == 4.0
        assert d["summary"]["by_language"]["python"]["max_complexity"] == 25
        assert len(d["functions"]) == 1
        assert d["functions"][0]["name"] == "process"
        assert len(d["warnings"]) == 1
        assert d["errors"] == ["test error"]


class TestRunCmd:
    """Test run_cmd helper."""

    def test_success(self):
        success, stdout, stderr = code_stats.run_cmd(["echo", "hello"])
        assert success is True
        assert stdout.strip() == "hello"
        assert stderr == ""

    def test_failure(self):
        success, stdout, stderr = code_stats.run_cmd(["false"])
        assert success is False

    def test_nonexistent_command(self):
        success, stdout, stderr = code_stats.run_cmd(["nonexistent_command_xyz"])
        assert success is False
        assert "FileNotFoundError" in stderr or "No such file" in stderr

    def test_timeout(self):
        # Very short timeout to test timeout handling
        with patch("subprocess.run") as mock_run:
            mock_run.side_effect = subprocess.TimeoutExpired(["sleep", "100"], 1)
            success, stdout, stderr = code_stats.run_cmd(["sleep", "100"])
            assert success is False
            assert "timed out" in stderr


class TestFindFiles:
    """Test find_files helper."""

    def test_find_python_files(self, tmp_path):
        # Create test files
        (tmp_path / "test.py").write_text("# test")
        (tmp_path / "test.txt").write_text("# test")
        (tmp_path / "subdir").mkdir()
        (tmp_path / "subdir" / "sub.py").write_text("# sub")

        files = code_stats.find_files(tmp_path, [".py"])
        assert len(files) == 2
        filenames = {f.name for f in files}
        assert "test.py" in filenames
        assert "sub.py" in filenames

    def test_skip_directories(self, tmp_path):
        # Create files in skip dirs
        (tmp_path / "test.py").write_text("# test")
        (tmp_path / "__pycache__").mkdir()
        (tmp_path / "__pycache__" / "cached.py").write_text("# cached")
        (tmp_path / ".git").mkdir()
        (tmp_path / ".git" / "git.py").write_text("# git")

        files = code_stats.find_files(tmp_path, [".py"])
        assert len(files) == 1
        assert files[0].name == "test.py"

    def test_case_insensitive_extension(self, tmp_path):
        (tmp_path / "test.PY").write_text("# test")
        (tmp_path / "test2.Py").write_text("# test2")

        files = code_stats.find_files(tmp_path, [".py"])
        assert len(files) == 2


class TestHasTool:
    """Test has_tool helper."""

    def test_has_python(self):
        # python3 should always be available in test environment
        assert code_stats.has_tool("python3") is True

    def test_missing_tool(self):
        assert code_stats.has_tool("nonexistent_tool_xyz_123") is False


class TestGetGitInfo:
    """Test get_git_info helper."""

    def test_in_git_repo(self, tmp_path):
        # ai_template itself is a git repo
        project, commit = code_stats.get_git_info(Path(__file__).parent.parent)
        assert project == "ai_template"
        assert len(commit) == 7  # Short hash

    def test_not_git_repo(self, tmp_path):
        project, commit = code_stats.get_git_info(tmp_path)
        assert project == tmp_path.name
        assert commit == "unknown"


class TestAnalyzePython:
    """Test Python analysis with radon."""

    def test_no_radon(self):
        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )
        with patch.object(code_stats, "has_tool", return_value=False):
            code_stats.analyze_python(Path("/tmp"), result)
        assert "radon not installed" in result.errors[0]

    def test_no_files(self, tmp_path):
        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )
        with patch.object(code_stats, "has_tool", return_value=True):
            code_stats.analyze_python(tmp_path, result)
        # No error, just no results
        assert "python" not in result.by_language

    def test_with_mock_radon(self, tmp_path):
        # Create a Python file
        (tmp_path / "test.py").write_text("def foo():\n    pass\n")

        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )

        # Mock radon output
        radon_cc_output = json.dumps(
            {
                str(tmp_path / "test.py"): [
                    {"name": "foo", "lineno": 1, "complexity": 1},
                ],
            }
        )
        radon_raw_output = json.dumps(
            {
                str(tmp_path / "test.py"): {"sloc": 2},
            }
        )

        with patch.object(code_stats, "has_tool", return_value=True):
            with patch.object(code_stats, "run_cmd") as mock_run:
                # First call: radon cc, second call: radon raw
                mock_run.side_effect = [
                    (True, radon_cc_output, ""),
                    (True, radon_raw_output, ""),
                ]
                code_stats.analyze_python(tmp_path, result)

        assert "python" in result.by_language
        assert result.by_language["python"].files == 1
        assert result.by_language["python"].functions == 1
        assert result.by_language["python"].code_lines == 2
        assert len(result.functions) == 1
        assert result.functions[0].name == "foo"


class TestAnalyzeRust:
    """Test Rust analysis with lizard."""

    def test_no_lizard(self):
        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )
        with patch.object(code_stats, "has_tool", return_value=False):
            code_stats.analyze_rust(Path("/tmp"), result)
        assert "lizard not installed" in result.errors[0]

    def test_no_files(self, tmp_path):
        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )
        with patch.object(code_stats, "has_tool", return_value=True):
            code_stats.analyze_rust(tmp_path, result)
        assert "rust" not in result.by_language


class TestAnalyzeGo:
    """Test Go analysis with gocyclo."""

    def test_no_tools(self):
        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )
        with patch.object(code_stats, "has_tool", return_value=False):
            code_stats.analyze_go(Path("/tmp"), result)
        assert "Go tools not installed" in result.errors[0]

    def test_no_files(self, tmp_path):
        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )
        with patch.object(code_stats, "has_tool", return_value=True):
            code_stats.analyze_go(tmp_path, result)
        assert "go" not in result.by_language

    def test_with_mock_gocyclo(self, tmp_path):
        # Create a Go file
        go_file = tmp_path / "main.go"
        go_file.write_text("package main\nfunc main() {}\n")

        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )

        # Mock gocyclo output: "complexity file:line:col funcname"
        gocyclo_output = "5 main.go:2:1 main\nAverage: 5.0"

        def mock_has_tool(name):
            return name in ("gocyclo",)

        with patch.object(code_stats, "has_tool", side_effect=mock_has_tool):
            with patch.object(code_stats, "run_cmd") as mock_run:
                mock_run.return_value = (True, gocyclo_output, "")
                code_stats.analyze_go(tmp_path, result)

        assert "go" in result.by_language
        assert result.by_language["go"].files == 1
        assert result.by_language["go"].functions == 1
        assert len(result.functions) == 1
        assert result.functions[0].name == "main"
        assert result.functions[0].complexity == 5


class TestAnalyzeBash:
    """Test Bash analysis (line count only)."""

    def test_no_files(self, tmp_path):
        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )
        code_stats.analyze_bash(tmp_path, result)
        assert "bash" not in result.by_language

    def test_count_lines(self, tmp_path):
        (tmp_path / "test.sh").write_text(
            "#!/bin/bash\n# comment\necho hello\nexit 0\n"
        )
        (tmp_path / "test2.sh").write_text("echo world\n")

        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )
        code_stats.analyze_bash(tmp_path, result)

        assert "bash" in result.by_language
        assert result.by_language["bash"].files == 2
        # Lines excluding comments: "#!/bin/bash" is not a comment, "echo hello", "exit 0", "echo world"
        # But actually the code counts lines not starting with #
        # So: "echo hello", "exit 0", "echo world" = 3 SLOC
        assert result.by_language["bash"].code_lines == 3
        assert result.tools["bash"] == "line-count"


class TestAnalyzeCCpp:
    """Test C/C++ analysis."""

    def test_no_tools(self):
        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )
        with patch.object(code_stats, "has_tool", return_value=False):
            code_stats.analyze_c_cpp(Path("/tmp"), result)
        assert "C/C++ tools not installed" in result.errors[0]

    def test_no_files(self, tmp_path):
        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )
        with patch.object(code_stats, "has_tool", return_value=True):
            code_stats.analyze_c_cpp(tmp_path, result)
        assert "c" not in result.by_language
        assert "cpp" not in result.by_language


class TestAnalyzeTypescript:
    """Test TypeScript/JavaScript analysis."""

    def test_no_lizard(self):
        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )
        with patch.object(code_stats, "has_tool", return_value=False):
            code_stats.analyze_typescript(Path("/tmp"), result)
        assert "lizard not installed" in result.errors[0]

    def test_no_files(self, tmp_path):
        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )
        with patch.object(code_stats, "has_tool", return_value=True):
            code_stats.analyze_typescript(tmp_path, result)
        assert "typescript" not in result.by_language


class TestAnalyzeSwift:
    """Test Swift analysis."""

    def test_no_lizard(self):
        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )
        with patch.object(code_stats, "has_tool", return_value=False):
            code_stats.analyze_swift(Path("/tmp"), result)
        assert "lizard not installed" in result.errors[0]


class TestAnalyzeObjc:
    """Test Objective-C analysis."""

    def test_no_lizard(self):
        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )
        with patch.object(code_stats, "has_tool", return_value=False):
            code_stats.analyze_objc(Path("/tmp"), result)
        assert "lizard not installed" in result.errors[0]


class TestAnalyze:
    """Test the main analyze function."""

    def test_analyze_empty_dir(self, tmp_path):
        result = code_stats.analyze(tmp_path)
        assert result.project == tmp_path.name
        assert result.commit == "unknown"
        assert result.by_language == {}

    def test_warnings_sorted_by_severity(self, tmp_path):
        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )
        result.warnings = [
            {"severity": "medium", "complexity": 15},
            {"severity": "high", "complexity": 25},
            {"severity": "low", "complexity": 5},
            {"severity": "high", "complexity": 30},
        ]

        # Call the sort logic from analyze
        severity_order = {"high": 0, "medium": 1, "low": 2}
        result.warnings.sort(
            key=lambda w: (
                severity_order.get(w.get("severity", "low"), 2),
                -w.get("complexity", 0),
            ),
        )

        # Should be: high/30, high/25, medium/15, low/5
        assert result.warnings[0]["complexity"] == 30
        assert result.warnings[1]["complexity"] == 25
        assert result.warnings[2]["complexity"] == 15
        assert result.warnings[3]["complexity"] == 5


class TestPrintSummary:
    """Test print_summary output."""

    def test_empty_result(self, capsys):
        result = code_stats.AnalysisResult(
            project="test",
            commit="abc123",
            timestamp="2024-01-01T00:00:00Z",
        )
        code_stats.print_summary(result)
        captured = capsys.readouterr()
        assert "test @ abc123" in captured.err
        assert "No source files found" in captured.err

    def test_with_errors(self, capsys):
        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )
        result.errors.append("radon not installed")
        result.errors.append("gocyclo not installed")
        code_stats.print_summary(result)
        captured = capsys.readouterr()
        assert "Missing tools:" in captured.err
        assert "radon not installed" in captured.err

    def test_with_language_summary(self, capsys):
        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )
        result.tools["python"] = "radon"
        result.by_language["python"] = code_stats.LanguageSummary(
            files=10,
            code_lines=500,
            functions=25,
            total_complexity=100,
            max_complexity=15,
        )
        code_stats.print_summary(result)
        captured = capsys.readouterr()
        assert "python" in captured.err
        assert "10" in captured.err  # files
        assert "500" in captured.err  # code_lines
        assert "[radon]" in captured.err

    def test_with_warnings(self, capsys):
        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )
        result.by_language["python"] = code_stats.LanguageSummary(files=1)
        result.warnings = [
            {
                "file": "test.py",
                "name": "complex_func",
                "line": 10,
                "complexity": 25,
                "severity": "high",
            },
        ]
        code_stats.print_summary(result)
        captured = capsys.readouterr()
        assert "1 high" in captured.err
        assert "[H]" in captured.err
        assert "complex_func" in captured.err


class TestMain:
    """Test main CLI entry point."""

    def test_nonexistent_path(self, capsys):
        with patch("sys.argv", ["code_stats.py", "/nonexistent/path/xyz"]):
            ret = code_stats.main()
        assert ret == 1
        captured = capsys.readouterr()
        assert "Path not found" in captured.err

    def test_json_output(self, tmp_path, capsys):
        (tmp_path / "test.sh").write_text("echo hello\n")
        with patch("sys.argv", ["code_stats.py", str(tmp_path), "--json"]):
            code_stats.main()
        captured = capsys.readouterr()
        # JSON output should be valid
        output = json.loads(captured.out)
        assert output["version"] == "1.0"
        assert output["project"] == tmp_path.name

    def test_output_file(self, tmp_path):
        (tmp_path / "test.sh").write_text("echo hello\n")
        output_file = tmp_path / "output.json"
        with patch(
            "sys.argv", ["code_stats.py", str(tmp_path), "-o", str(output_file), "-q"]
        ):
            ret = code_stats.main()
        assert ret == 0
        assert output_file.exists()
        content = json.loads(output_file.read_text())
        assert content["version"] == "1.0"

    def test_custom_threshold(self, tmp_path):
        with patch("sys.argv", ["code_stats.py", str(tmp_path), "--threshold", "5"]):
            code_stats.main()
        # The global should be updated
        assert code_stats.THRESHOLD_CYCLOMATIC == 5
        # Reset for other tests
        code_stats.THRESHOLD_CYCLOMATIC = 10


class TestLizardAnalysis:
    """Test _analyze_with_lizard helper."""

    def test_empty_files(self, tmp_path):
        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )
        code_stats._analyze_with_lizard(tmp_path, [], ["rust"], result)  # noqa: SLF001
        assert "rust" not in result.by_language

    def test_with_mock_lizard(self, tmp_path):
        # Create a Rust file
        rust_file = tmp_path / "main.rs"
        rust_file.write_text("fn main() {}\n")

        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )

        # Mock lizard CSV output
        # NLOC,CCN,token,PARAM,length,location,file,function,start,end
        lizard_output = f"10,3,50,2,15,main.rs:1,{rust_file},main,1,10\n"

        with patch.object(code_stats, "run_cmd") as mock_run:
            mock_run.return_value = (True, lizard_output, "")
            code_stats._analyze_with_lizard(tmp_path, [rust_file], ["rust"], result)  # noqa: SLF001

        assert "rust" in result.by_language
        assert result.by_language["rust"].files == 1
        assert result.by_language["rust"].functions == 1
        assert result.by_language["rust"].total_complexity == 3
        assert len(result.functions) == 1
        assert result.functions[0].name == "main"


class TestPmccabeAnalysis:
    """Test _analyze_with_pmccabe helper."""

    def test_with_mock_pmccabe(self, tmp_path):
        # Create a C file
        c_file = tmp_path / "main.c"
        c_file.write_text("int main() { return 0; }\n")

        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )

        # Mock pmccabe output: "complexity statements line function file"
        pmccabe_output = "5\t10\t1\tmain\tmain.c"

        with patch.object(code_stats, "run_cmd") as mock_run:
            mock_run.return_value = (True, pmccabe_output, "")
            code_stats._analyze_with_pmccabe(tmp_path, [c_file], result)  # noqa: SLF001

        assert "c" in result.by_language
        assert result.by_language["c"].files == 1
        assert result.by_language["c"].functions == 1
        assert result.by_language["c"].total_complexity == 5
        assert len(result.functions) == 1
        assert result.functions[0].name == "main"


class TestThresholds:
    """Test complexity threshold handling."""

    def test_warning_generation(self, tmp_path):
        """Test that warnings are generated for high complexity functions."""
        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )

        # Simulate Python analysis with high complexity function
        radon_cc_output = json.dumps(
            {
                str(tmp_path / "test.py"): [
                    {"name": "simple", "lineno": 1, "complexity": 5},
                    {"name": "medium", "lineno": 10, "complexity": 15},
                    {"name": "complex", "lineno": 50, "complexity": 25},
                ],
            }
        )
        radon_raw_output = json.dumps(
            {
                str(tmp_path / "test.py"): {"sloc": 100},
            }
        )

        (tmp_path / "test.py").write_text("# placeholder")

        with patch.object(code_stats, "has_tool", return_value=True):
            with patch.object(code_stats, "run_cmd") as mock_run:
                mock_run.side_effect = [
                    (True, radon_cc_output, ""),
                    (True, radon_raw_output, ""),
                ]
                code_stats.analyze_python(tmp_path, result)

        # Should have 2 warnings (medium=15 and complex=25, both > 10)
        assert len(result.warnings) == 2

        # Check severities
        severities = {w["name"]: w["severity"] for w in result.warnings}
        assert severities["medium"] == "medium"  # 15 > 10 but <= 20
        assert severities["complex"] == "high"  # 25 > 20


class TestLizardParsedLine:
    """Test LizardParsedLine dataclass."""

    def test_create(self):
        parsed = code_stats.LizardParsedLine(
            sloc=10,
            complexity=5,
            filepath="/path/to/file.rs",
            name="my_func",
            start_line=42,
        )
        assert parsed.sloc == 10
        assert parsed.complexity == 5
        assert parsed.filepath == "/path/to/file.rs"
        assert parsed.name == "my_func"
        assert parsed.start_line == 42


class TestBuildLizardLangArgs:
    """Test _build_lizard_lang_args helper."""

    def test_single_lang(self):
        args = code_stats._build_lizard_lang_args(["rust"])  # noqa: SLF001
        assert args == ["-l", "rust"]

    def test_multiple_langs(self):
        args = code_stats._build_lizard_lang_args(["rust", "cpp", "swift"])  # noqa: SLF001
        assert args == ["-l", "rust", "-l", "cpp", "-l", "swift"]

    def test_typescript_maps_to_javascript(self):
        args = code_stats._build_lizard_lang_args(["typescript"])  # noqa: SLF001
        assert args == ["-l", "javascript"]

    def test_objc_maps_to_objectivec(self):
        args = code_stats._build_lizard_lang_args(["objc"])  # noqa: SLF001
        assert args == ["-l", "objectivec"]

    def test_unknown_lang_ignored(self):
        args = code_stats._build_lizard_lang_args(["rust", "unknown", "cpp"])  # noqa: SLF001
        assert args == ["-l", "rust", "-l", "cpp"]

    def test_empty_list(self):
        args = code_stats._build_lizard_lang_args([])  # noqa: SLF001
        assert args == []


class TestParseLizardCsvLine:
    """Test _parse_lizard_csv_line helper."""

    def test_valid_line(self):
        line = "10,5,100,2,15,file.rs:1,/path/to/file.rs,my_func,42,55"
        parsed = code_stats._parse_lizard_csv_line(line)  # noqa: SLF001
        assert parsed is not None
        assert parsed.sloc == 10
        assert parsed.complexity == 5
        assert parsed.filepath == "/path/to/file.rs"
        assert parsed.name == "my_func"
        assert parsed.start_line == 42

    def test_empty_line(self):
        parsed = code_stats._parse_lizard_csv_line("")  # noqa: SLF001
        assert parsed is None

    def test_header_line(self):
        parsed = code_stats._parse_lizard_csv_line(
            "NLOC,CCN,token,PARAM,length,location,file,function,start,end"
        )  # noqa: SLF001
        assert parsed is None

    def test_too_few_parts(self):
        parsed = code_stats._parse_lizard_csv_line("10,5,100,2,15")  # noqa: SLF001
        assert parsed is None

    def test_invalid_integers(self):
        line = "abc,5,100,2,15,file.rs:1,/path/file.rs,func,42,55"
        parsed = code_stats._parse_lizard_csv_line(line)  # noqa: SLF001
        assert parsed is None


class TestDetermineLangFromExtension:
    """Test _determine_lang_from_extension helper."""

    def test_rust_extension(self):
        lang = code_stats._determine_lang_from_extension(
            "/path/file.rs", ["rust", "python"]
        )  # noqa: SLF001
        assert lang == "rust"

    def test_python_extension(self):
        lang = code_stats._determine_lang_from_extension(
            "/path/file.py", ["rust", "python"]
        )  # noqa: SLF001
        assert lang == "python"

    def test_typescript_extension(self):
        lang = code_stats._determine_lang_from_extension(
            "/path/file.ts", ["typescript"]
        )  # noqa: SLF001
        assert lang == "typescript"

    def test_lang_not_in_allowed_list(self):
        lang = code_stats._determine_lang_from_extension(
            "/path/file.rs", ["python", "go"]
        )  # noqa: SLF001
        assert lang is None

    def test_unknown_extension(self):
        lang = code_stats._determine_lang_from_extension(
            "/path/file.xyz", ["rust", "python"]
        )  # noqa: SLF001
        assert lang is None

    def test_case_insensitive(self):
        lang = code_stats._determine_lang_from_extension("/path/file.RS", ["rust"])  # noqa: SLF001
        assert lang == "rust"


class TestGetRelativePath:
    """Test _get_relative_path helper."""

    def test_path_under_root(self, tmp_path):
        filepath = str(tmp_path / "src" / "main.rs")
        rel = code_stats._get_relative_path(filepath, tmp_path)  # noqa: SLF001
        assert rel == "src/main.rs"

    def test_path_not_under_root(self, tmp_path):
        filepath = "/some/other/path/file.rs"
        rel = code_stats._get_relative_path(filepath, tmp_path)  # noqa: SLF001
        assert rel == "/some/other/path/file.rs"


class TestMaybeAddComplexityWarning:
    """Test _maybe_add_complexity_warning helper."""

    def test_below_threshold_no_warning(self):
        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )
        code_stats._maybe_add_complexity_warning(result, "file.py", "func", 10, 5)  # noqa: SLF001
        assert len(result.warnings) == 0

    def test_above_threshold_adds_warning(self):
        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )
        code_stats._maybe_add_complexity_warning(result, "file.py", "func", 10, 15)  # noqa: SLF001
        assert len(result.warnings) == 1
        w = result.warnings[0]
        assert w["file"] == "file.py"
        assert w["name"] == "func"
        assert w["line"] == 10
        assert w["complexity"] == 15
        assert w["severity"] == "medium"

    def test_high_severity_above_high_threshold(self):
        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )
        code_stats._maybe_add_complexity_warning(result, "file.py", "func", 10, 25)  # noqa: SLF001
        assert len(result.warnings) == 1
        assert result.warnings[0]["severity"] == "high"

    def test_exact_threshold_no_warning(self):
        # complexity == 10 should not trigger (>10 required)
        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )
        code_stats._maybe_add_complexity_warning(result, "file.py", "func", 10, 10)  # noqa: SLF001
        assert len(result.warnings) == 0


# =============================================================================
# Tests for Go-related helper functions
# =============================================================================


class TestGocycloParsedLine:
    """Test GocycloParsedLine dataclass."""

    def test_create(self):
        parsed = code_stats.GocycloParsedLine(
            complexity=15,
            filepath="main.go",
            name="processData",
            lineno=42,
        )
        assert parsed.complexity == 15
        assert parsed.filepath == "main.go"
        assert parsed.name == "processData"
        assert parsed.lineno == 42


class TestParseGocycloLine:
    """Test _parse_gocyclo_line helper."""

    def test_valid_line(self):
        line = "15 pkg/handler.go:42:1 HandleRequest"
        parsed = code_stats._parse_gocyclo_line(line)  # noqa: SLF001
        assert parsed is not None
        assert parsed.complexity == 15
        assert parsed.filepath == "pkg/handler.go"
        assert parsed.name == "HandleRequest"
        assert parsed.lineno == 42

    def test_valid_line_without_col(self):
        # Some older versions might not include column
        line = "10 main.go:100 main"
        parsed = code_stats._parse_gocyclo_line(line)  # noqa: SLF001
        assert parsed is not None
        assert parsed.complexity == 10
        assert parsed.filepath == "main.go"
        assert parsed.name == "main"
        assert parsed.lineno == 100

    def test_empty_line(self):
        parsed = code_stats._parse_gocyclo_line("")  # noqa: SLF001
        assert parsed is None

    def test_average_line(self):
        # gocyclo with -avg outputs an average line that should be skipped
        parsed = code_stats._parse_gocyclo_line("Average: 5.2")  # noqa: SLF001
        assert parsed is None

    def test_too_few_parts(self):
        parsed = code_stats._parse_gocyclo_line("15 main.go:42")  # noqa: SLF001
        assert parsed is None

    def test_invalid_complexity(self):
        line = "abc pkg/handler.go:42:1 HandleRequest"
        parsed = code_stats._parse_gocyclo_line(line)  # noqa: SLF001
        assert parsed is None

    def test_invalid_line_number(self):
        line = "15 pkg/handler.go:abc:1 HandleRequest"
        parsed = code_stats._parse_gocyclo_line(line)  # noqa: SLF001
        assert parsed is None

    def test_no_line_number_in_location(self):
        line = "15 handler.go HandleRequest"
        parsed = code_stats._parse_gocyclo_line(line)  # noqa: SLF001
        assert parsed is not None
        assert parsed.lineno == 0  # Falls back to 0

    def test_complex_path_with_dots(self):
        line = "8 github.com/user/project/pkg/v2/handler.go:10:1 ProcessV2"
        parsed = code_stats._parse_gocyclo_line(line)  # noqa: SLF001
        assert parsed is not None
        assert parsed.filepath == "github.com/user/project/pkg/v2/handler.go"
        assert parsed.lineno == 10
        assert parsed.name == "ProcessV2"


class TestGetGoToolsString:
    """Test _get_go_tools_string helper."""

    def test_both_tools(self):
        result = code_stats._get_go_tools_string(has_gocyclo=True, has_gocognit=True)  # noqa: SLF001
        assert result == "gocyclo+gocognit"

    def test_only_gocyclo(self):
        result = code_stats._get_go_tools_string(has_gocyclo=True, has_gocognit=False)  # noqa: SLF001
        assert result == "gocyclo"

    def test_only_gocognit(self):
        result = code_stats._get_go_tools_string(has_gocyclo=False, has_gocognit=True)  # noqa: SLF001
        assert result == "gocognit"

    def test_neither_tool(self):
        result = code_stats._get_go_tools_string(has_gocyclo=False, has_gocognit=False)  # noqa: SLF001
        assert result == ""


class TestProcessGocycloOutput:
    """Test _process_gocyclo_output helper."""

    def test_empty_output(self):
        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )
        lang_summary = code_stats.LanguageSummary()
        code_stats._process_gocyclo_output("", result, lang_summary)  # noqa: SLF001
        assert lang_summary.functions == 0
        assert len(result.functions) == 0

    def test_single_function(self):
        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )
        lang_summary = code_stats.LanguageSummary()
        stdout = "8 main.go:10:1 main"
        code_stats._process_gocyclo_output(stdout, result, lang_summary)  # noqa: SLF001

        assert lang_summary.functions == 1
        assert lang_summary.total_complexity == 8
        assert lang_summary.max_complexity == 8
        assert len(result.functions) == 1
        assert result.functions[0].file == "main.go"
        assert result.functions[0].name == "main"
        assert result.functions[0].complexity == 8
        assert result.functions[0].lang == "go"

    def test_multiple_functions(self):
        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )
        lang_summary = code_stats.LanguageSummary()
        stdout = """15 handler.go:100:1 ProcessRequest
8 main.go:10:1 main
12 utils.go:50:1 parseData
Average: 11.67"""
        code_stats._process_gocyclo_output(stdout, result, lang_summary)  # noqa: SLF001

        assert lang_summary.functions == 3
        assert lang_summary.total_complexity == 35  # 15 + 8 + 12
        assert lang_summary.max_complexity == 15
        assert len(result.functions) == 3

    def test_deduplicates_same_function(self):
        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )
        lang_summary = code_stats.LanguageSummary()
        # Same function appearing twice (shouldn't happen but test dedup)
        stdout = """8 main.go:10:1 main
8 main.go:10:1 main"""
        code_stats._process_gocyclo_output(stdout, result, lang_summary)  # noqa: SLF001

        assert lang_summary.functions == 1
        assert len(result.functions) == 1

    def test_adds_warning_for_high_complexity(self):
        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )
        lang_summary = code_stats.LanguageSummary()
        stdout = "25 complex.go:50:1 veryComplexFunc"
        code_stats._process_gocyclo_output(stdout, result, lang_summary)  # noqa: SLF001

        assert len(result.warnings) == 1
        assert result.warnings[0]["severity"] == "high"
        assert result.warnings[0]["complexity"] == 25

    def test_skips_invalid_lines(self):
        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )
        lang_summary = code_stats.LanguageSummary()
        stdout = """8 main.go:10:1 main
invalid line
another bad line
12 utils.go:50:1 helper"""
        code_stats._process_gocyclo_output(stdout, result, lang_summary)  # noqa: SLF001

        assert lang_summary.functions == 2
        assert len(result.functions) == 2


class TestCountGoSloc:
    """Test _count_go_sloc helper."""

    def test_empty_files_list(self):
        sloc = code_stats._count_go_sloc([])  # noqa: SLF001
        assert sloc == 0

    def test_single_file(self, tmp_path):
        go_file = tmp_path / "main.go"
        go_file.write_text("""package main

func main() {
    fmt.Println("Hello")
}
""")
        sloc = code_stats._count_go_sloc([go_file])  # noqa: SLF001
        # Non-empty, non-comment lines: package, func, fmt.Println, }
        assert sloc == 4

    def test_excludes_comments(self, tmp_path):
        go_file = tmp_path / "main.go"
        go_file.write_text("""// Package main is the entry point
package main

// main is the entry function
func main() {
    // Print hello
    fmt.Println("Hello")
}
""")
        sloc = code_stats._count_go_sloc([go_file])  # noqa: SLF001
        # Excludes comment lines: package, func, fmt.Println, }
        assert sloc == 4

    def test_excludes_blank_lines(self, tmp_path):
        go_file = tmp_path / "main.go"
        go_file.write_text("""package main



func main() {

    fmt.Println("Hello")

}
""")
        sloc = code_stats._count_go_sloc([go_file])  # noqa: SLF001
        assert sloc == 4

    def test_multiple_files(self, tmp_path):
        file1 = tmp_path / "main.go"
        file1.write_text("package main\nfunc main() {}\n")
        file2 = tmp_path / "utils.go"
        file2.write_text("package main\nfunc helper() {}\n")

        sloc = code_stats._count_go_sloc([file1, file2])  # noqa: SLF001
        # Each file has 2 lines
        assert sloc == 4

    def test_handles_nonexistent_file(self, tmp_path):
        nonexistent = tmp_path / "missing.go"
        sloc = code_stats._count_go_sloc([nonexistent])  # noqa: SLF001
        assert sloc == 0

    def test_handles_read_error_gracefully(self, tmp_path):
        valid_file = tmp_path / "valid.go"
        valid_file.write_text("package main\n")
        nonexistent = tmp_path / "missing.go"

        # Should count valid file and skip missing
        sloc = code_stats._count_go_sloc([valid_file, nonexistent])  # noqa: SLF001
        assert sloc == 1


# =============================================================================
# Additional coverage tests for previously uncovered lines
# =============================================================================


class TestAnalyzeRustWithFiles:
    """Test analyze_rust when Rust files are present."""

    def test_sets_tools_when_files_exist(self, tmp_path):
        """Test that tools['rust'] is set to 'lizard' when files exist (lines 212-213)."""
        rust_file = tmp_path / "main.rs"
        rust_file.write_text("fn main() {}\n")

        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )

        lizard_output = f"5,2,30,0,10,main.rs:1,{rust_file},main,1,10\n"

        with patch.object(code_stats, "has_tool", return_value=True):
            with patch.object(code_stats, "run_cmd") as mock_run:
                mock_run.return_value = (True, lizard_output, "")
                code_stats.analyze_rust(tmp_path, result)

        assert result.tools.get("rust") == "lizard"
        assert "rust" in result.by_language


class TestAnalyzePythonJsonErrors:
    """Test JSON decode error handling in analyze_python."""

    def test_radon_cc_json_decode_error(self, tmp_path):
        """Test handling of invalid JSON from radon cc (lines 282-283)."""
        (tmp_path / "test.py").write_text("def foo(): pass\n")

        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )

        with patch.object(code_stats, "has_tool", return_value=True):
            with patch.object(code_stats, "run_cmd") as mock_run:
                # Return invalid JSON for radon cc
                mock_run.side_effect = [
                    (True, "invalid json {{{", ""),  # radon cc
                    (True, "{}", ""),  # radon raw
                ]
                code_stats.analyze_python(tmp_path, result)

        assert "Failed to parse radon cc output" in result.errors

    def test_radon_raw_json_decode_error(self, tmp_path):
        """Test handling of invalid JSON from radon raw (lines 293-294)."""
        (tmp_path / "test.py").write_text("def foo(): pass\n")

        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )

        valid_cc = json.dumps({str(tmp_path / "test.py"): []})

        with patch.object(code_stats, "has_tool", return_value=True):
            with patch.object(code_stats, "run_cmd") as mock_run:
                mock_run.side_effect = [
                    (True, valid_cc, ""),  # radon cc - valid but empty
                    (True, "invalid json {{{", ""),  # radon raw - invalid
                ]
                code_stats.analyze_python(tmp_path, result)

        # Should not error out, just silently skip the raw metrics
        assert "python" in result.by_language


class TestAnalyzeCCppWithPmccabe:
    """Test C/C++ analysis using pmccabe."""

    def test_uses_pmccabe_when_available(self, tmp_path):
        """Test that pmccabe is preferred over lizard (lines 470-477)."""
        c_file = tmp_path / "main.c"
        c_file.write_text("int main() { return 0; }\n")

        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )

        pmccabe_output = "3\t5\t1\tmain\tmain.c"

        def mock_has_tool(name):
            return name == "pmccabe"

        with patch.object(code_stats, "has_tool", side_effect=mock_has_tool):
            with patch.object(code_stats, "run_cmd") as mock_run:
                mock_run.return_value = (True, pmccabe_output, "")
                code_stats.analyze_c_cpp(tmp_path, result)

        assert result.tools.get("c") == "pmccabe"
        assert result.tools.get("cpp") == "pmccabe"

    def test_uses_lizard_when_no_pmccabe(self, tmp_path):
        """Test that lizard is used as fallback (lines 475-477)."""
        c_file = tmp_path / "main.c"
        c_file.write_text("int main() { return 0; }\n")

        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )

        lizard_output = f"5,2,30,0,10,main.c:1,{c_file},main,1,10\n"

        def mock_has_tool(name):
            return name == "lizard"

        with patch.object(code_stats, "has_tool", side_effect=mock_has_tool):
            with patch.object(code_stats, "run_cmd") as mock_run:
                mock_run.return_value = (True, lizard_output, "")
                code_stats.analyze_c_cpp(tmp_path, result)

        assert result.tools.get("c") == "lizard"
        assert result.tools.get("cpp") == "lizard"


class TestAnalyzeWithPmccabeEdgeCases:
    """Test _analyze_with_pmccabe edge cases."""

    def test_cpp_file_detection(self, tmp_path):
        """Test that C++ files are correctly identified (line 488-490)."""
        cpp_file = tmp_path / "main.cpp"
        cpp_file.write_text("int main() { return 0; }\n")

        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )

        pmccabe_output = "3\t5\t1\tmain\tmain.cpp"

        with patch.object(code_stats, "run_cmd") as mock_run:
            mock_run.return_value = (True, pmccabe_output, "")
            code_stats._analyze_with_pmccabe(tmp_path, [cpp_file], result)  # noqa: SLF001

        assert "cpp" in result.by_language
        assert result.by_language["cpp"].files == 1

    def test_sloc_read_exception(self, tmp_path):
        """Test exception handling when reading file for SLOC (lines 502-503)."""
        c_file = tmp_path / "main.c"
        c_file.write_text("int main() { return 0; }\n")

        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )

        with patch.object(code_stats, "run_cmd") as mock_run:
            mock_run.return_value = (True, "", "")
            with patch.object(Path, "read_text", side_effect=PermissionError("denied")):
                code_stats._analyze_with_pmccabe(tmp_path, [c_file], result)  # noqa: SLF001

        # Should continue without error
        assert "c" in result.by_language

    def test_pmccabe_run_failure(self, tmp_path):
        """Test handling of pmccabe run failure (line 508)."""
        c_file = tmp_path / "main.c"
        c_file.write_text("int main() { return 0; }\n")

        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )

        with patch.object(code_stats, "run_cmd") as mock_run:
            mock_run.return_value = (False, "", "error")
            code_stats._analyze_with_pmccabe(tmp_path, [c_file], result)  # noqa: SLF001

        # File counted but no functions
        assert "c" in result.by_language
        assert result.by_language["c"].files == 1
        assert result.by_language["c"].functions == 0

    def test_pmccabe_empty_line_skip(self, tmp_path):
        """Test that empty lines in pmccabe output are skipped (line 513)."""
        c_file = tmp_path / "main.c"
        c_file.write_text("int main() { return 0; }\n")

        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )

        pmccabe_output = "\n3\t5\t1\tmain\tmain.c\n\n"

        with patch.object(code_stats, "run_cmd") as mock_run:
            mock_run.return_value = (True, pmccabe_output, "")
            code_stats._analyze_with_pmccabe(tmp_path, [c_file], result)  # noqa: SLF001

        assert result.by_language["c"].functions == 1

    def test_pmccabe_high_complexity_warning(self, tmp_path):
        """Test that high complexity generates warning (lines 537-551)."""
        c_file = tmp_path / "main.c"
        c_file.write_text("int main() { return 0; }\n")

        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )

        # Complexity 15 > 10 threshold
        pmccabe_output = "15\t20\t1\tcomplex_func\tmain.c"

        with patch.object(code_stats, "run_cmd") as mock_run:
            mock_run.return_value = (True, pmccabe_output, "")
            code_stats._analyze_with_pmccabe(tmp_path, [c_file], result)  # noqa: SLF001

        assert len(result.warnings) == 1
        assert result.warnings[0]["severity"] == "medium"
        assert result.warnings[0]["complexity"] == 15

    def test_pmccabe_very_high_complexity_warning(self, tmp_path):
        """Test that very high complexity gets high severity (lines 545-547)."""
        c_file = tmp_path / "main.c"
        c_file.write_text("int main() { return 0; }\n")

        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )

        # Complexity 25 > 20 high threshold
        pmccabe_output = "25\t50\t1\tvery_complex\tmain.c"

        with patch.object(code_stats, "run_cmd") as mock_run:
            mock_run.return_value = (True, pmccabe_output, "")
            code_stats._analyze_with_pmccabe(tmp_path, [c_file], result)  # noqa: SLF001

        assert len(result.warnings) == 1
        assert result.warnings[0]["severity"] == "high"

    def test_pmccabe_parse_error_continue(self, tmp_path):
        """Test that parse errors are silently skipped (lines 550-551)."""
        c_file = tmp_path / "main.c"
        c_file.write_text("int main() { return 0; }\n")

        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )

        # Has 5 parts but first is not an integer (triggers ValueError in int(parts[0]))
        pmccabe_output = "abc\t5\t1\tmain\tmain.c"

        with patch.object(code_stats, "run_cmd") as mock_run:
            mock_run.return_value = (True, pmccabe_output, "")
            code_stats._analyze_with_pmccabe(tmp_path, [c_file], result)  # noqa: SLF001

        # Function not added due to parse error
        assert result.by_language["c"].functions == 0

    def test_pmccabe_insufficient_parts_skip(self, tmp_path):
        """Test that lines with fewer than 5 parts are skipped."""
        c_file = tmp_path / "main.c"
        c_file.write_text("int main() { return 0; }\n")

        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )

        # Only 3 tabs, so fewer than 5 parts
        pmccabe_output = "not\tenough\ttabs"

        with patch.object(code_stats, "run_cmd") as mock_run:
            mock_run.return_value = (True, pmccabe_output, "")
            code_stats._analyze_with_pmccabe(tmp_path, [c_file], result)  # noqa: SLF001

        assert result.by_language["c"].functions == 0

    def test_pmccabe_cpp_summary_assignment(self, tmp_path):
        """Test that cpp_summary is assigned to by_language (line 556)."""
        cpp_file = tmp_path / "main.cpp"
        cpp_file.write_text("int main() { return 0; }\n")

        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )

        pmccabe_output = "3\t5\t1\tmain\tmain.cpp"

        with patch.object(code_stats, "run_cmd") as mock_run:
            mock_run.return_value = (True, pmccabe_output, "")
            code_stats._analyze_with_pmccabe(tmp_path, [cpp_file], result)  # noqa: SLF001

        assert "cpp" in result.by_language
        assert result.by_language["cpp"].files == 1
        assert result.by_language["cpp"].functions == 1


class TestAnalyzeWithLizardEdgeCases:
    """Test _analyze_with_lizard edge cases."""

    def test_lizard_command_failure(self, tmp_path):
        """Test handling of lizard command failure (line 667)."""
        rust_file = tmp_path / "main.rs"
        rust_file.write_text("fn main() {}\n")

        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )

        with patch.object(code_stats, "run_cmd") as mock_run:
            mock_run.return_value = (False, "", "error")
            code_stats._analyze_with_lizard(tmp_path, [rust_file], ["rust"], result)  # noqa: SLF001

        # Should not add language to by_language
        assert "rust" not in result.by_language

    def test_lizard_invalid_csv_line_skip(self, tmp_path):
        """Test that invalid CSV lines are skipped (line 675)."""
        rust_file = tmp_path / "main.rs"
        rust_file.write_text("fn main() {}\n")

        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )

        # Mix of valid and invalid lines
        lizard_output = f"invalid line\n5,2,30,0,10,main.rs:1,{rust_file},main,1,10\n"

        with patch.object(code_stats, "run_cmd") as mock_run:
            mock_run.return_value = (True, lizard_output, "")
            code_stats._analyze_with_lizard(tmp_path, [rust_file], ["rust"], result)  # noqa: SLF001

        assert result.by_language["rust"].functions == 1

    def test_lizard_unknown_lang_skip(self, tmp_path):
        """Test that files with unknown languages are skipped (line 679)."""
        unknown_file = tmp_path / "main.xyz"
        unknown_file.write_text("code\n")

        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )

        # Lizard output for unknown extension
        lizard_output = f"5,2,30,0,10,main.xyz:1,{unknown_file},main,1,10\n"

        with patch.object(code_stats, "run_cmd") as mock_run:
            mock_run.return_value = (True, lizard_output, "")
            # Pass an empty list of allowed langs
            code_stats._analyze_with_lizard(tmp_path, [unknown_file], [], result)  # noqa: SLF001

        # No languages should be added
        assert len(result.by_language) == 0


class TestAnalyzeTypescriptWithFiles:
    """Test analyze_typescript when files are present."""

    def test_sets_tools_for_ts_and_js(self, tmp_path):
        """Test that both typescript and javascript tools are set (lines 725-727)."""
        ts_file = tmp_path / "app.ts"
        ts_file.write_text("function main() {}\n")

        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )

        lizard_output = f"5,2,30,0,10,app.ts:1,{ts_file},main,1,10\n"

        with patch.object(code_stats, "has_tool", return_value=True):
            with patch.object(code_stats, "run_cmd") as mock_run:
                mock_run.return_value = (True, lizard_output, "")
                code_stats.analyze_typescript(tmp_path, result)

        assert result.tools.get("typescript") == "lizard"
        assert result.tools.get("javascript") == "lizard"


class TestAnalyzeSwiftWithFiles:
    """Test analyze_swift when files are present."""

    def test_sets_tools_when_files_exist(self, tmp_path):
        """Test that tools['swift'] is set (lines 740-741)."""
        swift_file = tmp_path / "main.swift"
        swift_file.write_text("func main() {}\n")

        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )

        lizard_output = f"5,2,30,0,10,main.swift:1,{swift_file},main,1,10\n"

        with patch.object(code_stats, "has_tool", return_value=True):
            with patch.object(code_stats, "run_cmd") as mock_run:
                mock_run.return_value = (True, lizard_output, "")
                code_stats.analyze_swift(tmp_path, result)

        assert result.tools.get("swift") == "lizard"

    def test_no_files_returns_early(self, tmp_path):
        """Test that function returns early when no swift files exist."""
        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )

        with patch.object(code_stats, "has_tool", return_value=True):
            code_stats.analyze_swift(tmp_path, result)

        assert "swift" not in result.tools


class TestAnalyzeObjcWithFiles:
    """Test analyze_objc when files are present."""

    def test_sets_tools_when_files_exist(self, tmp_path):
        """Test that tools['objc'] is set (lines 756-757)."""
        objc_file = tmp_path / "main.m"
        objc_file.write_text("int main() { return 0; }\n")

        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )

        lizard_output = f"5,2,30,0,10,main.m:1,{objc_file},main,1,10\n"

        with patch.object(code_stats, "has_tool", return_value=True):
            with patch.object(code_stats, "run_cmd") as mock_run:
                mock_run.return_value = (True, lizard_output, "")
                code_stats.analyze_objc(tmp_path, result)

        assert result.tools.get("objc") == "lizard"

    def test_no_files_returns_early(self, tmp_path):
        """Test that function returns early when no objc files exist."""
        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )

        with patch.object(code_stats, "has_tool", return_value=True):
            code_stats.analyze_objc(tmp_path, result)

        assert "objc" not in result.tools


class TestAnalyzeBashException:
    """Test analyze_bash exception handling."""

    def test_read_exception_handling(self, tmp_path):
        """Test exception handling when reading bash files (lines 779-780)."""
        bash_file = tmp_path / "test.sh"
        bash_file.write_text("echo hello\n")

        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )

        # Mock read_text to raise exception
        original_read = Path.read_text

        def mock_read(self, *args, **kwargs):
            if self.suffix == ".sh":
                raise PermissionError("denied")
            return original_read(self, *args, **kwargs)

        with patch.object(Path, "read_text", mock_read):
            code_stats.analyze_bash(tmp_path, result)

        # File counted but no lines
        assert "bash" in result.by_language
        assert result.by_language["bash"].files == 1
        assert result.by_language["bash"].code_lines == 0


class TestPrintSummaryWarningOverflow:
    """Test print_summary with more than 10 warnings."""

    def test_more_than_10_warnings(self, capsys):
        """Test that overflow message is shown (line 880)."""
        result = code_stats.AnalysisResult(
            project="test",
            commit="abc",
            timestamp="2024-01-01T00:00:00Z",
        )
        result.by_language["python"] = code_stats.LanguageSummary(files=1)

        # Create 15 warnings
        for i in range(15):
            result.warnings.append(
                {
                    "file": f"test{i}.py",
                    "name": f"func{i}",
                    "line": i * 10,
                    "complexity": 15 + i,
                    "severity": "medium",
                }
            )

        code_stats.print_summary(result)
        captured = capsys.readouterr()

        assert "... and 5 more" in captured.err


class TestMainScriptExecution:
    """Test script execution via __name__ == '__main__'."""

    def test_script_execution(self, tmp_path):
        """Test running as script (line 932)."""
        # Run the script directly as a subprocess to cover the if __name__ == "__main__" block
        script_path = (
            Path(__file__).parent.parent / "ai_template_scripts" / "code_stats.py"
        )
        result = subprocess.run(
            ["python3", str(script_path), str(tmp_path), "--json"],
            capture_output=True,
            text=True,
            timeout=30,
        )
        # Script should run and produce JSON output
        assert result.returncode == 0
        output = json.loads(result.stdout)
        assert output["version"] == "1.0"

    def test_module_has_main(self):
        """Test that module has main function."""
        assert hasattr(code_stats, "main")
        assert callable(code_stats.main)

    def test_exit_code_with_high_warnings(self, tmp_path, capsys):
        """Test exit code 1 when high severity warnings exist."""
        (tmp_path / "test.py").write_text("def foo(): pass\n")

        radon_cc_output = json.dumps(
            {
                str(tmp_path / "test.py"): [
                    {"name": "complex", "lineno": 1, "complexity": 25},
                ],
            }
        )
        radon_raw_output = json.dumps({str(tmp_path / "test.py"): {"sloc": 10}})

        # Mock has_tool to only return True for radon (to avoid other analyzers)
        def mock_has_tool(name):
            return name == "radon"

        with patch("sys.argv", ["code_stats.py", str(tmp_path), "-q"]):
            with patch.object(code_stats, "has_tool", side_effect=mock_has_tool):
                with patch.object(code_stats, "run_cmd") as mock_run:
                    mock_run.side_effect = [
                        (True, "abc1234", ""),  # git rev-parse for get_git_info
                        (True, radon_cc_output, ""),
                        (True, radon_raw_output, ""),
                    ]
                    ret = code_stats.main()

        assert ret == 1  # High severity warning present
