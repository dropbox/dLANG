// Suppress collapsible warnings - nested if/match structure is often clearer than let-chains
#![allow(clippy::collapsible_if)]
#![allow(clippy::collapsible_else_if)]

//! tswift-verify CLI: Verify Swift verification bundles using Z4 SMT solver.
//!
//! This CLI reads JSON verification bundles and verifies them using the Z4 SMT solver
//! (with optional Z3 fallback for non-linear arithmetic when built with `z3-fallback` feature).
//!
//! # Usage
//!
//! ```text
//! tswift-verify <bundle.json>           # Verify a single bundle file
//! tswift-verify -                       # Read bundle from stdin
//! tswift-verify --dir <path>            # Verify all .json files in directory
//! tswift-verify --sil <file.sil>        # Verify SIL file directly
//! tswift-verify --swift <file.swift>    # Compile Swift and verify
//! tswift-verify --help                  # Show help
//! ```
//!
//! # Output formats
//!
//! - `--json` - Output results as JSON (default for stdin)
//! - `--human` - Output human-readable summary (default for files)
//! - `--quiet` - Only output errors and failures
//! - `--quiet-progress` - Only output progress lines for FAIL/WARN

use std::env;
use std::fmt::Write as FmtWrite;
use std::fs;
use std::io::{self, IsTerminal, Read, Write};
use std::path::Path;
use std::process::{Command, ExitCode};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread;
use std::time::Duration;

use vc_ir_swift::{
    KaniVcResult, SwiftAutoVcResult, SwiftVcBundle, SwiftVerifyResponse, SwiftVerifyResult,
    VcProgressInfo, VerificationSummary,
    cache::{CacheManager, hash_sil_function},
    convert_bundle, kani_backend, kani_runner, parse_bundles_json, sil_parser, sil_to_vcir,
    verify_bundle, verify_bundle_with_progress,
};

/// Output format for CLI
#[derive(Clone, Copy, PartialEq, Eq)]
enum OutputFormat {
    Human,
    Json,
    Diagnostic,
    Quiet,
}

/// Color mode for CLI output
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ColorMode {
    Auto,
    Always,
    Never,
}

/// Progress mode for CLI output
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ProgressMode {
    Auto,
    Always,
    Never,
}

/// JSON progress mode for machine-parseable output
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum JsonProgressMode {
    Off,
    On,
}

/// Verbose mode for per-VC output in non-interactive mode
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum VerboseMode {
    Off,
    On,
}

/// Tracks counts and timing during verbose output for summary line
#[derive(Default)]
struct VerboseSummary {
    ok: u32,
    fail: u32,
    warn: u32,
    err: u32,
    total_time_seconds: f64,
}

impl VerboseSummary {
    const fn total(&self) -> u32 {
        self.ok + self.fail + self.warn + self.err
    }

    /// Add time from a verification result
    fn add_time(&mut self, time_seconds: f64) {
        self.total_time_seconds += time_seconds;
    }

    /// Print summary line to stderr (only if there were any VCs)
    fn print_summary(&self, use_color: bool) {
        if self.total() == 0 {
            return;
        }

        let (green, red, yellow, reset) = if use_color {
            (colors::GREEN, colors::RED, colors::YELLOW, colors::RESET)
        } else {
            ("", "", "", "")
        };

        eprintln!(
            "Verbose summary: {}{}{} OK, {}{}{} FAIL, {}{}{} WARN ({:.3}s)",
            green,
            self.ok,
            reset,
            if self.fail > 0 { red } else { "" },
            self.fail,
            if self.fail > 0 { reset } else { "" },
            if self.warn > 0 { yellow } else { "" },
            self.warn,
            if self.warn > 0 { reset } else { "" },
            self.total_time_seconds
        );
    }
}

/// Configuration for verification execution
#[allow(clippy::struct_excessive_bools)] // Config flags are simpler than enums here
struct VerifyConfig {
    format: OutputFormat,
    use_color: bool,
    use_progress: bool,
    use_verbose: bool,
    use_json_progress: bool,
    quiet_progress: bool,
    /// If set, write a JSON array of all UNKNOWN/TIMEOUT VCs to this file.
    emit_unknown_vcs_path: Option<String>,
    /// Enable incremental verification (use cache)
    use_incremental: bool,
    /// Custom cache directory (None = default location)
    cache_dir: Option<String>,
    /// If set, only verify functions originating from this Swift source file.
    ///
    /// This avoids verifying imported stdlib/internal functions when verifying a single file.
    filter_source_file: Option<String>,
    /// If set, export Kani proof harnesses to this directory.
    export_kani_dir: Option<String>,
    /// If true, run Kani verification after exporting harnesses.
    run_kani: bool,
    /// If true, use bitvector mode for Kani export (v351).
    /// Native Rust types (i8, i16, i32, i64) instead of i128 with bounds.
    kani_bitvector: bool,
}

/// Result of running verification on bundles
struct VerifyLoopResult {
    responses: Vec<SwiftVerifyResponse>,
    summary: VerificationSummary,
}

/// Mapping from VC identifiers to Kani harness module names.
///
/// This allows mapping Kani results back to individual VCs for per-VC reporting.
struct VcHarnessMapping {
    /// Map from (`function_name`, `vc_description`) -> `module_name`
    entries: std::collections::HashMap<(String, String), String>,
}

impl VcHarnessMapping {
    fn new() -> Self {
        Self {
            entries: std::collections::HashMap::new(),
        }
    }

    fn insert(&mut self, function_name: &str, vc_description: &str, module_name: &str) {
        self.entries.insert(
            (function_name.to_string(), vc_description.to_string()),
            module_name.to_string(),
        );
    }

    /// Get the module name for a VC
    fn get(&self, function_name: &str, vc_description: &str) -> Option<&String> {
        self.entries
            .get(&(function_name.to_string(), vc_description.to_string()))
    }
}

/// Result of Kani export including the mapping
struct KaniExportResult {
    /// The Kani run result (if --run-kani was used)
    run_result: Option<kani_runner::KaniRunResult>,
    /// Mapping from VCs to harness module names
    mapping: VcHarnessMapping,
}

/// Merge Kani results into verification responses for per-VC reporting.
///
/// This function maps Kani harness results back to individual VCs using the
/// harness naming convention and updates each `SwiftAutoVcResult` with its
/// corresponding Kani result.
fn merge_kani_results_into_responses(
    responses: &mut [SwiftVerifyResponse],
    kani_result: &kani_runner::KaniRunResult,
    mapping: &VcHarnessMapping,
) {
    // Build a map from module_name -> Kani harness result
    let mut harness_results: std::collections::HashMap<String, &kani_runner::KaniHarnessResult> =
        std::collections::HashMap::new();

    for result in &kani_result.results {
        let harness_name = match result {
            kani_runner::KaniHarnessResult::Success { harness_name, .. }
            | kani_runner::KaniHarnessResult::Failure { harness_name, .. }
            | kani_runner::KaniHarnessResult::Error { harness_name, .. } => harness_name,
        };

        // Kani reports harness names as "kani_harnesses::{module}::proof_{vc_name}"
        // Extract the module name from the harness name
        let parts: Vec<&str> = harness_name.split("::").collect();
        if parts.len() >= 2 {
            // The module name is the second-to-last component (before the proof function)
            let module_name = parts[parts.len() - 2];
            harness_results.insert(module_name.to_string(), result);
        }
    }

    // Update each response's auto_vc_results with Kani results
    for response in responses.iter_mut() {
        for vc_result in &mut response.auto_vc_results {
            // Look up the module name for this VC
            if let Some(module_name) = mapping.get(&response.function_name, &vc_result.description)
            {
                // Look up the Kani result for this module
                if let Some(kani_harness_result) = harness_results.get(module_name) {
                    vc_result.kani_result = Some(convert_kani_harness_result(kani_harness_result));
                }
            }
        }
    }
}

/// Convert a Kani harness result to a `KaniVcResult` for JSON output
fn convert_kani_harness_result(result: &kani_runner::KaniHarnessResult) -> KaniVcResult {
    match result {
        kani_runner::KaniHarnessResult::Success {
            harness_name,
            time_seconds,
        } => KaniVcResult::Verified {
            harness_name: harness_name.clone(),
            time_seconds: *time_seconds,
        },
        kani_runner::KaniHarnessResult::Failure {
            harness_name,
            description,
            time_seconds,
            ..
        } => KaniVcResult::Failed {
            harness_name: harness_name.clone(),
            description: description.clone(),
            time_seconds: *time_seconds,
        },
        kani_runner::KaniHarnessResult::Error {
            harness_name,
            message,
        } => KaniVcResult::Error {
            harness_name: harness_name.clone(),
            message: message.clone(),
        },
    }
}

/// Core verification loop shared between all verification entry points.
/// Returns None if verification encountered an error (error already printed).
#[allow(clippy::too_many_lines)]
fn run_verification_loop(
    bundles: Vec<vc_ir_swift::SwiftVcBundle>,
    source: &str,
    config: &VerifyConfig,
) -> Option<VerifyLoopResult> {
    let mut responses: Vec<SwiftVerifyResponse> = Vec::with_capacity(bundles.len());
    let mut summary = VerificationSummary {
        total_vcs: 0,
        verified: 0,
        trusted: 0,
        failed: 0,
        unknown: 0,
        timeout: 0,
        total_time_seconds: 0.0,
        spec_verified: 0,
        spec_failed: 0,
        spec_unknown: 0,
        auto_vc_verified: 0,
        auto_vc_failed: 0,
        auto_vc_unknown: 0,
    };

    let total = bundles.len();
    let is_tty = io::stderr().is_terminal();
    let mut progress_display = if config.use_progress {
        Some(progress::InteractiveProgress::new(
            is_tty,
            config.use_color,
            total,
            config.quiet_progress,
        ))
    } else {
        None
    };

    let mut verbose_summary = VerboseSummary::default();

    if let Some(ref mut p) = progress_display {
        if !config.quiet_progress {
            p.print_header(source);
        }
    }

    for bundle in bundles {
        if let Some(ref mut p) = progress_display {
            p.start_function(&bundle.function_name);
        }

        if config.use_json_progress {
            emit_json_function_start(&bundle.function_name, source);
        }

        let verbose_non_tty = config.use_verbose && !is_tty;
        let func_name = bundle.function_name.clone();

        let response = if progress_display.is_some()
            || config.use_verbose
            || config.use_json_progress
        {
            let vc_state = progress_display
                .as_ref()
                .map(progress::InteractiveProgress::vc_state);
            let mut progress_cb = |info: &VcProgressInfo| {
                if let Some(ref state) = vc_state {
                    state.reset(info.total_vcs);
                    state.set_completed(info.completed_vcs);
                }
                if verbose_non_tty {
                    emit_verbose_vc_line(info, &func_name, config.use_color, &mut verbose_summary);
                }
                if config.use_json_progress {
                    emit_json_vc_event(info, &func_name);
                }
            };
            match verify_bundle_with_progress(&bundle, &mut progress_cb) {
                Ok(r) => r,
                Err(e) => {
                    if let Some(ref mut p) = progress_display {
                        p.finish();
                    }
                    print_verification_error(
                        source,
                        &e.to_string(),
                        config.format,
                        config.use_color,
                    );
                    return None;
                }
            }
        } else {
            match verify_bundle(&bundle) {
                Ok(r) => r,
                Err(e) => {
                    print_verification_error(
                        source,
                        &e.to_string(),
                        config.format,
                        config.use_color,
                    );
                    return None;
                }
            }
        };

        if let Some(ref mut p) = progress_display {
            p.complete_function(
                &response.function_name,
                response.is_trusted,
                &response.summary,
            );
        }

        accumulate_summary(&mut summary, &response.summary);

        if config.use_json_progress {
            emit_json_function_complete(&response);
        }

        responses.push(response);
    }

    if let Some(ref mut p) = progress_display {
        p.finish();
    }

    if config.use_verbose && !is_tty {
        verbose_summary.print_summary(config.use_color);
    }

    if config.use_json_progress {
        emit_json_summary(&summary);
    }

    Some(VerifyLoopResult { responses, summary })
}

/// Emit a verbose per-VC line to stderr
fn emit_verbose_vc_line(
    info: &VcProgressInfo,
    func_name: &str,
    use_color: bool,
    verbose_summary: &mut VerboseSummary,
) {
    let time_s = result_time_seconds(&info.result);
    verbose_summary.add_time(time_s);
    let (status, status_color) = match &info.result {
        SwiftVerifyResult::Verified { .. } => {
            verbose_summary.ok += 1;
            ("OK", colors::GREEN)
        }
        SwiftVerifyResult::Failed { .. } => {
            verbose_summary.fail += 1;
            ("FAIL", colors::RED)
        }
        SwiftVerifyResult::Unknown { .. } | SwiftVerifyResult::Timeout { .. } => {
            verbose_summary.warn += 1;
            ("WARN", colors::YELLOW)
        }
        SwiftVerifyResult::Error { .. } => {
            verbose_summary.err += 1;
            ("ERR", colors::RED)
        }
    };
    let vc_type = if info.is_spec { "spec" } else { "auto" };
    let reset = if use_color { colors::RESET } else { "" };
    let color = if use_color { status_color } else { "" };
    eprintln!(
        "  [VC {}/{}] {} {} ({}): {}{}{} ({:.3}s)",
        info.completed_vcs,
        info.total_vcs,
        func_name,
        vc_type,
        info.vc_name,
        color,
        status,
        reset,
        time_s
    );
}

fn json_string(s: &str) -> String {
    // serde_json handles all necessary escaping (quotes, backslashes, control chars).
    serde_json::to_string(s).expect("JSON string serialization should not fail")
}

/// Emit JSON progress event for function start
fn emit_json_function_start(function_name: &str, source: &str) {
    let function_name = json_string(function_name);
    let source = json_string(source);
    eprintln!(r#"{{"event":"function_start","function":{function_name},"source":{source}}}"#);
}

/// Emit JSON progress event for VC completion
fn emit_json_vc_event(info: &VcProgressInfo, func_name: &str) {
    let time_s = result_time_seconds(&info.result);
    let status = match &info.result {
        SwiftVerifyResult::Verified { .. } => "ok",
        SwiftVerifyResult::Failed { .. } => "fail",
        SwiftVerifyResult::Unknown { .. } | SwiftVerifyResult::Timeout { .. } => "unknown",
        SwiftVerifyResult::Error { .. } => "error",
    };
    let vc_type = if info.is_spec { "spec" } else { "auto" };
    let func_name = json_string(func_name);
    let vc_name = json_string(&info.vc_name);
    eprintln!(
        r#"{{"event":"vc_complete","function":{},"vc":{},"vc_type":"{}","status":"{}","completed":{},"total":{},"time_seconds":{:.6}}}"#,
        func_name, vc_name, vc_type, status, info.completed_vcs, info.total_vcs, time_s
    );
}

/// Emit JSON progress event for function completion
fn emit_json_function_complete(response: &SwiftVerifyResponse) {
    let unknown = response.summary.unknown + response.summary.timeout;
    let function_name = json_string(&response.function_name);
    eprintln!(
        r#"{{"event":"function_complete","function":{},"verified":{},"trusted":{},"failed":{},"unknown":{},"time_seconds":{:.6}}}"#,
        function_name,
        response.summary.verified,
        response.summary.trusted,
        response.summary.failed,
        unknown,
        response.summary.total_time_seconds
    );
}

/// Emit JSON progress event for summary
fn emit_json_summary(summary: &VerificationSummary) {
    let unknown = summary.unknown + summary.timeout;
    eprintln!(
        r#"{{"event":"summary","total_vcs":{},"verified":{},"trusted":{},"failed":{},"unknown":{},"time_seconds":{:.6}}}"#,
        summary.total_vcs,
        summary.verified,
        summary.trusted,
        summary.failed,
        unknown,
        summary.total_time_seconds
    );
}

/// Accumulate summary statistics from a response
fn accumulate_summary(summary: &mut VerificationSummary, response_summary: &VerificationSummary) {
    summary.total_vcs += response_summary.total_vcs;
    summary.verified += response_summary.verified;
    summary.trusted += response_summary.trusted;
    summary.failed += response_summary.failed;
    summary.unknown += response_summary.unknown;
    summary.timeout += response_summary.timeout;
    summary.total_time_seconds += response_summary.total_time_seconds;
    summary.spec_verified += response_summary.spec_verified;
    summary.spec_failed += response_summary.spec_failed;
    summary.spec_unknown += response_summary.spec_unknown;
    summary.auto_vc_verified += response_summary.auto_vc_verified;
    summary.auto_vc_failed += response_summary.auto_vc_failed;
    summary.auto_vc_unknown += response_summary.auto_vc_unknown;
}

/// Print verification error in appropriate format
fn print_verification_error(source: &str, error: &str, format: OutputFormat, use_color: bool) {
    match format {
        OutputFormat::Json => {
            println!(r#"{{"error":"Verification error: {error}"}}"#);
        }
        OutputFormat::Diagnostic => {
            let (bold, reset, error_label) = if use_color {
                (
                    colors::BOLD,
                    colors::RESET,
                    format!("{}error:{}", colors::BOLD_RED, colors::RESET),
                )
            } else {
                ("", "", "error:".to_string())
            };
            // Note: No line:column - verification errors don't have source locations
            println!("{bold}{source}{reset}: {error_label} verification error: {error}");
        }
        _ => {
            eprintln!("{source}: Verification error: {error}");
        }
    }
}

/// Extract time from a `SwiftVerifyResult`
const fn result_time_seconds(result: &SwiftVerifyResult) -> f64 {
    match result {
        SwiftVerifyResult::Verified { time_seconds }
        | SwiftVerifyResult::Failed { time_seconds, .. }
        | SwiftVerifyResult::Unknown { time_seconds, .. } => *time_seconds,
        SwiftVerifyResult::Timeout { timeout_seconds } => *timeout_seconds,
        SwiftVerifyResult::Error { .. } => 0.0,
    }
}

// ANSI color codes
mod colors {
    pub const RESET: &str = "\x1b[0m";
    pub const BOLD: &str = "\x1b[1m";
    pub const GREEN: &str = "\x1b[32m";
    pub const YELLOW: &str = "\x1b[33m";
    pub const RED: &str = "\x1b[31m";
    pub const BOLD_RED: &str = "\x1b[1;31m";
    pub const BOLD_GREEN: &str = "\x1b[1;32m";
    pub const BOLD_YELLOW: &str = "\x1b[1;33m";
    pub const CYAN: &str = "\x1b[36m";
    pub const BOLD_CYAN: &str = "\x1b[1;36m";
    pub const CLEAR_LINE: &str = "\x1b[2K";
}

/// Interactive progress display with spinner for TTY terminals
mod progress {
    use super::{
        Arc, AtomicBool, Duration, Ordering, VerificationSummary, Write, colors, io, thread,
    };
    use std::sync::atomic::AtomicUsize;

    /// Spinner frames for animated progress (Braille pattern)
    const SPINNER_FRAMES: &[char] = &['⣾', '⣽', '⣻', '⢿', '⡿', '⣟', '⣯', '⣷'];
    /// Fallback spinner for non-unicode terminals
    const SPINNER_FRAMES_ASCII: &[char] = &['|', '/', '-', '\\'];
    /// Default progress bar width in characters
    const PROGRESS_BAR_WIDTH: usize = 20;
    /// Smaller progress bar for VC-level display
    const VC_PROGRESS_BAR_WIDTH: usize = 10;

    /// Render a progress bar string: [=====>    ] 50%
    pub fn render_progress_bar(completed: usize, total: usize, width: usize) -> String {
        if total == 0 {
            return format!("[{}]   0%", " ".repeat(width));
        }

        let percent = (completed * 100) / total;
        let filled = (completed * width) / total;
        let remaining = width.saturating_sub(filled);

        // Build the bar: filled part with '=' and arrow '>', then empty spaces
        let bar = if filled == 0 {
            " ".repeat(width)
        } else if filled >= width {
            // Fully complete
            "=".repeat(width)
        } else {
            // In progress: filled portion with arrow
            format!(
                "{}>{}",
                "=".repeat(filled.saturating_sub(1)),
                " ".repeat(remaining)
            )
        };

        format!("[{bar}] {percent:>3}%")
    }

    /// Shared state for VC-level progress within a function
    pub struct VcProgressState {
        /// Total VCs in current function
        pub vc_total: AtomicUsize,
        /// Completed VCs in current function
        pub vc_completed: AtomicUsize,
    }

    impl VcProgressState {
        pub const fn new() -> Self {
            Self {
                vc_total: AtomicUsize::new(0),
                vc_completed: AtomicUsize::new(0),
            }
        }

        pub fn reset(&self, total: usize) {
            self.vc_total.store(total, Ordering::Relaxed);
            self.vc_completed.store(0, Ordering::Relaxed);
        }

        pub fn set_completed(&self, completed: usize) {
            self.vc_completed.store(completed, Ordering::Relaxed);
        }

        pub fn get(&self) -> (usize, usize) {
            (
                self.vc_completed.load(Ordering::Relaxed),
                self.vc_total.load(Ordering::Relaxed),
            )
        }
    }

    /// Interactive progress bar for TTY output
    pub struct InteractiveProgress {
        is_tty: bool,
        use_color: bool,
        quiet_progress: bool,
        total: usize,
        completed: usize,
        elapsed_seconds: f64,
        spinner_stop: Option<Arc<AtomicBool>>,
        spinner_handle: Option<thread::JoinHandle<()>>,
        /// Shared state for per-VC progress (read by spinner thread)
        vc_state: Arc<VcProgressState>,
    }

    impl InteractiveProgress {
        /// Create a new interactive progress display
        pub fn new(is_tty: bool, use_color: bool, total: usize, quiet_progress: bool) -> Self {
            Self {
                is_tty,
                use_color,
                quiet_progress,
                total,
                completed: 0,
                elapsed_seconds: 0.0,
                spinner_stop: None,
                spinner_handle: None,
                vc_state: Arc::new(VcProgressState::new()),
            }
        }

        /// Get a reference to the VC progress state for updating from callbacks
        pub fn vc_state(&self) -> Arc<VcProgressState> {
            Arc::clone(&self.vc_state)
        }

        /// Start the spinner for a function (TTY only)
        pub fn start_function(&mut self, function_name: &str) {
            if !self.is_tty {
                return;
            }

            // Stop any existing spinner
            self.stop_spinner();

            // Reset VC progress for new function
            self.vc_state.reset(0);

            let stop_flag = Arc::new(AtomicBool::new(false));
            self.spinner_stop = Some(stop_flag.clone());

            let completed = self.completed;
            let total = self.total;
            let func_name = function_name.to_string();
            let use_color = self.use_color;
            let vc_state = Arc::clone(&self.vc_state);

            let handle = thread::spawn(move || {
                let frames = if std::env::var("TERM")
                    .is_ok_and(|t| t.contains("xterm") || t.contains("256color"))
                {
                    SPINNER_FRAMES
                } else {
                    SPINNER_FRAMES_ASCII
                };
                let mut frame_idx = 0;

                while !stop_flag.load(Ordering::Relaxed) {
                    let spinner = frames[frame_idx % frames.len()];
                    frame_idx += 1;

                    let cyan = if use_color { colors::BOLD_CYAN } else { "" };
                    let reset = if use_color { colors::RESET } else { "" };

                    // Truncate function name if too long
                    let display_name = if func_name.len() > 30 {
                        format!("{}...", &func_name[..27])
                    } else {
                        func_name.clone()
                    };

                    // Render function-level progress bar
                    let progress_bar = render_progress_bar(completed, total, PROGRESS_BAR_WIDTH);

                    // Get VC-level progress within current function
                    let (vc_completed, vc_total) = vc_state.get();
                    let vc_progress = if vc_total > 0 {
                        let vc_bar =
                            render_progress_bar(vc_completed, vc_total, VC_PROGRESS_BAR_WIDTH);
                        format!(" VC {vc_bar}")
                    } else {
                        String::new()
                    };

                    eprint!(
                        "\r{}{}{} {} Verifying {}...{}{}",
                        colors::CLEAR_LINE,
                        cyan,
                        spinner,
                        progress_bar,
                        display_name,
                        vc_progress,
                        reset
                    );
                    let _ = io::stderr().flush();

                    thread::sleep(Duration::from_millis(80));
                }
            });

            self.spinner_handle = Some(handle);
        }

        /// Stop the spinner
        fn stop_spinner(&mut self) {
            if let Some(stop_flag) = self.spinner_stop.take() {
                stop_flag.store(true, Ordering::Relaxed);
            }
            if let Some(handle) = self.spinner_handle.take() {
                let _ = handle.join();
            }
        }

        /// Complete a function and show result
        #[allow(clippy::cast_precision_loss)] // ETA precision loss is acceptable for UI
        pub fn complete_function(
            &mut self,
            function_name: &str,
            is_trusted: bool,
            summary: &VerificationSummary,
        ) {
            let verified = summary.verified;
            let trusted = summary.trusted;
            let failed = summary.failed;
            let unknown = summary.unknown + summary.timeout;
            let time_seconds = summary.total_time_seconds;

            self.stop_spinner();
            self.completed += 1;
            self.elapsed_seconds += time_seconds;

            // Calculate ETA
            let remaining = self.total.saturating_sub(self.completed);
            let avg = if self.completed > 0 {
                self.elapsed_seconds / (self.completed as f64)
            } else {
                0.0
            };
            let eta = avg * (remaining as f64);

            if self.quiet_progress && failed == 0 && unknown == 0 {
                if self.is_tty {
                    eprint!("\r{}", colors::CLEAR_LINE);
                    let _ = io::stderr().flush();
                }
                return;
            }

            if self.is_tty {
                // Clear spinner line and print result
                let (green, red, yellow, cyan, reset) = if self.use_color {
                    (
                        colors::GREEN,
                        colors::RED,
                        colors::YELLOW,
                        colors::BOLD_CYAN,
                        colors::RESET,
                    )
                } else {
                    ("", "", "", "", "")
                };

                let status = if failed > 0 {
                    format!("{red}FAIL{reset}")
                } else if unknown > 0 {
                    format!("{yellow}WARN{reset}")
                } else if is_trusted || trusted > 0 {
                    format!("{cyan}TRUSTED{reset}")
                } else {
                    format!("{green}OK{reset}")
                };

                let ok = verified.saturating_sub(trusted);
                let counts = if trusted > 0 {
                    format!("{ok} ok, {trusted} trusted, {failed} fail, {unknown} unk")
                } else {
                    format!("{ok} ok, {failed} fail, {unknown} unk")
                };

                // Truncate function name if needed
                let display_name = if function_name.len() > 30 {
                    format!("{}...", &function_name[..27])
                } else {
                    function_name.to_string()
                };

                // Render progress bar for completed state
                let progress_bar =
                    render_progress_bar(self.completed, self.total, PROGRESS_BAR_WIDTH);

                eprintln!(
                    "\r{}{} {} {} ({}) {:.2}s ETA {:.1}s",
                    colors::CLEAR_LINE,
                    progress_bar,
                    status,
                    display_name,
                    counts,
                    time_seconds,
                    eta
                );
            } else {
                // Non-TTY: simple line output with progress bar
                let progress_bar =
                    render_progress_bar(self.completed, self.total, PROGRESS_BAR_WIDTH);
                let ok = verified.saturating_sub(trusted);
                if trusted > 0 {
                    eprintln!(
                        "{progress_bar} {function_name}: {ok} verified, {trusted} trusted, {failed} failed, {unknown} unknown ({time_seconds:.3}s, ETA {eta:.1}s)"
                    );
                } else {
                    eprintln!(
                        "{progress_bar} {function_name}: {ok} verified, {failed} failed, {unknown} unknown ({time_seconds:.3}s, ETA {eta:.1}s)"
                    );
                }
            }
        }

        /// Print header line (e.g., "Verifying N functions from source")
        pub fn print_header(&self, source: &str) {
            if self.total > 0 {
                eprintln!("Verifying {} function(s) from {}", self.total, source);
            }
        }

        /// Finish progress display
        pub fn finish(&mut self) {
            self.stop_spinner();
        }
    }

    impl Drop for InteractiveProgress {
        fn drop(&mut self) {
            self.stop_spinner();
        }
    }
}

/// Determine if colors should be used based on mode and terminal detection
fn should_use_color(mode: ColorMode) -> bool {
    match mode {
        ColorMode::Always => true,
        ColorMode::Never => false,
        ColorMode::Auto => io::stdout().is_terminal(),
    }
}

/// Determine if progress output should be used based on mode and output format.
/// Progress is emitted on stderr so it never corrupts stdout (e.g. --json).
fn should_use_progress(mode: ProgressMode, format: OutputFormat) -> bool {
    match mode {
        ProgressMode::Always => true,
        ProgressMode::Never => false,
        ProgressMode::Auto => {
            if format == OutputFormat::Quiet {
                false
            } else {
                io::stderr().is_terminal()
            }
        }
    }
}

/// Parse --color flag from arguments
fn parse_color_mode(args: &[String]) -> ColorMode {
    for (i, arg) in args.iter().enumerate() {
        // Handle --color=value format
        if let Some(value) = arg.strip_prefix("--color=") {
            return match value {
                "always" => ColorMode::Always,
                "never" => ColorMode::Never,
                _ => ColorMode::Auto,
            };
        }
        // Handle --color value format
        if arg == "--color" {
            if let Some(value) = args.get(i + 1) {
                match value.as_str() {
                    "always" => return ColorMode::Always,
                    "never" => return ColorMode::Never,
                    "auto" => return ColorMode::Auto,
                    _ => {}
                }
            }
            return ColorMode::Auto;
        }
    }
    ColorMode::Auto
}

/// Parse --progress flag from arguments
fn parse_progress_mode(args: &[String]) -> ProgressMode {
    for (i, arg) in args.iter().enumerate() {
        // Handle --progress=value format
        if let Some(value) = arg.strip_prefix("--progress=") {
            return match value {
                "always" => ProgressMode::Always,
                "never" => ProgressMode::Never,
                _ => ProgressMode::Auto,
            };
        }
        // Handle --progress value format (or just --progress)
        if arg == "--progress" {
            if let Some(value) = args.get(i + 1) {
                match value.as_str() {
                    "always" => return ProgressMode::Always,
                    "never" => return ProgressMode::Never,
                    "auto" => return ProgressMode::Auto,
                    _ => {}
                }
            }
            return ProgressMode::Auto;
        }
    }
    ProgressMode::Never
}

/// Parse --verbose / -v flag from arguments
fn parse_verbose_mode(args: &[String]) -> VerboseMode {
    for arg in args {
        if arg == "--verbose" || arg == "-v" {
            return VerboseMode::On;
        }
    }
    VerboseMode::Off
}

/// Parse --json-progress flag from arguments
fn parse_json_progress_mode(args: &[String]) -> JsonProgressMode {
    for arg in args {
        if arg == "--json-progress" {
            return JsonProgressMode::On;
        }
    }
    JsonProgressMode::Off
}

/// Parse --cache-dir flag from arguments
fn parse_cache_dir(args: &[String]) -> Option<String> {
    for (i, arg) in args.iter().enumerate() {
        // Handle --cache-dir=value format
        if let Some(value) = arg.strip_prefix("--cache-dir=") {
            return Some(value.to_string());
        }
        // Handle --cache-dir value format
        if arg == "--cache-dir" {
            if let Some(value) = args.get(i + 1) {
                if !value.starts_with('-') {
                    return Some(value.clone());
                }
            }
        }
    }
    None
}

/// Parse --source-file flag from arguments.
///
/// Supports `--source-file=path` and `--source-file path` forms.
fn parse_source_file(args: &[String]) -> Option<String> {
    for (i, arg) in args.iter().enumerate() {
        if let Some(value) = arg.strip_prefix("--source-file=") {
            return Some(value.to_string());
        }
        if arg == "--source-file" {
            if let Some(value) = args.get(i + 1) {
                if !value.starts_with('-') {
                    return Some(value.clone());
                }
            }
        }
    }
    None
}

/// Parse --export-kani flag from arguments.
///
/// Supports `--export-kani=dir` and `--export-kani dir` forms.
fn parse_export_kani_dir(args: &[String]) -> Option<String> {
    for (i, arg) in args.iter().enumerate() {
        if let Some(value) = arg.strip_prefix("--export-kani=") {
            return Some(value.to_string());
        }
        if arg == "--export-kani" {
            if let Some(value) = args.get(i + 1) {
                if !value.starts_with('-') {
                    return Some(value.clone());
                }
            }
        }
    }
    None
}

/// Parse --run-kani flag from arguments.
fn parse_run_kani(args: &[String]) -> bool {
    args.iter().any(|arg| arg == "--run-kani")
}

/// Parse --kani-bitvector flag from arguments (v351).
fn parse_kani_bitvector(args: &[String]) -> bool {
    args.iter().any(|arg| arg == "--kani-bitvector")
}

/// Parse --emit-unknown-vcs flag from arguments.
///
/// Supports `--emit-unknown-vcs=path` and `--emit-unknown-vcs path` forms.
fn parse_emit_unknown_vcs_path(args: &[String]) -> Option<String> {
    for (i, arg) in args.iter().enumerate() {
        if let Some(value) = arg.strip_prefix("--emit-unknown-vcs=") {
            return Some(value.to_string());
        }
        if arg == "--emit-unknown-vcs" {
            if let Some(value) = args.get(i + 1) {
                if !value.starts_with('-') {
                    return Some(value.clone());
                }
            }
        }
    }
    None
}

#[allow(clippy::too_many_lines)]
fn main() -> ExitCode {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 || args.contains(&"--help".to_string()) || args.contains(&"-h".to_string()) {
        print_help();
        return ExitCode::SUCCESS;
    }

    // Parse flags
    let json_output = args.contains(&"--json".to_string());
    let quiet = args.contains(&"--quiet".to_string());
    let quiet_progress = args.contains(&"--quiet-progress".to_string());
    let diagnostic = args.contains(&"--diagnostic".to_string());
    let dir_mode = args.contains(&"--dir".to_string());
    let sil_mode = args.contains(&"--sil".to_string());
    let swift_mode = args.contains(&"--swift".to_string());

    // Parse --color flag (accepts --color=auto, --color=always, --color=never, or --color auto)
    let color_mode = parse_color_mode(&args);
    // Parse --progress flag (accepts --progress, --progress=auto/always/never, or --progress auto/always/never)
    let progress_mode = parse_progress_mode(&args);
    // Parse --verbose / -v flag for per-VC output in non-interactive mode
    let verbose_mode = parse_verbose_mode(&args);
    // Parse --json-progress flag for machine-parseable JSON lines on stderr
    let json_progress_mode = parse_json_progress_mode(&args);
    // Parse --incremental flag for incremental verification (use cache)
    let use_incremental = args.contains(&"--incremental".to_string());
    // Parse --cache-dir flag for custom cache directory
    let cache_dir = parse_cache_dir(&args);
    // Parse --source-file flag for source filtering
    let mut filter_source_file = parse_source_file(&args);
    // Parse --export-kani flag for exporting Kani proof harnesses
    let export_kani_dir = parse_export_kani_dir(&args);
    // Parse --run-kani flag for running Kani after exporting harnesses
    let run_kani = parse_run_kani(&args);
    // Parse --kani-bitvector flag for bitvector mode (v351)
    let kani_bitvector = parse_kani_bitvector(&args);
    // Parse --emit-unknown-vcs flag for emitting unknown VCs as JSON
    let emit_unknown_vcs_path = parse_emit_unknown_vcs_path(&args);

    if run_kani && export_kani_dir.is_none() {
        eprintln!("Error: --run-kani requires --export-kani=DIR");
        return ExitCode::from(2);
    }
    if kani_bitvector && export_kani_dir.is_none() {
        eprintln!("Error: --kani-bitvector requires --export-kani=DIR");
        return ExitCode::from(2);
    }
    if dir_mode && emit_unknown_vcs_path.is_some() {
        eprintln!("Error: --emit-unknown-vcs is not supported with --dir");
        return ExitCode::from(2);
    }
    if emit_unknown_vcs_path.as_deref() == Some("-") {
        eprintln!("Error: --emit-unknown-vcs requires a file path (not '-')");
        return ExitCode::from(2);
    }

    // Determine output format (priority: json > diagnostic > quiet > human)
    let format = if json_output {
        OutputFormat::Json
    } else if diagnostic {
        OutputFormat::Diagnostic
    } else if quiet {
        OutputFormat::Quiet
    } else {
        OutputFormat::Human
    };

    // Find the input path (first positional argument after options).
    // Be careful not to treat option values (e.g. "--color always") as the input path.
    let mut input: &str = "-";
    let mut i = 1;
    while i < args.len() {
        let arg = args[i].as_str();
        if arg == "--color" || arg == "--progress" {
            if let Some(value) = args.get(i + 1).map(String::as_str) {
                if matches!(value, "auto" | "always" | "never") {
                    i += 2;
                    continue;
                }
            }
            i += 1;
            continue;
        }
        if arg == "--cache-dir"
            || arg == "--source-file"
            || arg == "--export-kani"
            || arg == "--emit-unknown-vcs"
        {
            if let Some(value) = args.get(i + 1).map(String::as_str) {
                if !value.starts_with('-') {
                    i += 2;
                    continue;
                }
            }
            i += 1;
            continue;
        }

        if arg.starts_with('-') {
            i += 1;
            continue;
        }

        input = arg;
        break;
    }

    let use_color = should_use_color(color_mode);
    let use_progress = should_use_progress(progress_mode, format);
    let use_verbose = verbose_mode == VerboseMode::On;
    let use_json_progress = json_progress_mode == JsonProgressMode::On;

    if sil_mode {
        let config = VerifyConfig {
            format,
            use_color,
            use_progress,
            use_verbose,
            use_json_progress,
            quiet_progress,
            emit_unknown_vcs_path: emit_unknown_vcs_path.clone(),
            use_incremental,
            cache_dir,
            filter_source_file,
            export_kani_dir,
            run_kani,
            kani_bitvector,
        };
        verify_sil_file(input, &config)
    } else if swift_mode {
        // Default to filtering verification results to the Swift file being compiled.
        if filter_source_file.is_none() && input != "-" {
            filter_source_file = Some(input.to_string());
        }
        let config = VerifyConfig {
            format,
            use_color,
            use_progress,
            use_verbose,
            use_json_progress,
            quiet_progress,
            emit_unknown_vcs_path: emit_unknown_vcs_path.clone(),
            use_incremental,
            cache_dir,
            filter_source_file,
            export_kani_dir,
            run_kani,
            kani_bitvector,
        };
        verify_swift_file(input, &config)
    } else if dir_mode {
        verify_directory(
            input,
            format,
            use_color,
            use_progress,
            use_verbose,
            use_json_progress,
            quiet_progress,
        )
    } else if input == "-" {
        verify_stdin(
            format,
            use_color,
            use_progress,
            use_verbose,
            use_json_progress,
            quiet_progress,
            emit_unknown_vcs_path.clone(),
        )
    } else {
        let config = VerifyConfig {
            format,
            use_color,
            use_progress,
            use_verbose,
            use_json_progress,
            quiet_progress,
            emit_unknown_vcs_path: emit_unknown_vcs_path.clone(),
            use_incremental: false,
            cache_dir: None,
            filter_source_file,
            export_kani_dir: None,
            run_kani: false,
            kani_bitvector: false,
        };
        verify_file(input, &config)
    }
}

fn print_help() {
    eprintln!(
        r#"tswift-verify - Verify Swift verification bundles using Z4 SMT solver

USAGE:
    tswift-verify [OPTIONS] <INPUT>

ARGS:
    <INPUT>     Path to bundle file, SIL file, or Swift source file

OPTIONS:
    --sil           Input is a SIL file (from swiftc -emit-sil)
    --swift         Input is a Swift source file (invokes swiftc)
    --dir           Verify all .json files in the directory
    --json          Output results as JSON
    --human         Output human-readable summary (default)
    --diagnostic    Output compiler-style diagnostics (file:line:col: error: ...)
    --quiet         Only output errors and failures
    --quiet-progress Only output progress lines for FAIL/WARN (when progress enabled)
    --source-file=FILE Only verify functions from this Swift file
    --color=MODE    Color output: auto (default), always, never
    --progress=MODE Progress output: auto (with tty), always, never (default)
    -v, --verbose   Show per-VC progress in non-interactive mode (piped output)
    --json-progress Emit JSON Lines progress events to stderr (for IDE integration)
    --incremental   Enable incremental verification (cache results, skip unchanged)
    --cache-dir=DIR Custom cache directory (default: .tswift_cache/ in source dir)
    --emit-unknown-vcs=FILE Write all UNKNOWN/TIMEOUT VCs as JSON to FILE
    --export-kani=DIR Export a runnable Kani Cargo project to directory
    --run-kani      Run Kani on the exported project (requires --export-kani, cargo-kani)
    --kani-bitvector Use native Rust types (i8,i16,i32,i64) for exact overflow semantics
    -h, --help      Show this help message

EXAMPLES:
    tswift-verify bundle.json              # Verify JSON bundle
    tswift-verify --sil output.sil         # Verify SIL file directly
    tswift-verify --swift test.swift       # Compile and verify Swift
    tswift-verify --diagnostic test.swift  # Compiler-style errors
    tswift-verify --progress test.swift    # Stream progress to stderr
    tswift-verify -v test.swift 2>&1       # Verbose per-VC output (piped)
    tswift-verify --json-progress file.sil # JSON Lines progress to stderr
    cat bundle.json | tswift-verify -      # Read from stdin
    tswift-verify --dir ./bundles --json   # Verify directory
    tswift-verify --incremental --sil f.sil # Incremental verification (cache)
    tswift-verify --sil f.sil --export-kani ./harnesses  # Export Kani harnesses
    tswift-verify --sil f.sil --export-kani ./harnesses --run-kani  # Export and run Kani

OUTPUT:
    Exit code 0: All VCs verified
    Exit code 1: At least one VC failed or had errors
    Exit code 2: Input/parse error (or missing Kani when --run-kani is used)

DIAGNOSTIC FORMAT:
    --diagnostic outputs errors in compiler format for IDE integration:
    file.swift:42:10: error: overflow check failed

JSON PROGRESS FORMAT:
    --json-progress emits JSON Lines to stderr with these event types:
    {{"event":"function_start","function":"foo","source":"test.sil"}}
    {{"event":"vc_complete","function":"foo","vc":"overflow_check","status":"ok",...}}
    {{"event":"function_complete","function":"foo","verified":2,"failed":0,...}}
    {{"event":"summary","total_vcs":5,"verified":5,"failed":0,...}}
"#
    );
}

#[allow(clippy::fn_params_excessive_bools)] // Config bools are simpler than enum wrappers here
fn verify_stdin(
    format: OutputFormat,
    use_color: bool,
    use_progress: bool,
    use_verbose: bool,
    use_json_progress: bool,
    quiet_progress: bool,
    emit_unknown_vcs_path: Option<String>,
) -> ExitCode {
    let mut input = String::new();
    if let Err(e) = io::stdin().read_to_string(&mut input) {
        eprintln!("Error reading stdin: {e}");
        return ExitCode::from(2);
    }
    // stdin always uses JSON format for output since it's typically piped
    let effective_format = if format == OutputFormat::Human {
        OutputFormat::Json
    } else {
        format
    };
    let config = VerifyConfig {
        format: effective_format,
        use_color,
        use_progress,
        use_verbose,
        use_json_progress,
        quiet_progress,
        emit_unknown_vcs_path,
        use_incremental: false,
        cache_dir: None,
        filter_source_file: None,
        export_kani_dir: None,
        run_kani: false,
        kani_bitvector: false,
    };
    verify_bundles(&input, "<stdin>", &config)
}

fn verify_file(path: &str, config: &VerifyConfig) -> ExitCode {
    let content = match fs::read_to_string(path) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("Error reading file '{path}': {e}");
            return ExitCode::from(2);
        }
    };
    verify_bundles(&content, path, config)
}

#[allow(clippy::fn_params_excessive_bools)] // Config bools are simpler than enum wrappers here
fn verify_directory(
    path: &str,
    format: OutputFormat,
    use_color: bool,
    use_progress: bool,
    _use_verbose: bool,
    _use_json_progress: bool,
    quiet_progress: bool,
) -> ExitCode {
    let dir = match fs::read_dir(path) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("Error reading directory '{path}': {e}");
            return ExitCode::from(2);
        }
    };

    let mut total_verified = 0;
    let mut total_trusted = 0;
    let mut total_failed = 0;
    let mut total_unknown = 0;
    let mut file_count = 0;

    if use_progress && !quiet_progress {
        eprintln!("Verifying directory: {path}");
    }

    for entry in dir {
        let Ok(entry) = entry else {
            continue;
        };

        let path = entry.path();
        if path
            .extension()
            .is_some_and(|ext| ext == "json" || ext == "jsonl")
        {
            file_count += 1;
            if use_progress && !quiet_progress {
                eprintln!("[{file_count}] {}", path.display());
            }
            let content = match fs::read_to_string(&path) {
                Ok(c) => c,
                Err(e) => {
                    eprintln!("Error reading '{}': {}", path.display(), e);
                    total_failed += 1;
                    continue;
                }
            };

            match verify_bundles_internal(&content, path.to_string_lossy().as_ref()) {
                Ok(counts) => {
                    total_verified += counts.verified;
                    total_trusted += counts.trusted;
                    total_failed += counts.failed;
                    total_unknown += counts.unknown;
                }
                Err(()) => total_failed += 1,
            }
        }
    }

    match format {
        OutputFormat::Json => {
            println!(
                r#"{{"files":{file_count},"verified":{total_verified},"trusted":{total_trusted},"failed":{total_failed},"unknown":{total_unknown}}}"#
            );
        }
        OutputFormat::Diagnostic => {
            // Diagnostic mode doesn't output directory summary
        }
        OutputFormat::Quiet => {
            // Quiet mode only outputs if there are failures
            if total_failed > 0 {
                eprintln!("Verification failed: {total_failed} VCs failed");
            }
        }
        OutputFormat::Human => {
            let (green, cyan, red, yellow, reset) = if use_color {
                (
                    colors::BOLD_GREEN,
                    colors::BOLD_CYAN,
                    colors::BOLD_RED,
                    colors::BOLD_YELLOW,
                    colors::RESET,
                )
            } else {
                ("", "", "", "", "")
            };
            println!("\n=== Directory Summary ===");
            println!("Files processed: {file_count}");
            println!("VCs verified:    {green}{total_verified}{reset}");
            if total_trusted > 0 {
                println!("VCs trusted:     {cyan}{total_trusted}{reset}");
            }
            println!(
                "VCs failed:      {}{}{}",
                if total_failed > 0 { red } else { "" },
                total_failed,
                if total_failed > 0 { reset } else { "" }
            );
            println!(
                "VCs unknown:     {}{}{}",
                if total_unknown > 0 { yellow } else { "" },
                total_unknown,
                if total_unknown > 0 { reset } else { "" }
            );
        }
    }

    if total_failed > 0 {
        ExitCode::from(1)
    } else {
        ExitCode::SUCCESS
    }
}

struct VerifyCounts {
    verified: u32,
    trusted: u32,
    failed: u32,
    unknown: u32,
}

fn verify_bundles_internal(json: &str, source: &str) -> Result<VerifyCounts, ()> {
    let bundles = match parse_bundles_json(json) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("{source}: Parse error: {e}");
            return Err(());
        }
    };

    let mut verified = 0;
    let mut trusted = 0;
    let mut failed = 0;
    let mut unknown = 0;

    for bundle in bundles {
        let response = match verify_bundle(&bundle) {
            Ok(r) => r,
            Err(e) => {
                eprintln!("{source}: Verification error: {e}");
                return Err(());
            }
        };

        trusted += response.summary.trusted;
        verified += response
            .summary
            .verified
            .saturating_sub(response.summary.trusted);
        failed += response.summary.failed;
        unknown += response.summary.unknown + response.summary.timeout;
    }

    Ok(VerifyCounts {
        verified,
        trusted,
        failed,
        unknown,
    })
}

#[allow(clippy::too_many_lines)]
fn verify_bundles(json: &str, source: &str, config: &VerifyConfig) -> ExitCode {
    let bundles = match parse_bundles_json(json) {
        Ok(b) => b,
        Err(e) => {
            if config.format == OutputFormat::Json {
                println!(r#"{{"error":"Parse error: {e}"}}"#);
            } else {
                eprintln!("{source}: Parse error: {e}");
            }
            return ExitCode::from(2);
        }
    };

    let bundles = filter_bundles_by_source(bundles, config.filter_source_file.as_deref());
    let source_label = config.filter_source_file.as_deref().unwrap_or(source);

    let Some(result) = run_verification_loop(bundles, source_label, config) else {
        return ExitCode::from(2);
    };

    let VerifyLoopResult { responses, summary } = result;

    if let Some(path) = config.emit_unknown_vcs_path.as_deref() {
        if let Err(e) = write_unknown_vcs_file(path, &responses) {
            eprintln!("Error writing --emit-unknown-vcs output: {e}");
            return ExitCode::from(2);
        }
    }

    // Output results based on format
    match config.format {
        OutputFormat::Json => {
            if let Some(exit_code) = output_json_results(&responses, &summary) {
                return exit_code;
            }
        }
        OutputFormat::Diagnostic => {
            output_diagnostic_results(&responses, config.use_color);
        }
        OutputFormat::Human => {
            output_bundle_results(&responses, &summary, config.use_color);
        }
        OutputFormat::Quiet if summary.failed > 0 => {
            output_bundle_results(&responses, &summary, config.use_color);
        }
        OutputFormat::Quiet => {
            // No output for quiet mode when no failures
        }
    }

    if summary.failed > 0 {
        ExitCode::from(1)
    } else {
        ExitCode::SUCCESS
    }
}

#[derive(serde::Serialize)]
struct UnknownVcRecord {
    function_name: String,
    vc_type: String,
    description: String,
    source_file: String,
    source_line: u32,
    source_column: u32,
    reason: String,
    time_seconds: f64,
}

fn write_unknown_vcs_file(path: &str, responses: &[SwiftVerifyResponse]) -> Result<(), String> {
    let mut records = Vec::new();

    for response in responses {
        if let Some(spec_result) = &response.spec_result {
            match spec_result {
                SwiftVerifyResult::Unknown {
                    reason,
                    time_seconds,
                } => {
                    records.push(UnknownVcRecord {
                        function_name: response.function_name.clone(),
                        vc_type: "spec".to_string(),
                        description: "specification".to_string(),
                        source_file: response.source_file.clone(),
                        source_line: response.source_line,
                        source_column: 0,
                        reason: reason.clone(),
                        time_seconds: *time_seconds,
                    });
                }
                SwiftVerifyResult::Timeout { timeout_seconds } => {
                    records.push(UnknownVcRecord {
                        function_name: response.function_name.clone(),
                        vc_type: "spec".to_string(),
                        description: "specification".to_string(),
                        source_file: response.source_file.clone(),
                        source_line: response.source_line,
                        source_column: 0,
                        reason: "timeout".to_string(),
                        time_seconds: *timeout_seconds,
                    });
                }
                _ => {}
            }
        }

        for vc in &response.auto_vc_results {
            match &vc.result {
                SwiftVerifyResult::Unknown {
                    reason,
                    time_seconds,
                } => {
                    records.push(UnknownVcRecord {
                        function_name: response.function_name.clone(),
                        vc_type: "auto".to_string(),
                        description: vc.description.clone(),
                        source_file: vc.source_file.clone(),
                        source_line: vc.source_line,
                        source_column: vc.source_column,
                        reason: reason.clone(),
                        time_seconds: *time_seconds,
                    });
                }
                SwiftVerifyResult::Timeout { timeout_seconds } => {
                    records.push(UnknownVcRecord {
                        function_name: response.function_name.clone(),
                        vc_type: "auto".to_string(),
                        description: vc.description.clone(),
                        source_file: vc.source_file.clone(),
                        source_line: vc.source_line,
                        source_column: vc.source_column,
                        reason: "timeout".to_string(),
                        time_seconds: *timeout_seconds,
                    });
                }
                _ => {}
            }
        }
    }

    if let Some(parent) = Path::new(path).parent() {
        if !parent.as_os_str().is_empty() {
            fs::create_dir_all(parent)
                .map_err(|e| format!("create dir {}: {e}", parent.display()))?;
        }
    }

    let file = fs::File::create(path).map_err(|e| format!("open {path}: {e}"))?;
    serde_json::to_writer_pretty(file, &records).map_err(|e| format!("serialize JSON: {e}"))?;
    Ok(())
}

fn print_result(label: &str, result: &SwiftVerifyResult, use_color: bool) {
    let (green, red, yellow, reset) = if use_color {
        (
            colors::BOLD_GREEN,
            colors::BOLD_RED,
            colors::BOLD_YELLOW,
            colors::RESET,
        )
    } else {
        ("", "", "", "")
    };

    match result {
        SwiftVerifyResult::Verified { time_seconds } => {
            println!("  {label} {green}VERIFIED{reset} ({time_seconds:.3}s)");
        }
        SwiftVerifyResult::Failed {
            counterexample,
            time_seconds,
        } => {
            println!("  {label} {red}FAILED{reset} ({time_seconds:.3}s)");
            if !counterexample.is_empty() {
                println!("    Counterexample:");
                for (var, val) in counterexample {
                    println!("      {var} = {val}");
                }
            }
        }
        SwiftVerifyResult::Unknown {
            reason,
            time_seconds,
        } => {
            println!("  {label} {yellow}UNKNOWN{reset}: {reason} ({time_seconds:.3}s)");
        }
        SwiftVerifyResult::Timeout { timeout_seconds } => {
            println!("  {label} {yellow}TIMEOUT{reset} after {timeout_seconds:.3}s");
        }
        SwiftVerifyResult::Error { message } => {
            println!("  {label} {red}ERROR{reset}: {message}");
        }
    }
}

fn print_auto_vc_result(index: usize, vc_result: &SwiftAutoVcResult, use_color: bool) {
    // Format source location if available
    let loc_str = format_source_location(
        &vc_result.source_file,
        vc_result.source_line,
        vc_result.source_column,
    );

    let label = if loc_str.is_empty() {
        format!("Auto-VC #{} ({})", index, vc_result.description)
    } else {
        format!(
            "Auto-VC #{} ({}) at {}",
            index, vc_result.description, loc_str
        )
    };
    print_result(&label, &vc_result.result, use_color);

    // Print Kani result if present
    if let Some(ref kani_result) = vc_result.kani_result {
        let (cyan, green, red, yellow, reset) = if use_color {
            (
                colors::CYAN,
                colors::GREEN,
                colors::RED,
                colors::YELLOW,
                colors::RESET,
            )
        } else {
            ("", "", "", "", "")
        };

        let kani_status = match kani_result {
            KaniVcResult::Verified { time_seconds, .. } => {
                format!("{green}Kani: VERIFIED{reset} ({time_seconds:.3}s)")
            }
            KaniVcResult::Failed {
                description,
                time_seconds,
                ..
            } => {
                format!("{red}Kani: FAILED{reset} - {description} ({time_seconds:.3}s)")
            }
            KaniVcResult::Error { message, .. } => {
                format!("{yellow}Kani: ERROR{reset} - {message}")
            }
            KaniVcResult::NotExported { reason } => {
                format!("{cyan}Kani: not exported{reset} ({reason})")
            }
        };
        println!("         {kani_status}");
    }
}

/// Format source location as `file:line:col` or `file:line` or empty string.
fn format_source_location(file: &str, line: u32, col: u32) -> String {
    if file.is_empty() && line == 0 {
        return String::new();
    }

    let file_part = if file.is_empty() {
        "<unknown>".to_string()
    } else {
        // Use just the filename, not the full path, for readability
        std::path::Path::new(file)
            .file_name()
            .map_or_else(|| file.to_string(), |n| n.to_string_lossy().to_string())
    };

    if col > 0 {
        format!("{file_part}:{line}:{col}")
    } else if line > 0 {
        format!("{file_part}:{line}")
    } else {
        file_part
    }
}

/// Format source location with full path for compiler diagnostics.
/// Returns `file:line:col:` or `<unknown>:0:0:` format.
fn format_diagnostic_location(file: &str, line: u32, col: u32) -> String {
    let file_part = if file.is_empty() {
        "<unknown>".to_string()
    } else {
        file.to_string()
    };

    // Always output line:col for compiler format (use 1 as default for line/col)
    let l = if line == 0 { 1 } else { line };
    let c = if col == 0 { 1 } else { col };

    format!("{file_part}:{l}:{c}:")
}

/// Print compiler-style diagnostic for a verification result.
/// Format: file.swift:42:10: error: overflow check failed
fn print_diagnostic_result(
    file: &str,
    line: u32,
    col: u32,
    description: &str,
    result: &SwiftVerifyResult,
    suggestion: &str,
    use_color: bool,
) {
    let loc = format_diagnostic_location(file, line, col);

    let (error_label, warning_label, note_label, hint_label, reset) = if use_color {
        (
            format!("{}error:{}", colors::BOLD_RED, colors::RESET),
            format!("{}warning:{}", colors::BOLD_YELLOW, colors::RESET),
            format!("{}note:{}", colors::BOLD_CYAN, colors::RESET),
            format!("{}hint:{}", colors::BOLD_GREEN, colors::RESET),
            colors::RESET,
        )
    } else {
        (
            "error:".to_string(),
            "warning:".to_string(),
            "note:".to_string(),
            "hint:".to_string(),
            "",
        )
    };
    let bold = if use_color { colors::BOLD } else { "" };

    match result {
        SwiftVerifyResult::Verified { .. } => {
            // Optionally output success as a note (commented out by default)
            // println!("{} {} {} verified", loc, note_label, description);
        }
        SwiftVerifyResult::Failed { counterexample, .. } => {
            println!("{bold}{loc}{reset} {error_label} verification failed: {description}");
            if !counterexample.is_empty() {
                // Print counterexample as follow-up notes
                for (var, val) in counterexample {
                    println!("{bold}{loc}{reset} {note_label} counterexample: {var} = {val}");
                }
            }
            // Print suggestion if available
            if !suggestion.is_empty() {
                println!("{bold}{loc}{reset} {hint_label} {suggestion}");
            }
        }
        SwiftVerifyResult::Unknown { reason, .. } => {
            println!(
                "{bold}{loc}{reset} {warning_label} verification inconclusive: {description} ({reason})"
            );
        }
        SwiftVerifyResult::Timeout { timeout_seconds } => {
            println!(
                "{bold}{loc}{reset} {warning_label} verification timeout after {timeout_seconds:.1}s: {description}"
            );
        }
        SwiftVerifyResult::Error { message } => {
            println!(
                "{bold}{loc}{reset} {error_label} verification error: {description} ({message})"
            );
        }
    }
}

/// Export Kani proof harnesses for all VCs in the given bundles.
///
/// For each bundle, converts it to VC IR and exports each VC as a standalone Kani harness.
/// Unsupported VCs (e.g., containing constructs like Apply, Forall) are skipped with a warning.
///
/// Returns the export result including the VC-to-harness mapping, which can be used to
/// map Kani results back to individual VCs after running Kani.
#[allow(clippy::too_many_lines)]
fn export_kani_harnesses(
    bundles: &[SwiftVcBundle],
    output_dir: &str,
    use_color: bool,
    format: OutputFormat,
    run_kani: bool,
    kani_bitvector: bool,
) -> Result<KaniExportResult, kani_runner::KaniRunnerError> {
    let dir_path = Path::new(output_dir);

    // Create output directory if it doesn't exist
    fs::create_dir_all(dir_path).map_err(kani_runner::KaniRunnerError::WriteError)?;

    let src_dir = dir_path.join("src");
    fs::create_dir_all(&src_dir).map_err(kani_runner::KaniRunnerError::WriteError)?;

    // Create Cargo.toml if missing (do not clobber existing project).
    let cargo_toml_path = dir_path.join("Cargo.toml");
    if !cargo_toml_path.exists() {
        let cargo_toml_content = r#"[package]
name = "kani_harnesses"
version = "0.1.0"
edition = "2021"

[dependencies]
"#;
        fs::write(&cargo_toml_path, cargo_toml_content)
            .map_err(kani_runner::KaniRunnerError::WriteError)?;
    }

    let mut exported_count = 0;
    let mut skipped_count = 0;
    let mut module_names: Vec<String> = Vec::new();
    let mut used_modules: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut vc_mapping = VcHarnessMapping::new();

    for bundle in bundles {
        // Convert bundle to VC IR
        let fvcs = match convert_bundle(bundle) {
            Ok(f) => f,
            Err(e) => {
                if format != OutputFormat::Quiet {
                    eprintln!(
                        "Kani export: skipping {} - conversion error: {}",
                        bundle.function_name, e
                    );
                }
                continue;
            }
        };

        // Extract preconditions from fvcs.requires (v354)
        // Convert VcKind::Predicate to raw Predicate for kani::assume()
        let preconditions: Vec<vc_ir_swift::Predicate> = fvcs
            .requires
            .iter()
            .filter_map(|vc| match &vc.condition {
                vc_ir_swift::VcKind::Predicate(p) => Some(p.clone()),
                _ => None, // Skip non-predicate VCs (shouldn't happen for requires)
            })
            .collect();

        // Extract postconditions from fvcs.ensures (v355)
        // Convert VcKind::Predicate to raw Predicate for kani::assert()
        let postconditions: Vec<vc_ir_swift::Predicate> = fvcs
            .ensures
            .iter()
            .filter_map(|vc| match &vc.condition {
                vc_ir_swift::VcKind::Predicate(p) => Some(p.clone()),
                _ => None, // Skip non-predicate VCs (shouldn't happen for ensures)
            })
            .collect();

        // Configure Kani export mode (v351) with preconditions (v354) and postconditions (v355)
        let export_config = kani_backend::KaniExportConfig {
            bitvector_mode: kani_bitvector,
            preconditions,
            postconditions,
        };

        // Export each auto-VC (stored as assertions) as a separate harness
        for vc in &fvcs.assertions {
            match kani_backend::export_vc_to_kani_harness_with_config(
                &fvcs.signature,
                vc,
                &export_config,
            ) {
                Ok(harness_code) => {
                    // One Rust module per harness.
                    let base = format!(
                        "{}_{}",
                        sanitize_rust_module_name(&bundle.function_name),
                        sanitize_rust_module_name(&vc.name)
                    );
                    let mut module_name = base;
                    if module_name.is_empty() {
                        module_name.push_str("harness");
                    }
                    if used_modules.contains(&module_name) {
                        let mut i = 2_u32;
                        loop {
                            let candidate = format!("{module_name}_{i}");
                            if !used_modules.contains(&candidate) {
                                module_name = candidate;
                                break;
                            }
                            i += 1;
                        }
                    }
                    used_modules.insert(module_name.clone());

                    let filename = format!("{module_name}.rs");
                    let file_path = src_dir.join(&filename);

                    match fs::write(&file_path, &harness_code) {
                        Ok(()) => {
                            exported_count += 1;
                            module_names.push(module_name.clone());
                            // Track the mapping from (function_name, vc_description) -> module_name
                            // The VC description is used as the key since that's what's stored in SwiftAutoVcResult
                            vc_mapping.insert(&bundle.function_name, &vc.name, &module_name);
                        }
                        Err(e) => {
                            if format != OutputFormat::Quiet {
                                eprintln!("Kani export: failed to write {filename}: {e}");
                            }
                            skipped_count += 1;
                        }
                    }
                }
                Err(e) => {
                    // Unsupported construct - skip silently or with a debug message
                    skipped_count += 1;
                    if format == OutputFormat::Human && use_color {
                        // Only show in verbose human mode
                    }
                    let _ = e; // Suppress unused warning
                }
            }
        }
    }

    // If no harnesses were exported, create a dummy harness so `cargo kani` can run.
    if exported_count == 0 {
        let dummy = r#"#[kani::proof]
fn dummy_harness() {
    kani::assert(true, "no VCs exported");
}
"#;
        fs::write(src_dir.join("dummy.rs"), dummy)
            .map_err(kani_runner::KaniRunnerError::WriteError)?;
        module_names.push("dummy".to_string());
    }

    // Create src/lib.rs with module declarations (overwrite to reflect current export).
    let mut lib_content = String::new();
    for module_name in &module_names {
        let _ = writeln!(lib_content, "mod {module_name};");
    }
    fs::write(src_dir.join("lib.rs"), &lib_content)
        .map_err(kani_runner::KaniRunnerError::WriteError)?;

    // Print summary
    if format == OutputFormat::Human {
        let (green, yellow, reset) = if use_color {
            (colors::GREEN, colors::YELLOW, colors::RESET)
        } else {
            ("", "", "")
        };

        if exported_count > 0 || skipped_count > 0 {
            eprintln!(
                "Kani export: {green}{exported_count}{reset} harness(es) exported to {output_dir}, {yellow}{skipped_count}{reset} skipped"
            );
        }
    }

    // Run Kani if requested
    let run_result = if run_kani {
        Some(run_kani_verification(dir_path, use_color, format)?)
    } else {
        None
    };

    Ok(KaniExportResult {
        run_result,
        mapping: vc_mapping,
    })
}

/// Run Kani verification on exported harness files.
fn run_kani_verification(
    output_dir: &Path,
    use_color: bool,
    format: OutputFormat,
) -> Result<kani_runner::KaniRunResult, kani_runner::KaniRunnerError> {
    // Check if Kani is installed
    if !kani_runner::is_kani_available() {
        return Err(kani_runner::KaniRunnerError::KaniNotFound);
    }

    // Run cargo kani
    if format == OutputFormat::Human {
        let (cyan, reset) = if use_color {
            (colors::CYAN, colors::RESET)
        } else {
            ("", "")
        };
        eprintln!("{cyan}Running cargo kani...{reset}");
    }

    let output = Command::new("cargo")
        .arg("kani")
        .current_dir(output_dir)
        .output();

    let out = output.map_err(|e| kani_runner::KaniRunnerError::ExecutionError(e.to_string()))?;

    // Print Kani output (never to stdout in JSON mode).
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    match format {
        OutputFormat::Human => {
            if !stdout.is_empty() {
                println!("{stdout}");
            }
            if !stderr.is_empty() {
                eprintln!("{stderr}");
            }
        }
        OutputFormat::Json | OutputFormat::Diagnostic => {
            if !stdout.is_empty() {
                eprintln!("{stdout}");
            }
            if !stderr.is_empty() {
                eprintln!("{stderr}");
            }
        }
        OutputFormat::Quiet => {
            if !stderr.is_empty() {
                eprintln!("{stderr}");
            }
        }
    }

    let run_result = kani_runner::parse_kani_output(&out)?;

    // Summarize results
    if format == OutputFormat::Human {
        let (green, red, yellow, reset) = if use_color {
            (colors::GREEN, colors::RED, colors::YELLOW, colors::RESET)
        } else {
            ("", "", "", "")
        };

        if run_result.failed == 0 && run_result.errors == 0 {
            eprintln!(
                "{}Kani: {} harness(es) verified successfully ({:.3}s){}",
                green, run_result.successful, run_result.total_time_seconds, reset
            );
        } else {
            eprintln!(
                "{}Kani: {} ok, {}{}{} failed, {}{}{} errors ({:.3}s){}",
                yellow,
                run_result.successful,
                if run_result.failed > 0 { red } else { "" },
                run_result.failed,
                if run_result.failed > 0 { reset } else { "" },
                if run_result.errors > 0 { red } else { "" },
                run_result.errors,
                if run_result.errors > 0 { reset } else { "" },
                run_result.total_time_seconds,
                reset
            );
        }
    }

    Ok(run_result)
}

/// Sanitize a string for use as a Rust module identifier (and a filename stem).
fn sanitize_rust_module_name(name: &str) -> String {
    let mut out = String::with_capacity(name.len());
    for (i, c) in name.chars().enumerate() {
        if i == 0 {
            if c.is_ascii_alphabetic() || c == '_' {
                out.push(c.to_ascii_lowercase());
            } else {
                out.push('_');
            }
        } else if c.is_ascii_alphanumeric() || c == '_' {
            out.push(c.to_ascii_lowercase());
        } else {
            out.push('_');
        }
    }
    if out.is_empty() {
        out.push_str("harness");
    }
    out
}

/// Verify a SIL file directly
fn verify_sil_file(path: &str, config: &VerifyConfig) -> ExitCode {
    let sil_content = match fs::read_to_string(path) {
        Ok(c) => c,
        Err(e) => {
            if config.format == OutputFormat::Json {
                println!(r#"{{"error":"Failed to read SIL file: {e}"}}"#);
            } else {
                eprintln!("Error reading SIL file '{path}': {e}");
            }
            return ExitCode::from(2);
        }
    };

    let source_label = config.filter_source_file.as_deref().unwrap_or(path);
    verify_sil_content(&sil_content, source_label, config)
}

/// Locate the tSwiftMacrosPlugin executable if available.
///
/// Returns the plugin spec string (e.g., "/path/to/plugin#tSwiftMacrosPlugin") if found.
fn find_macro_plugin() -> Option<String> {
    // Get the binary's directory and try to find the project root
    let exe_path = env::current_exe().ok()?;
    let exe_dir = exe_path.parent()?;

    // Binary is typically at vc-ir-swift/target/{debug,release}/tswift-verify
    // Project root is vc-ir-swift/../ = tSwift/
    // Macro plugin is at tSwift/tswift-macros/.build/*/[release|debug]/tSwiftMacrosPlugin-tool

    // Try going up from the binary location
    let mut project_root = None;
    let mut dir = exe_dir;
    for _ in 0..5 {
        // Check if this looks like the tSwift project root (has tswift-macros/)
        let macros_dir = dir.join("tswift-macros");
        if macros_dir.is_dir() {
            project_root = Some(dir.to_path_buf());
            break;
        }
        dir = dir.parent()?;
    }

    let project_root = project_root?;
    let macros_build = project_root.join("tswift-macros").join(".build");

    // Look for the plugin executable in SwiftPM build directory
    // SwiftPM builds plugin executables with the "-tool" suffix
    if let Ok(entries) = fs::read_dir(&macros_build) {
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                // Check release first, then debug
                for build_type in ["release", "debug"] {
                    let plugin_path = path.join(build_type).join("tSwiftMacrosPlugin-tool");
                    if plugin_path.is_file() {
                        return Some(format!("{}#tSwiftMacrosPlugin", plugin_path.display()));
                    }
                }
            }
        }
    }

    None
}

/// Verify a Swift source file by compiling to SIL first
fn verify_swift_file(path: &str, config: &VerifyConfig) -> ExitCode {
    // Check that swiftc is available
    let swiftc = env::var("SWIFTC").unwrap_or_else(|_| "swiftc".to_string());

    // Detect if we're using swift-frontend directly (doesn't accept -Xfrontend)
    let is_swift_frontend = swiftc.contains("swift-frontend");

    // Try to find the macro plugin for @requires/@ensures support
    let macro_plugin = find_macro_plugin();

    // Build compilation arguments.
    //
    // Use `-g` to preserve SIL debug locations (`loc "file.swift":line:col`) so we can
    // report precise source diagnostics and filter to the user's file.
    // Avoid `-O` here; aggressive optimization can strip unused functions and hinder
    // verification of user-defined code.
    let base_args: Vec<&str> = vec!["-emit-sil", "-g", path];

    // Run swiftc -emit-sil (with macro plugin if available)
    let output = if let Some(ref plugin_spec) = macro_plugin {
        // First try with the macro plugin
        // swift-frontend uses -load-plugin-executable directly
        // swiftc uses -Xfrontend -load-plugin-executable -Xfrontend <spec>
        let args_with_plugin: Vec<&str> = if is_swift_frontend {
            let mut args = vec!["-load-plugin-executable", plugin_spec.as_str()];
            args.extend(base_args.iter().copied());
            args
        } else {
            let mut args = vec![
                "-Xfrontend",
                "-load-plugin-executable",
                "-Xfrontend",
                plugin_spec.as_str(),
            ];
            args.extend(base_args.iter().copied());
            args
        };

        match Command::new(&swiftc).args(&args_with_plugin).output() {
            Ok(o) if o.status.success() => o,
            Ok(o) => {
                // Check if failure was plugin-related; if so, retry without plugin
                let stderr = String::from_utf8_lossy(&o.stderr);
                if stderr.contains("load-plugin-executable")
                    || stderr.contains("plugin")
                    || stderr.contains("macro")
                {
                    // Retry without plugin
                    match Command::new(&swiftc).args(&base_args).output() {
                        Ok(o2) => o2,
                        Err(e) => {
                            if config.format == OutputFormat::Json {
                                println!(r#"{{"error":"Failed to run swiftc: {e}"}}"#);
                            } else {
                                eprintln!("Error running swiftc: {e}");
                                eprintln!(
                                    "Ensure swiftc is in your PATH or set SWIFTC environment variable"
                                );
                            }
                            return ExitCode::from(2);
                        }
                    }
                } else {
                    // Non-plugin-related error, return original output
                    o
                }
            }
            Err(e) => {
                if config.format == OutputFormat::Json {
                    println!(r#"{{"error":"Failed to run swiftc: {e}"}}"#);
                } else {
                    eprintln!("Error running swiftc: {e}");
                    eprintln!("Ensure swiftc is in your PATH or set SWIFTC environment variable");
                }
                return ExitCode::from(2);
            }
        }
    } else {
        // No plugin found, compile without it
        match Command::new(&swiftc).args(&base_args).output() {
            Ok(o) => o,
            Err(e) => {
                if config.format == OutputFormat::Json {
                    println!(r#"{{"error":"Failed to run swiftc: {e}"}}"#);
                } else {
                    eprintln!("Error running swiftc: {e}");
                    eprintln!("Ensure swiftc is in your PATH or set SWIFTC environment variable");
                }
                return ExitCode::from(2);
            }
        }
    };

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        if config.format == OutputFormat::Json {
            println!(
                r#"{{"error":"Swift compilation failed: {}"}}"#,
                stderr.trim()
            );
        } else {
            eprintln!("Swift compilation failed:");
            eprintln!("{stderr}");
        }
        return ExitCode::from(2);
    }

    let sil_content = String::from_utf8_lossy(&output.stdout);
    verify_sil_content(&sil_content, path, config)
}

/// Format a (line, caret) snippet for a parse error location.
fn format_source_snippet(input: &str, line: usize, column: usize) -> Option<(String, String)> {
    if line == 0 || column == 0 {
        return None;
    }

    let line_text = input.lines().nth(line.saturating_sub(1))?.to_string();
    let col = column.saturating_sub(1);
    let caret_pos = std::cmp::min(col, line_text.len());
    let caret_line = format!("{}^", " ".repeat(caret_pos));
    Some((line_text, caret_line))
}

/// Report SIL parse error in the appropriate format.
fn report_sil_parse_error(
    e: &sil_parser::SilParseError,
    source: &str,
    sil: &str,
    config: &VerifyConfig,
) {
    match config.format {
        OutputFormat::Json => {
            println!(
                r#"{{"error":"SIL parse error: {}","line":{},"column":{}}}"#,
                e, e.line, e.column
            );
        }
        OutputFormat::Diagnostic => {
            let (bold, reset, error_label) = if config.use_color {
                (
                    colors::BOLD,
                    colors::RESET,
                    format!("{}error:{}", colors::BOLD_RED, colors::RESET),
                )
            } else {
                ("", "", "error:".to_string())
            };
            let (line_text, caret_line) =
                format_source_snippet(sil, e.line, e.column).unwrap_or_default();

            println!(
                "{}{}:{}:{}:{} {} SIL parse error: {}",
                bold, source, e.line, e.column, reset, error_label, e.message
            );
            if !line_text.is_empty() {
                println!("  {line_text}");
                println!("  {caret_line}");
            }
        }
        OutputFormat::Human | OutputFormat::Quiet => {
            let (line_text, caret_line) =
                format_source_snippet(sil, e.line, e.column).unwrap_or_default();
            eprintln!(
                "{}:{}:{}: SIL parse error: {}",
                source, e.line, e.column, e.message
            );
            if !line_text.is_empty() {
                eprintln!("  {line_text}");
                eprintln!("  {caret_line}");
            }
        }
    }
}

/// Report SIL translation error in the appropriate format.
fn report_translation_error(
    e: &sil_to_vcir::SilTranslateError,
    source: &str,
    config: &VerifyConfig,
) {
    match config.format {
        OutputFormat::Json => {
            println!(r#"{{"error":"SIL translation error: {e}"}}"#);
        }
        OutputFormat::Diagnostic => {
            let (bold, reset, error_label) = if config.use_color {
                (
                    colors::BOLD,
                    colors::RESET,
                    format!("{}error:{}", colors::BOLD_RED, colors::RESET),
                )
            } else {
                ("", "", "error:".to_string())
            };
            println!("{bold}{source}{reset}: {error_label} SIL translation error: {e}");
        }
        OutputFormat::Human | OutputFormat::Quiet => {
            eprintln!("{source}: SIL translation error: {e}");
        }
    }
}

/// Output verification results in JSON format.
/// Returns Some(ExitCode) on error, None on success.
fn output_json_results(
    responses: &[SwiftVerifyResponse],
    summary: &VerificationSummary,
) -> Option<ExitCode> {
    if responses.len() == 1 {
        match serde_json::to_string_pretty(&responses[0]) {
            Ok(json) => println!("{json}"),
            Err(e) => {
                eprintln!("JSON serialization error: {e}");
                return Some(ExitCode::from(2));
            }
        }
    } else {
        #[derive(serde::Serialize)]
        struct MultiResponse<'a> {
            bundles: &'a [SwiftVerifyResponse],
            summary: &'a VerificationSummary,
        }

        let payload = MultiResponse {
            bundles: responses,
            summary,
        };

        match serde_json::to_string_pretty(&payload) {
            Ok(json) => println!("{json}"),
            Err(e) => {
                eprintln!("JSON serialization error: {e}");
                return Some(ExitCode::from(2));
            }
        }
    }
    None
}

/// Print function header for human-readable output.
fn print_function_header(response: &SwiftVerifyResponse) {
    let func_loc = format_source_location(&response.source_file, response.source_line, 0);
    let trusted_suffix = if response.is_trusted {
        " [TRUSTED]"
    } else {
        ""
    };

    if func_loc.is_empty() {
        println!("  Function: {}{}", response.function_name, trusted_suffix);
    } else {
        println!(
            "  Function: {} ({}){}",
            response.function_name, func_loc, trusted_suffix
        );
    }
}

/// Print verification summary line for human-readable output.
fn print_verification_summary(summary: &VerificationSummary, use_color: bool) {
    let verified = summary.verified.saturating_sub(summary.trusted);
    let trusted = summary.trusted;
    let unknown = summary.unknown + summary.timeout;

    let (green, red, yellow, cyan, reset) = if use_color {
        (
            colors::GREEN,
            colors::RED,
            colors::YELLOW,
            colors::BOLD_CYAN,
            colors::RESET,
        )
    } else {
        ("", "", "", "", "")
    };

    let failed_color = if summary.failed > 0 { red } else { "" };
    let failed_reset = if summary.failed > 0 { reset } else { "" };
    let unknown_color = if unknown > 0 { yellow } else { "" };
    let unknown_reset = if unknown > 0 { reset } else { "" };

    if trusted > 0 {
        println!(
            "\nSummary: {green}{verified}{reset} verified, {cyan}{trusted}{reset} trusted, \
             {failed_color}{}{failed_reset} failed, {unknown_color}{unknown}{unknown_reset} unknown ({:.3}s)",
            summary.failed, summary.total_time_seconds
        );
    } else {
        println!(
            "\nSummary: {green}{verified}{reset} verified, {failed_color}{}{failed_reset} failed, \
             {unknown_color}{unknown}{unknown_reset} unknown ({:.3}s)",
            summary.failed, summary.total_time_seconds
        );
    }
}

/// Output verification results in human-readable format.
fn output_human_results(
    responses: &[SwiftVerifyResponse],
    summary: &VerificationSummary,
    source: &str,
    use_color: bool,
) {
    let bold = if use_color { colors::BOLD } else { "" };
    let reset = if use_color { colors::RESET } else { "" };
    println!("{bold}=== {source} ==={reset}");

    for response in responses {
        print_function_header(response);

        // Print spec warnings (if any)
        for warning in &response.spec_warnings {
            let (yellow, reset) = if use_color {
                (colors::BOLD_YELLOW, colors::RESET)
            } else {
                ("", "")
            };
            println!("    {yellow}warning:{reset} {warning}");
        }

        // Print spec verification result
        if let Some(ref result) = response.spec_result {
            print_result("    Specification", result, use_color);
        }

        for (i, vc_result) in response.auto_vc_results.iter().enumerate() {
            print_auto_vc_result(i + 1, vc_result, use_color);
        }
    }

    print_verification_summary(summary, use_color);
}

/// Output verification results in diagnostic format (for IDE integration).
fn output_diagnostic_results(responses: &[SwiftVerifyResponse], use_color: bool) {
    for response in responses {
        if let Some(ref result) = response.spec_result {
            print_diagnostic_result(
                &response.source_file,
                response.source_line,
                0,
                &format!("specification for {}", response.function_name),
                result,
                "", // No suggestion for spec results yet
                use_color,
            );
        }

        for vc_result in &response.auto_vc_results {
            print_diagnostic_result(
                &vc_result.source_file,
                vc_result.source_line,
                vc_result.source_column,
                &vc_result.description,
                &vc_result.result,
                &vc_result.suggestion,
                use_color,
            );
        }
    }
}

/// Print per-bundle function header (different format from source file output).
fn print_bundle_function_header(response: &SwiftVerifyResponse, use_color: bool) {
    let func_loc = format_source_location(&response.source_file, response.source_line, 0);
    let bold = if use_color { colors::BOLD } else { "" };
    let reset = if use_color { colors::RESET } else { "" };
    let trusted_suffix = if response.is_trusted {
        " [TRUSTED]"
    } else {
        ""
    };

    if func_loc.is_empty() {
        println!(
            "{bold}=== {}{trusted_suffix} ==={reset}",
            response.function_name
        );
    } else {
        println!(
            "{bold}=== {} ({func_loc}){trusted_suffix} ==={reset}",
            response.function_name
        );
    }
}

/// Print per-bundle verification summary with trailing newline.
fn print_bundle_summary(summary: &VerificationSummary, use_color: bool) {
    let verified = summary.verified.saturating_sub(summary.trusted);
    let trusted = summary.trusted;
    let unknown = summary.unknown + summary.timeout;

    let (green, red, yellow, cyan, reset) = if use_color {
        (
            colors::GREEN,
            colors::RED,
            colors::YELLOW,
            colors::BOLD_CYAN,
            colors::RESET,
        )
    } else {
        ("", "", "", "", "")
    };

    let failed_color = if summary.failed > 0 { red } else { "" };
    let failed_reset = if summary.failed > 0 { reset } else { "" };
    let unknown_color = if unknown > 0 { yellow } else { "" };
    let unknown_reset = if unknown > 0 { reset } else { "" };

    if trusted > 0 {
        println!(
            "\nSummary: {green}{verified}{reset} verified, {cyan}{trusted}{reset} trusted, \
             {failed_color}{}{failed_reset} failed, {unknown_color}{unknown}{unknown_reset} unknown ({:.3}s)\n",
            summary.failed, summary.total_time_seconds
        );
    } else {
        println!(
            "\nSummary: {green}{verified}{reset} verified, {failed_color}{}{failed_reset} failed, \
             {unknown_color}{unknown}{unknown_reset} unknown ({:.3}s)\n",
            summary.failed, summary.total_time_seconds
        );
    }
}

/// Print overall summary header for multiple bundles.
fn print_overall_summary(summary: &VerificationSummary, use_color: bool) {
    let verified = summary.verified.saturating_sub(summary.trusted);
    let trusted = summary.trusted;
    let unknown = summary.unknown + summary.timeout;

    let (green, red, yellow, cyan, reset) = if use_color {
        (
            colors::GREEN,
            colors::RED,
            colors::YELLOW,
            colors::BOLD_CYAN,
            colors::RESET,
        )
    } else {
        ("", "", "", "", "")
    };

    let failed_color = if summary.failed > 0 { red } else { "" };
    let failed_reset = if summary.failed > 0 { reset } else { "" };
    let unknown_color = if unknown > 0 { yellow } else { "" };
    let unknown_reset = if unknown > 0 { reset } else { "" };

    if trusted > 0 {
        println!(
            "=== Overall Summary ===\nVCs: {green}{verified}{reset} verified, {cyan}{trusted}{reset} trusted, \
             {failed_color}{}{failed_reset} failed, {unknown_color}{unknown}{unknown_reset} unknown ({:.3}s)",
            summary.failed, summary.total_time_seconds
        );
    } else {
        println!(
            "=== Overall Summary ===\nVCs: {green}{verified}{reset} verified, {failed_color}{}{failed_reset} failed, \
             {unknown_color}{unknown}{unknown_reset} unknown ({:.3}s)",
            summary.failed, summary.total_time_seconds
        );
    }
}

/// Output bundle verification results in human-readable format (per-bundle summaries).
fn output_bundle_results(
    responses: &[SwiftVerifyResponse],
    summary: &VerificationSummary,
    use_color: bool,
) {
    for response in responses {
        print_bundle_function_header(response, use_color);

        // Print spec warnings (if any)
        for warning in &response.spec_warnings {
            let (yellow, reset) = if use_color {
                (colors::BOLD_YELLOW, colors::RESET)
            } else {
                ("", "")
            };
            println!("  {yellow}warning:{reset} {warning}");
        }

        if let Some(ref result) = response.spec_result {
            print_result("Specification", result, use_color);
        }

        for (i, vc_result) in response.auto_vc_results.iter().enumerate() {
            print_auto_vc_result(i + 1, vc_result, use_color);
        }

        print_bundle_summary(&response.summary, use_color);
    }

    if responses.len() > 1 {
        print_overall_summary(summary, use_color);
    }
}

/// Helper to translate functions incrementally with cache support.
/// Returns (`bundles_to_verify`, `cached_responses`).
fn translate_functions_incrementally(
    module: &sil_parser::SilModule,
    cache_manager: &mut Option<CacheManager>,
    source: &str,
    config: &VerifyConfig,
) -> (Vec<vc_ir_swift::SwiftVcBundle>, Vec<SwiftVerifyResponse>) {
    let mut bundles_to_verify = Vec::new();
    let mut cached = Vec::new();

    for func in &module.functions {
        // Skip functions without blocks (external declarations)
        if func.blocks.is_empty() {
            continue;
        }

        let hash = hash_sil_function(func);

        // Check cache
        if let Some(cm) = cache_manager {
            if let Some(cached_response) = cm.get(&hash) {
                cached.push(cached_response.clone());
                continue;
            }
        }

        // Translate this function
        match sil_to_vcir::translate_function_to_vcir(func) {
            Ok(bundle) => {
                bundles_to_verify.push(bundle);
            }
            Err(e) => {
                if config.format != OutputFormat::Quiet {
                    let name = func.demangled_name.as_deref().unwrap_or(&func.name);
                    eprintln!("{source}: Translation error for {name}: {e}");
                }
                // Continue with other functions
            }
        }
    }

    (bundles_to_verify, cached)
}

/// Helper to store newly verified responses in the cache.
fn store_responses_in_cache(
    cache_manager: &mut Option<CacheManager>,
    module: &sil_parser::SilModule,
    responses: &[SwiftVerifyResponse],
) {
    let Some(cm) = cache_manager else {
        return;
    };

    for response in responses {
        // Compute hash for this function by finding it in the module
        for func in &module.functions {
            let name = func.demangled_name.as_deref().unwrap_or(&func.name);
            if name == response.function_name || func.name == response.function_name {
                let hash = hash_sil_function(func);
                cm.insert(hash, response.function_name.clone(), response.clone());
                break;
            }
        }
    }
}

/// Verify SIL content (shared between --sil and --swift modes)
#[allow(clippy::too_many_lines)]
fn verify_sil_content(sil: &str, source: &str, config: &VerifyConfig) -> ExitCode {
    // Parse SIL
    let module = match sil_parser::parse_sil(sil) {
        Ok(m) => m,
        Err(e) => {
            report_sil_parse_error(&e, source, sil, config);
            return ExitCode::from(2);
        }
    };

    // Set up cache if incremental mode is enabled
    let mut cache_manager = if config.use_incremental {
        let cache_path = config.cache_dir.as_ref().map_or_else(
            || vc_ir_swift::cache::cache_path_for_source(Path::new(source)),
            |dir| {
                let cache_dir = Path::new(dir);
                let _ = fs::create_dir_all(cache_dir);
                let basename = Path::new(source)
                    .file_name()
                    .and_then(|n| n.to_str())
                    .unwrap_or("unknown");
                cache_dir.join(format!("{basename}.cache.json"))
            },
        );
        Some(CacheManager::with_path(cache_path, true))
    } else {
        None
    };

    // For incremental mode, translate and verify per-function with caching
    // For non-incremental mode, translate the whole module at once
    let (bundles, cached_responses) = if config.use_incremental {
        translate_functions_incrementally(&module, &mut cache_manager, source, config)
    } else {
        // Non-incremental: translate whole module
        let bundles = match sil_to_vcir::translate_sil_to_vcir(&module) {
            Ok(b) => b,
            Err(e) => {
                report_translation_error(&e, source, config);
                return ExitCode::from(2);
            }
        };
        (bundles, Vec::new())
    };

    let bundles = filter_bundles_by_source(bundles, config.filter_source_file.as_deref());
    let cached_responses =
        filter_responses_by_source(cached_responses, config.filter_source_file.as_deref());

    // Export Kani harnesses if requested
    let mut kani_export_result: Option<KaniExportResult> = None;
    if let Some(ref export_dir) = config.export_kani_dir {
        match export_kani_harnesses(
            &bundles,
            export_dir,
            config.use_color,
            config.format,
            config.run_kani,
            config.kani_bitvector,
        ) {
            Ok(r) => kani_export_result = Some(r),
            Err(kani_runner::KaniRunnerError::KaniNotFound) => {
                eprintln!(
                    "Error: Kani is not installed or not in PATH. Install with: cargo install --locked kani-verifier && cargo kani setup"
                );
                return ExitCode::from(2);
            }
            Err(e) => {
                eprintln!("Kani export/run error: {e}");
                return ExitCode::from(2);
            }
        }
    }

    // Check if we have anything to verify or report
    if bundles.is_empty() && cached_responses.is_empty() {
        if config.format == OutputFormat::Json {
            println!(r#"{{"warning":"No functions with verification conditions found"}}"#);
        } else if config.format == OutputFormat::Human {
            println!("{source}: No functions with verification conditions found");
        }
        // Diagnostic and Quiet modes don't output anything for empty results
        return ExitCode::SUCCESS;
    }

    // Verify uncached bundles
    let (mut responses, mut summary) = if bundles.is_empty() {
        // All functions were cached, no new verification needed
        (Vec::new(), VerificationSummary::default())
    } else {
        match run_verification_loop(bundles, source, config) {
            Some(r) => (r.responses, r.summary),
            None => return ExitCode::from(2),
        }
    };

    // For incremental mode, store new results in cache and merge with cached
    if config.use_incremental {
        store_responses_in_cache(&mut cache_manager, &module, &responses);

        // Merge cached responses with newly verified ones
        if !cached_responses.is_empty() {
            responses.extend(cached_responses);

            // Recompute summary to include cached results
            summary = VerificationSummary::default();
            for response in &responses {
                accumulate_summary(&mut summary, &response.summary);
            }

            // Print cache stats if verbose
            if config.use_verbose {
                if let Some(ref cm) = cache_manager {
                    let (hits, misses) = cm.statistics();
                    if hits > 0 || misses > 0 {
                        eprintln!("Cache: {hits} hits, {misses} misses");
                    }
                }
            }
        }
    }

    let VerifyLoopResult {
        mut responses,
        summary,
    } = VerifyLoopResult { responses, summary };

    // Merge Kani results into responses for per-VC reporting
    if let Some(ref kani_export) = kani_export_result {
        if let Some(ref kani_run) = kani_export.run_result {
            merge_kani_results_into_responses(&mut responses, kani_run, &kani_export.mapping);
        }
    }

    // Write UNKNOWN/TIMEOUT VCs to file if requested
    if let Some(path) = config.emit_unknown_vcs_path.as_deref() {
        if let Err(e) = write_unknown_vcs_file(path, &responses) {
            eprintln!("Error writing --emit-unknown-vcs output: {e}");
            return ExitCode::from(2);
        }
    }

    // Output results based on format
    match config.format {
        OutputFormat::Json => {
            if let Some(exit_code) = output_json_results(&responses, &summary) {
                return exit_code;
            }
        }
        OutputFormat::Diagnostic => {
            for response in &responses {
                for vc_result in &response.auto_vc_results {
                    print_diagnostic_result(
                        &vc_result.source_file,
                        vc_result.source_line,
                        vc_result.source_column,
                        &vc_result.description,
                        &vc_result.result,
                        &vc_result.suggestion,
                        config.use_color,
                    );
                }
            }
        }
        OutputFormat::Human => {
            output_human_results(&responses, &summary, source, config.use_color);
        }
        OutputFormat::Quiet if summary.failed > 0 => {
            output_human_results(&responses, &summary, source, config.use_color);
        }
        OutputFormat::Quiet => {
            // No output for quiet mode when no failures
        }
    }

    let kani_failed = kani_export_result
        .as_ref()
        .and_then(|e| e.run_result.as_ref())
        .is_some_and(|r| r.failed > 0 || r.errors > 0);

    if summary.failed > 0 || kani_failed {
        ExitCode::from(1)
    } else {
        ExitCode::SUCCESS
    }
}

fn filter_bundles_by_source(
    bundles: Vec<vc_ir_swift::SwiftVcBundle>,
    filter_source_file: Option<&str>,
) -> Vec<vc_ir_swift::SwiftVcBundle> {
    let Some(filter) = filter_source_file else {
        return bundles;
    };
    bundles
        .into_iter()
        .filter(|b| paths_match(&b.source_file, filter))
        .collect()
}

fn filter_responses_by_source(
    responses: Vec<SwiftVerifyResponse>,
    filter_source_file: Option<&str>,
) -> Vec<SwiftVerifyResponse> {
    let Some(filter) = filter_source_file else {
        return responses;
    };
    responses
        .into_iter()
        .filter(|r| paths_match(&r.source_file, filter))
        .collect()
}

fn paths_match(source_file: &str, filter_source_file: &str) -> bool {
    if source_file.is_empty() {
        return false;
    }
    if filter_source_file.is_empty() {
        return true;
    }
    if source_file == filter_source_file {
        return true;
    }

    let source_path = Path::new(source_file);
    let filter_path = Path::new(filter_source_file);

    if let (Ok(a), Ok(b)) = (fs::canonicalize(source_path), fs::canonicalize(filter_path)) {
        if a == b {
            return true;
        }
    }

    // Fallback: handle absolute vs relative comparisons.
    // Prefer suffix matching because SIL debug paths are often relative.
    source_file.ends_with(filter_source_file) || filter_source_file.ends_with(source_file)
}

#[cfg(test)]
mod tests {
    use super::*;

    // ============================================================
    // Tests for json_string
    // ============================================================

    #[test]
    fn test_json_string_simple() {
        let result = json_string("hello");
        assert_eq!(result, "\"hello\"");
    }

    #[test]
    fn test_json_string_with_quotes() {
        let result = json_string("say \"hello\"");
        assert_eq!(result, "\"say \\\"hello\\\"\"");
    }

    #[test]
    fn test_json_string_with_backslash() {
        let result = json_string("path\\to\\file");
        assert_eq!(result, "\"path\\\\to\\\\file\"");
    }

    #[test]
    fn test_json_string_with_newline() {
        let result = json_string("line1\nline2");
        assert_eq!(result, "\"line1\\nline2\"");
    }

    #[test]
    fn test_json_string_with_tab() {
        let result = json_string("col1\tcol2");
        assert_eq!(result, "\"col1\\tcol2\"");
    }

    #[test]
    fn test_json_string_empty() {
        let result = json_string("");
        assert_eq!(result, "\"\"");
    }

    #[test]
    fn test_json_string_unicode() {
        let result = json_string("日本語");
        assert_eq!(result, "\"日本語\"");
    }

    #[test]
    fn test_json_string_control_chars() {
        let result = json_string("\x00\x01\x02");
        // Control characters should be escaped
        assert!(result.starts_with('"') && result.ends_with('"'));
        assert!(result.contains("\\u"));
    }

    // ============================================================
    // Tests for result_time_seconds
    // ============================================================

    #[test]
    fn test_result_time_seconds_verified() {
        let result = SwiftVerifyResult::Verified { time_seconds: 1.5 };
        assert!((result_time_seconds(&result) - 1.5).abs() < 0.001);
    }

    #[test]
    fn test_result_time_seconds_failed() {
        let result = SwiftVerifyResult::Failed {
            time_seconds: 2.3,
            counterexample: Vec::new(),
        };
        assert!((result_time_seconds(&result) - 2.3).abs() < 0.001);
    }

    #[test]
    fn test_result_time_seconds_unknown() {
        let result = SwiftVerifyResult::Unknown {
            time_seconds: 3.1,
            reason: "solver returned unknown".to_string(),
        };
        assert!((result_time_seconds(&result) - 3.1).abs() < 0.001);
    }

    #[test]
    fn test_result_time_seconds_timeout() {
        let result = SwiftVerifyResult::Timeout {
            timeout_seconds: 60.0,
        };
        assert!((result_time_seconds(&result) - 60.0).abs() < 0.001);
    }

    #[test]
    fn test_result_time_seconds_error() {
        let result = SwiftVerifyResult::Error {
            message: "internal error".to_string(),
        };
        assert!((result_time_seconds(&result) - 0.0).abs() < 0.001);
    }

    // ============================================================
    // Tests for should_use_color
    // ============================================================

    #[test]
    fn test_should_use_color_always() {
        assert!(should_use_color(ColorMode::Always));
    }

    #[test]
    fn test_should_use_color_never() {
        assert!(!should_use_color(ColorMode::Never));
    }

    // Note: Auto mode depends on terminal detection, so we can't easily test it

    // ============================================================
    // Tests for should_use_progress
    // ============================================================

    #[test]
    fn test_should_use_progress_always() {
        assert!(should_use_progress(
            ProgressMode::Always,
            OutputFormat::Human
        ));
        assert!(should_use_progress(
            ProgressMode::Always,
            OutputFormat::Json
        ));
        assert!(should_use_progress(
            ProgressMode::Always,
            OutputFormat::Quiet
        ));
    }

    #[test]
    fn test_should_use_progress_never() {
        assert!(!should_use_progress(
            ProgressMode::Never,
            OutputFormat::Human
        ));
        assert!(!should_use_progress(
            ProgressMode::Never,
            OutputFormat::Json
        ));
    }

    #[test]
    fn test_should_use_progress_auto_quiet() {
        // Auto + Quiet format always returns false
        assert!(!should_use_progress(
            ProgressMode::Auto,
            OutputFormat::Quiet
        ));
    }

    // ============================================================
    // Tests for parse_color_mode
    // ============================================================

    #[test]
    fn test_parse_color_mode_default() {
        let args: Vec<String> = vec!["tswift-verify".to_string(), "file.json".to_string()];
        assert_eq!(parse_color_mode(&args), ColorMode::Auto);
    }

    #[test]
    fn test_parse_color_mode_always_equals() {
        let args: Vec<String> = vec![
            "tswift-verify".to_string(),
            "--color=always".to_string(),
            "file.json".to_string(),
        ];
        assert_eq!(parse_color_mode(&args), ColorMode::Always);
    }

    #[test]
    fn test_parse_color_mode_never_equals() {
        let args: Vec<String> = vec![
            "tswift-verify".to_string(),
            "--color=never".to_string(),
            "file.json".to_string(),
        ];
        assert_eq!(parse_color_mode(&args), ColorMode::Never);
    }

    #[test]
    fn test_parse_color_mode_auto_equals() {
        let args: Vec<String> = vec![
            "tswift-verify".to_string(),
            "--color=auto".to_string(),
            "file.json".to_string(),
        ];
        assert_eq!(parse_color_mode(&args), ColorMode::Auto);
    }

    #[test]
    fn test_parse_color_mode_unknown_value() {
        let args: Vec<String> = vec![
            "tswift-verify".to_string(),
            "--color=unknown".to_string(),
            "file.json".to_string(),
        ];
        assert_eq!(parse_color_mode(&args), ColorMode::Auto);
    }

    #[test]
    fn test_parse_color_mode_space_always() {
        let args: Vec<String> = vec![
            "tswift-verify".to_string(),
            "--color".to_string(),
            "always".to_string(),
            "file.json".to_string(),
        ];
        assert_eq!(parse_color_mode(&args), ColorMode::Always);
    }

    #[test]
    fn test_parse_color_mode_space_never() {
        let args: Vec<String> = vec![
            "tswift-verify".to_string(),
            "--color".to_string(),
            "never".to_string(),
            "file.json".to_string(),
        ];
        assert_eq!(parse_color_mode(&args), ColorMode::Never);
    }

    #[test]
    fn test_parse_color_mode_space_auto() {
        let args: Vec<String> = vec![
            "tswift-verify".to_string(),
            "--color".to_string(),
            "auto".to_string(),
            "file.json".to_string(),
        ];
        assert_eq!(parse_color_mode(&args), ColorMode::Auto);
    }

    #[test]
    fn test_parse_color_mode_flag_only() {
        // --color without value should default to Auto
        let args: Vec<String> = vec![
            "tswift-verify".to_string(),
            "--color".to_string(),
            "file.json".to_string(), // This is a file, not a color mode value
        ];
        // "file.json" doesn't match any color mode, so returns Auto
        assert_eq!(parse_color_mode(&args), ColorMode::Auto);
    }

    #[test]
    fn test_parse_color_mode_flag_at_end() {
        // --color at end with no value
        let args: Vec<String> = vec!["tswift-verify".to_string(), "--color".to_string()];
        assert_eq!(parse_color_mode(&args), ColorMode::Auto);
    }

    // ============================================================
    // Tests for parse_progress_mode
    // ============================================================

    #[test]
    fn test_parse_progress_mode_default() {
        let args: Vec<String> = vec!["tswift-verify".to_string(), "file.json".to_string()];
        assert_eq!(parse_progress_mode(&args), ProgressMode::Never);
    }

    #[test]
    fn test_parse_progress_mode_always_equals() {
        let args: Vec<String> = vec![
            "tswift-verify".to_string(),
            "--progress=always".to_string(),
            "file.json".to_string(),
        ];
        assert_eq!(parse_progress_mode(&args), ProgressMode::Always);
    }

    #[test]
    fn test_parse_progress_mode_never_equals() {
        let args: Vec<String> = vec![
            "tswift-verify".to_string(),
            "--progress=never".to_string(),
            "file.json".to_string(),
        ];
        assert_eq!(parse_progress_mode(&args), ProgressMode::Never);
    }

    #[test]
    fn test_parse_progress_mode_space_always() {
        let args: Vec<String> = vec![
            "tswift-verify".to_string(),
            "--progress".to_string(),
            "always".to_string(),
            "file.json".to_string(),
        ];
        assert_eq!(parse_progress_mode(&args), ProgressMode::Always);
    }

    #[test]
    fn test_parse_progress_mode_flag_only() {
        // --progress without a valid value should default to Auto
        let args: Vec<String> = vec![
            "tswift-verify".to_string(),
            "--progress".to_string(),
            "file.json".to_string(),
        ];
        assert_eq!(parse_progress_mode(&args), ProgressMode::Auto);
    }

    // ============================================================
    // Tests for parse_verbose_mode
    // ============================================================

    #[test]
    fn test_parse_verbose_mode_default() {
        let args: Vec<String> = vec!["tswift-verify".to_string(), "file.json".to_string()];
        assert_eq!(parse_verbose_mode(&args), VerboseMode::Off);
    }

    #[test]
    fn test_parse_verbose_mode_long_flag() {
        let args: Vec<String> = vec![
            "tswift-verify".to_string(),
            "--verbose".to_string(),
            "file.json".to_string(),
        ];
        assert_eq!(parse_verbose_mode(&args), VerboseMode::On);
    }

    #[test]
    fn test_parse_verbose_mode_short_flag() {
        let args: Vec<String> = vec![
            "tswift-verify".to_string(),
            "-v".to_string(),
            "file.json".to_string(),
        ];
        assert_eq!(parse_verbose_mode(&args), VerboseMode::On);
    }

    #[test]
    fn test_parse_verbose_mode_flag_position() {
        // Flag can be anywhere in args
        let args: Vec<String> = vec![
            "tswift-verify".to_string(),
            "file.json".to_string(),
            "--verbose".to_string(),
        ];
        assert_eq!(parse_verbose_mode(&args), VerboseMode::On);
    }

    // ============================================================
    // Tests for parse_json_progress_mode
    // ============================================================

    #[test]
    fn test_parse_json_progress_mode_default() {
        let args: Vec<String> = vec!["tswift-verify".to_string(), "file.json".to_string()];
        assert_eq!(parse_json_progress_mode(&args), JsonProgressMode::Off);
    }

    #[test]
    fn test_parse_json_progress_mode_on() {
        let args: Vec<String> = vec![
            "tswift-verify".to_string(),
            "--json-progress".to_string(),
            "file.json".to_string(),
        ];
        assert_eq!(parse_json_progress_mode(&args), JsonProgressMode::On);
    }

    // ============================================================
    // Tests for parse_cache_dir
    // ============================================================

    #[test]
    fn test_parse_cache_dir_default() {
        let args: Vec<String> = vec!["tswift-verify".to_string(), "file.json".to_string()];
        assert_eq!(parse_cache_dir(&args), None);
    }

    #[test]
    fn test_parse_cache_dir_equals() {
        let args: Vec<String> = vec![
            "tswift-verify".to_string(),
            "--cache-dir=/tmp/cache".to_string(),
            "file.json".to_string(),
        ];
        assert_eq!(parse_cache_dir(&args), Some("/tmp/cache".to_string()));
    }

    #[test]
    fn test_parse_cache_dir_space() {
        let args: Vec<String> = vec![
            "tswift-verify".to_string(),
            "--cache-dir".to_string(),
            "/tmp/cache".to_string(),
            "file.json".to_string(),
        ];
        assert_eq!(parse_cache_dir(&args), Some("/tmp/cache".to_string()));
    }

    #[test]
    fn test_parse_cache_dir_flag_at_end() {
        // --cache-dir at end with no value
        let args: Vec<String> = vec!["tswift-verify".to_string(), "--cache-dir".to_string()];
        assert_eq!(parse_cache_dir(&args), None);
    }

    // ============================================================
    // Tests for parse_emit_unknown_vcs_path
    // ============================================================

    #[test]
    fn test_parse_emit_unknown_vcs_path_default() {
        let args: Vec<String> = vec!["tswift-verify".to_string(), "file.json".to_string()];
        assert_eq!(parse_emit_unknown_vcs_path(&args), None);
    }

    #[test]
    fn test_parse_emit_unknown_vcs_path_equals() {
        let args: Vec<String> = vec![
            "tswift-verify".to_string(),
            "--emit-unknown-vcs=/tmp/unknown.json".to_string(),
            "file.json".to_string(),
        ];
        assert_eq!(
            parse_emit_unknown_vcs_path(&args),
            Some("/tmp/unknown.json".to_string())
        );
    }

    #[test]
    fn test_parse_emit_unknown_vcs_path_space() {
        let args: Vec<String> = vec![
            "tswift-verify".to_string(),
            "--emit-unknown-vcs".to_string(),
            "/tmp/unknown.json".to_string(),
            "file.json".to_string(),
        ];
        assert_eq!(
            parse_emit_unknown_vcs_path(&args),
            Some("/tmp/unknown.json".to_string())
        );
    }

    // ============================================================
    // Tests for parse_source_file
    // ============================================================

    #[test]
    fn test_parse_source_file_default() {
        let args: Vec<String> = vec!["tswift-verify".to_string(), "file.json".to_string()];
        assert_eq!(parse_source_file(&args), None);
    }

    #[test]
    fn test_parse_source_file_equals() {
        let args: Vec<String> = vec![
            "tswift-verify".to_string(),
            "--source-file=test.swift".to_string(),
            "file.json".to_string(),
        ];
        assert_eq!(parse_source_file(&args), Some("test.swift".to_string()));
    }

    #[test]
    fn test_parse_source_file_space() {
        let args: Vec<String> = vec![
            "tswift-verify".to_string(),
            "--source-file".to_string(),
            "test.swift".to_string(),
            "file.json".to_string(),
        ];
        assert_eq!(parse_source_file(&args), Some("test.swift".to_string()));
    }

    // ============================================================
    // Tests for parse_export_kani_dir
    // ============================================================

    #[test]
    fn test_parse_export_kani_dir_default() {
        let args: Vec<String> = vec!["tswift-verify".to_string(), "file.json".to_string()];
        assert_eq!(parse_export_kani_dir(&args), None);
    }

    #[test]
    fn test_parse_export_kani_dir_equals() {
        let args: Vec<String> = vec![
            "tswift-verify".to_string(),
            "--export-kani=/tmp/kani".to_string(),
            "file.json".to_string(),
        ];
        assert_eq!(parse_export_kani_dir(&args), Some("/tmp/kani".to_string()));
    }

    #[test]
    fn test_parse_export_kani_dir_space() {
        let args: Vec<String> = vec![
            "tswift-verify".to_string(),
            "--export-kani".to_string(),
            "/tmp/kani".to_string(),
            "file.json".to_string(),
        ];
        assert_eq!(parse_export_kani_dir(&args), Some("/tmp/kani".to_string()));
    }

    // ============================================================
    // Tests for parse_run_kani
    // ============================================================

    #[test]
    fn test_parse_run_kani_default() {
        let args: Vec<String> = vec!["tswift-verify".to_string(), "file.json".to_string()];
        assert!(!parse_run_kani(&args));
    }

    #[test]
    fn test_parse_run_kani_present() {
        let args: Vec<String> = vec![
            "tswift-verify".to_string(),
            "--run-kani".to_string(),
            "file.json".to_string(),
        ];
        assert!(parse_run_kani(&args));
    }

    // ============================================================
    // Tests for parse_kani_bitvector
    // ============================================================

    #[test]
    fn test_parse_kani_bitvector_default() {
        let args: Vec<String> = vec!["tswift-verify".to_string(), "file.json".to_string()];
        assert!(!parse_kani_bitvector(&args));
    }

    #[test]
    fn test_parse_kani_bitvector_present() {
        let args: Vec<String> = vec![
            "tswift-verify".to_string(),
            "--kani-bitvector".to_string(),
            "file.json".to_string(),
        ];
        assert!(parse_kani_bitvector(&args));
    }

    // ============================================================
    // Tests for format_source_location
    // ============================================================

    #[test]
    fn test_format_source_location_full() {
        let result = format_source_location("/path/to/file.swift", 42, 10);
        assert_eq!(result, "file.swift:42:10");
    }

    #[test]
    fn test_format_source_location_no_column() {
        let result = format_source_location("/path/to/file.swift", 42, 0);
        assert_eq!(result, "file.swift:42");
    }

    #[test]
    fn test_format_source_location_no_line() {
        let result = format_source_location("/path/to/file.swift", 0, 0);
        assert_eq!(result, "file.swift");
    }

    #[test]
    fn test_format_source_location_empty_file() {
        let result = format_source_location("", 42, 10);
        assert_eq!(result, "<unknown>:42:10");
    }

    #[test]
    fn test_format_source_location_all_empty() {
        let result = format_source_location("", 0, 0);
        assert_eq!(result, "");
    }

    #[test]
    fn test_format_source_location_just_filename() {
        let result = format_source_location("file.swift", 42, 10);
        assert_eq!(result, "file.swift:42:10");
    }

    // ============================================================
    // Tests for format_diagnostic_location
    // ============================================================

    #[test]
    fn test_format_diagnostic_location_full() {
        let result = format_diagnostic_location("/path/to/file.swift", 42, 10);
        assert_eq!(result, "/path/to/file.swift:42:10:");
    }

    #[test]
    fn test_format_diagnostic_location_zero_line() {
        // Zero line should become 1
        let result = format_diagnostic_location("/path/to/file.swift", 0, 10);
        assert_eq!(result, "/path/to/file.swift:1:10:");
    }

    #[test]
    fn test_format_diagnostic_location_zero_column() {
        // Zero column should become 1
        let result = format_diagnostic_location("/path/to/file.swift", 42, 0);
        assert_eq!(result, "/path/to/file.swift:42:1:");
    }

    #[test]
    fn test_format_diagnostic_location_all_zero() {
        let result = format_diagnostic_location("/path/to/file.swift", 0, 0);
        assert_eq!(result, "/path/to/file.swift:1:1:");
    }

    #[test]
    fn test_format_diagnostic_location_empty_file() {
        let result = format_diagnostic_location("", 42, 10);
        assert_eq!(result, "<unknown>:42:10:");
    }

    // ============================================================
    // Tests for accumulate_summary
    // ============================================================

    #[test]
    fn test_accumulate_summary_basic() {
        let mut summary = VerificationSummary::default();
        let response_summary = VerificationSummary {
            total_vcs: 5,
            verified: 3,
            failed: 1,
            unknown: 1,
            ..Default::default()
        };

        accumulate_summary(&mut summary, &response_summary);

        assert_eq!(summary.total_vcs, 5);
        assert_eq!(summary.verified, 3);
        assert_eq!(summary.failed, 1);
        assert_eq!(summary.unknown, 1);
    }

    #[test]
    fn test_accumulate_summary_multiple() {
        let mut summary = VerificationSummary::default();

        let response1 = VerificationSummary {
            total_vcs: 5,
            verified: 3,
            failed: 1,
            unknown: 1,
            ..Default::default()
        };
        let response2 = VerificationSummary {
            total_vcs: 10,
            verified: 8,
            failed: 2,
            unknown: 0,
            ..Default::default()
        };

        accumulate_summary(&mut summary, &response1);
        accumulate_summary(&mut summary, &response2);

        assert_eq!(summary.total_vcs, 15);
        assert_eq!(summary.verified, 11);
        assert_eq!(summary.failed, 3);
        assert_eq!(summary.unknown, 1);
    }

    #[test]
    fn test_accumulate_summary_trusted() {
        let mut summary = VerificationSummary::default();
        let response_summary = VerificationSummary {
            trusted: 2,
            ..Default::default()
        };

        accumulate_summary(&mut summary, &response_summary);

        assert_eq!(summary.trusted, 2);
    }

    #[test]
    fn test_accumulate_summary_time() {
        let mut summary = VerificationSummary::default();
        let response1 = VerificationSummary {
            total_time_seconds: 1.5,
            ..Default::default()
        };
        let response2 = VerificationSummary {
            total_time_seconds: 2.5,
            ..Default::default()
        };

        accumulate_summary(&mut summary, &response1);
        accumulate_summary(&mut summary, &response2);

        assert!((summary.total_time_seconds - 4.0).abs() < 0.001);
    }

    #[test]
    fn test_accumulate_summary_spec_and_auto() {
        let mut summary = VerificationSummary::default();
        let response_summary = VerificationSummary {
            spec_verified: 2,
            spec_failed: 1,
            spec_unknown: 0,
            auto_vc_verified: 5,
            auto_vc_failed: 2,
            auto_vc_unknown: 1,
            ..Default::default()
        };

        accumulate_summary(&mut summary, &response_summary);

        assert_eq!(summary.spec_verified, 2);
        assert_eq!(summary.spec_failed, 1);
        assert_eq!(summary.auto_vc_verified, 5);
        assert_eq!(summary.auto_vc_failed, 2);
        assert_eq!(summary.auto_vc_unknown, 1);
    }

    // ============================================================
    // Tests for sanitize_rust_module_name
    // ============================================================

    #[test]
    fn test_sanitize_rust_module_name_simple() {
        assert_eq!(sanitize_rust_module_name("hello"), "hello");
    }

    #[test]
    fn test_sanitize_rust_module_name_uppercase() {
        assert_eq!(sanitize_rust_module_name("HELLO"), "hello");
    }

    #[test]
    fn test_sanitize_rust_module_name_mixed_case() {
        assert_eq!(sanitize_rust_module_name("HelloWorld"), "helloworld");
    }

    #[test]
    fn test_sanitize_rust_module_name_with_numbers() {
        assert_eq!(sanitize_rust_module_name("test123"), "test123");
    }

    #[test]
    fn test_sanitize_rust_module_name_starts_with_number() {
        // Numbers at start should be replaced with underscore
        assert_eq!(sanitize_rust_module_name("123test"), "_23test");
    }

    #[test]
    fn test_sanitize_rust_module_name_with_special_chars() {
        assert_eq!(sanitize_rust_module_name("hello-world"), "hello_world");
        assert_eq!(sanitize_rust_module_name("hello.world"), "hello_world");
        assert_eq!(sanitize_rust_module_name("hello@world"), "hello_world");
    }

    #[test]
    fn test_sanitize_rust_module_name_with_underscores() {
        assert_eq!(sanitize_rust_module_name("hello_world"), "hello_world");
    }

    #[test]
    fn test_sanitize_rust_module_name_starts_with_underscore() {
        assert_eq!(sanitize_rust_module_name("_private"), "_private");
    }

    #[test]
    fn test_sanitize_rust_module_name_empty() {
        assert_eq!(sanitize_rust_module_name(""), "harness");
    }

    #[test]
    fn test_sanitize_rust_module_name_all_special() {
        // All special chars -> all underscores -> but first char must be valid
        assert_eq!(sanitize_rust_module_name("@#$"), "___");
    }

    #[test]
    fn test_sanitize_rust_module_name_unicode() {
        // Non-ASCII should be replaced with underscores
        assert_eq!(sanitize_rust_module_name("日本語"), "___");
    }

    #[test]
    fn test_sanitize_rust_module_name_spaces() {
        assert_eq!(sanitize_rust_module_name("hello world"), "hello_world");
    }

    // ============================================================
    // Tests for paths_match
    // ============================================================

    #[test]
    fn test_paths_match_exact() {
        assert!(paths_match("/path/to/file.swift", "/path/to/file.swift"));
    }

    #[test]
    fn test_paths_match_empty_source() {
        assert!(!paths_match("", "/path/to/file.swift"));
    }

    #[test]
    fn test_paths_match_empty_filter() {
        assert!(paths_match("/path/to/file.swift", ""));
    }

    #[test]
    fn test_paths_match_suffix_match() {
        assert!(paths_match("/full/path/to/file.swift", "file.swift"));
        assert!(paths_match("/full/path/to/file.swift", "to/file.swift"));
    }

    #[test]
    fn test_paths_match_source_is_suffix() {
        assert!(paths_match("file.swift", "/full/path/to/file.swift"));
    }

    #[test]
    fn test_paths_match_no_match() {
        assert!(!paths_match("/path/to/file.swift", "/other/file.swift"));
        assert!(!paths_match("a.swift", "b.swift"));
    }

    #[test]
    fn test_paths_match_partial_filename() {
        // "file" is not a suffix of "file.swift"
        assert!(!paths_match("/path/to/file.swift", "file"));
    }

    // ============================================================
    // Tests for format_source_snippet
    // ============================================================

    #[test]
    fn test_format_source_snippet_basic() {
        let input = "line 1\nline 2\nline 3";
        let result = format_source_snippet(input, 2, 3);
        assert!(result.is_some());
        let (line_text, caret) = result.unwrap();
        assert_eq!(line_text, "line 2");
        assert_eq!(caret, "  ^"); // 2 spaces then caret (0-indexed col 2)
    }

    #[test]
    fn test_format_source_snippet_first_line() {
        let input = "first line\nsecond line";
        let result = format_source_snippet(input, 1, 1);
        assert!(result.is_some());
        let (line_text, caret) = result.unwrap();
        assert_eq!(line_text, "first line");
        assert_eq!(caret, "^"); // Column 1 -> 0 spaces
    }

    #[test]
    fn test_format_source_snippet_zero_line() {
        let input = "line 1\nline 2";
        let result = format_source_snippet(input, 0, 5);
        assert!(result.is_none());
    }

    #[test]
    fn test_format_source_snippet_zero_column() {
        let input = "line 1\nline 2";
        let result = format_source_snippet(input, 1, 0);
        assert!(result.is_none());
    }

    #[test]
    fn test_format_source_snippet_out_of_bounds_line() {
        let input = "line 1\nline 2";
        let result = format_source_snippet(input, 10, 1);
        assert!(result.is_none());
    }

    #[test]
    fn test_format_source_snippet_column_past_end() {
        let input = "short";
        let result = format_source_snippet(input, 1, 100);
        assert!(result.is_some());
        let (line_text, caret) = result.unwrap();
        assert_eq!(line_text, "short");
        // Column is clamped to line length
        assert_eq!(caret, "     ^"); // 5 spaces (length of "short")
    }

    #[test]
    fn test_format_source_snippet_empty_line() {
        let input = "line1\n\nline3";
        let result = format_source_snippet(input, 2, 1);
        assert!(result.is_some());
        let (line_text, caret) = result.unwrap();
        assert_eq!(line_text, "");
        assert_eq!(caret, "^"); // Column 1 -> 0 spaces, clamped to 0
    }

    #[test]
    fn test_format_source_snippet_single_line() {
        let input = "only one line";
        let result = format_source_snippet(input, 1, 6);
        assert!(result.is_some());
        let (line_text, caret) = result.unwrap();
        assert_eq!(line_text, "only one line");
        assert_eq!(caret, "     ^"); // 5 spaces for col 6 (0-indexed 5)
    }

    // ============================================================
    // Tests for VerboseSummary
    // ============================================================

    #[test]
    fn test_verbose_summary_default() {
        let summary = VerboseSummary::default();
        assert_eq!(summary.ok, 0);
        assert_eq!(summary.fail, 0);
        assert_eq!(summary.warn, 0);
        assert_eq!(summary.err, 0);
        assert_eq!(summary.total(), 0);
    }

    #[test]
    fn test_verbose_summary_total() {
        let summary = VerboseSummary {
            ok: 5,
            fail: 2,
            warn: 1,
            err: 1,
            total_time_seconds: 0.0,
        };
        assert_eq!(summary.total(), 9);
    }

    // ============================================================
    // Tests for convert_kani_harness_result
    // ============================================================

    #[test]
    fn test_convert_kani_harness_result_success() {
        let kani_result = kani_runner::KaniHarnessResult::Success {
            harness_name: "test_harness".to_string(),
            time_seconds: 1.5,
        };
        let result = convert_kani_harness_result(&kani_result);
        match result {
            KaniVcResult::Verified {
                harness_name,
                time_seconds,
            } => {
                assert_eq!(harness_name, "test_harness");
                assert!((time_seconds - 1.5).abs() < 0.001);
            }
            _ => panic!("Expected Verified result"),
        }
    }

    #[test]
    fn test_convert_kani_harness_result_failure() {
        let kani_result = kani_runner::KaniHarnessResult::Failure {
            harness_name: "test_harness".to_string(),
            description: "assertion failed".to_string(),
            location: None,
            counterexample: Vec::new(),
            time_seconds: 2.0,
        };
        let result = convert_kani_harness_result(&kani_result);
        match result {
            KaniVcResult::Failed {
                harness_name,
                description,
                time_seconds,
            } => {
                assert_eq!(harness_name, "test_harness");
                assert_eq!(description, "assertion failed");
                assert!((time_seconds - 2.0).abs() < 0.001);
            }
            _ => panic!("Expected Failed result"),
        }
    }

    #[test]
    fn test_convert_kani_harness_result_error() {
        let kani_result = kani_runner::KaniHarnessResult::Error {
            harness_name: "test_harness".to_string(),
            message: "compilation error".to_string(),
        };
        let result = convert_kani_harness_result(&kani_result);
        match result {
            KaniVcResult::Error {
                harness_name,
                message,
            } => {
                assert_eq!(harness_name, "test_harness");
                assert_eq!(message, "compilation error");
            }
            _ => panic!("Expected Error result"),
        }
    }

    // =========================================================================
    // Tests for filter_bundles_by_source
    // =========================================================================

    fn make_test_bundle(function_name: &str, source_file: &str) -> vc_ir_swift::SwiftVcBundle {
        vc_ir_swift::SwiftVcBundle {
            function_name: function_name.to_string(),
            source_file: source_file.to_string(),
            source_line: 0,
            source_column: 0,
            parameters: vec![],
            return_type: None,
            requires: vec![],
            ensures: vec![],
            invariants: vec![],
            requires_str: vec![],
            ensures_str: vec![],
            invariants_str: vec![],
            auto_vcs: vec![],
            is_trusted: false,
            body_constraints: vec![],
            spec_warnings: vec![],
        }
    }

    #[test]
    fn test_filter_bundles_by_source_no_filter() {
        let bundles = vec![
            make_test_bundle("foo", "/path/to/foo.swift"),
            make_test_bundle("bar", "/path/to/bar.swift"),
        ];
        let filtered = filter_bundles_by_source(bundles, None);
        assert_eq!(filtered.len(), 2);
    }

    #[test]
    fn test_filter_bundles_by_source_exact_match() {
        let bundles = vec![
            make_test_bundle("foo", "/path/to/foo.swift"),
            make_test_bundle("bar", "/path/to/bar.swift"),
        ];
        let filtered = filter_bundles_by_source(bundles, Some("/path/to/foo.swift"));
        assert_eq!(filtered.len(), 1);
        assert_eq!(filtered[0].function_name, "foo");
    }

    #[test]
    fn test_filter_bundles_by_source_suffix_match() {
        let bundles = vec![
            make_test_bundle("foo", "/path/to/foo.swift"),
            make_test_bundle("bar", "/path/to/bar.swift"),
        ];
        let filtered = filter_bundles_by_source(bundles, Some("foo.swift"));
        assert_eq!(filtered.len(), 1);
        assert_eq!(filtered[0].function_name, "foo");
    }

    #[test]
    fn test_filter_bundles_by_source_no_match() {
        let bundles = vec![
            make_test_bundle("foo", "/path/to/foo.swift"),
            make_test_bundle("bar", "/path/to/bar.swift"),
        ];
        let filtered = filter_bundles_by_source(bundles, Some("baz.swift"));
        assert_eq!(filtered.len(), 0);
    }

    #[test]
    fn test_filter_bundles_by_source_empty_source_file() {
        let bundles = vec![
            make_test_bundle("foo", ""),
            make_test_bundle("bar", "/path/to/bar.swift"),
        ];
        let filtered = filter_bundles_by_source(bundles, Some("bar.swift"));
        assert_eq!(filtered.len(), 1);
        assert_eq!(filtered[0].function_name, "bar");
    }

    #[test]
    fn test_filter_bundles_by_source_all_match() {
        let bundles = vec![
            make_test_bundle("foo", "/path/to/app.swift"),
            make_test_bundle("bar", "/path/to/app.swift"),
        ];
        let filtered = filter_bundles_by_source(bundles, Some("app.swift"));
        assert_eq!(filtered.len(), 2);
    }

    // =========================================================================
    // Tests for filter_responses_by_source
    // =========================================================================

    fn make_test_response(function_name: &str, source_file: &str) -> SwiftVerifyResponse {
        SwiftVerifyResponse {
            function_name: function_name.to_string(),
            source_file: source_file.to_string(),
            source_line: 0,
            is_trusted: false,
            spec_result: None,
            auto_vc_results: vec![],
            summary: VerificationSummary::default(),
            spec_warnings: vec![],
        }
    }

    #[test]
    fn test_filter_responses_by_source_no_filter() {
        let responses = vec![
            make_test_response("foo", "/path/to/foo.swift"),
            make_test_response("bar", "/path/to/bar.swift"),
        ];
        let filtered = filter_responses_by_source(responses, None);
        assert_eq!(filtered.len(), 2);
    }

    #[test]
    fn test_filter_responses_by_source_exact_match() {
        let responses = vec![
            make_test_response("foo", "/path/to/foo.swift"),
            make_test_response("bar", "/path/to/bar.swift"),
        ];
        let filtered = filter_responses_by_source(responses, Some("/path/to/foo.swift"));
        assert_eq!(filtered.len(), 1);
        assert_eq!(filtered[0].function_name, "foo");
    }

    #[test]
    fn test_filter_responses_by_source_suffix_match() {
        let responses = vec![
            make_test_response("foo", "/path/to/foo.swift"),
            make_test_response("bar", "/path/to/bar.swift"),
        ];
        let filtered = filter_responses_by_source(responses, Some("foo.swift"));
        assert_eq!(filtered.len(), 1);
        assert_eq!(filtered[0].function_name, "foo");
    }

    #[test]
    fn test_filter_responses_by_source_no_match() {
        let responses = vec![
            make_test_response("foo", "/path/to/foo.swift"),
            make_test_response("bar", "/path/to/bar.swift"),
        ];
        let filtered = filter_responses_by_source(responses, Some("baz.swift"));
        assert_eq!(filtered.len(), 0);
    }

    #[test]
    fn test_filter_responses_by_source_empty_source_file() {
        let responses = vec![
            make_test_response("foo", ""),
            make_test_response("bar", "/path/to/bar.swift"),
        ];
        let filtered = filter_responses_by_source(responses, Some("bar.swift"));
        assert_eq!(filtered.len(), 1);
        assert_eq!(filtered[0].function_name, "bar");
    }

    // =========================================================================
    // Tests for merge_kani_results_into_responses
    // =========================================================================

    fn make_response_with_auto_vc(
        function_name: &str,
        vc_description: &str,
    ) -> SwiftVerifyResponse {
        SwiftVerifyResponse {
            function_name: function_name.to_string(),
            source_file: String::new(),
            source_line: 0,
            is_trusted: false,
            spec_result: None,
            auto_vc_results: vec![SwiftAutoVcResult {
                description: vc_description.to_string(),
                source_file: String::new(),
                source_line: 0,
                source_column: 0,
                result: SwiftVerifyResult::Unknown {
                    reason: "pending".to_string(),
                    time_seconds: 0.0,
                },
                suggestion: String::new(),
                kani_result: None,
                call_chain: vec![],
            }],
            summary: VerificationSummary::default(),
            spec_warnings: vec![],
        }
    }

    fn make_kani_run_result(
        results: Vec<kani_runner::KaniHarnessResult>,
    ) -> kani_runner::KaniRunResult {
        let total_harnesses = results.len();
        let successful = results
            .iter()
            .filter(|r| matches!(r, kani_runner::KaniHarnessResult::Success { .. }))
            .count();
        let failed = results
            .iter()
            .filter(|r| matches!(r, kani_runner::KaniHarnessResult::Failure { .. }))
            .count();
        let errors = results
            .iter()
            .filter(|r| matches!(r, kani_runner::KaniHarnessResult::Error { .. }))
            .count();
        kani_runner::KaniRunResult {
            results,
            total_harnesses,
            successful,
            failed,
            errors,
            total_time_seconds: 0.0,
        }
    }

    #[test]
    fn test_merge_kani_results_empty() {
        let mut responses = vec![make_response_with_auto_vc("foo", "overflow")];
        let kani_result = make_kani_run_result(vec![]);
        let mapping = VcHarnessMapping::new();
        merge_kani_results_into_responses(&mut responses, &kani_result, &mapping);
        // No Kani results to merge, so kani_result should remain None
        assert!(responses[0].auto_vc_results[0].kani_result.is_none());
    }

    #[test]
    fn test_merge_kani_results_no_mapping() {
        let mut responses = vec![make_response_with_auto_vc("foo", "overflow")];
        let kani_result = make_kani_run_result(vec![kani_runner::KaniHarnessResult::Success {
            harness_name: "kani_harnesses::mod_test::proof_overflow".to_string(),
            time_seconds: 1.0,
        }]);
        let mapping = VcHarnessMapping::new(); // Empty mapping
        merge_kani_results_into_responses(&mut responses, &kani_result, &mapping);
        // No mapping entry, so kani_result should remain None
        assert!(responses[0].auto_vc_results[0].kani_result.is_none());
    }

    #[test]
    fn test_merge_kani_results_with_mapping() {
        let mut responses = vec![make_response_with_auto_vc("foo", "overflow")];
        let kani_result = make_kani_run_result(vec![kani_runner::KaniHarnessResult::Success {
            harness_name: "kani_harnesses::mod_foo_overflow::proof_overflow".to_string(),
            time_seconds: 1.5,
        }]);
        let mut mapping = VcHarnessMapping::new();
        mapping.insert("foo", "overflow", "mod_foo_overflow");
        merge_kani_results_into_responses(&mut responses, &kani_result, &mapping);
        // Mapping exists, Kani result should be merged
        let kani_result = responses[0].auto_vc_results[0].kani_result.as_ref();
        assert!(kani_result.is_some());
        match kani_result.unwrap() {
            KaniVcResult::Verified { time_seconds, .. } => {
                assert!((time_seconds - 1.5).abs() < 0.001);
            }
            _ => panic!("Expected Verified result"),
        }
    }

    #[test]
    fn test_merge_kani_results_failure() {
        let mut responses = vec![make_response_with_auto_vc("bar", "bounds_check")];
        let kani_result = make_kani_run_result(vec![kani_runner::KaniHarnessResult::Failure {
            harness_name: "kani_harnesses::mod_bar_bounds::proof_bounds_check".to_string(),
            description: "array index out of bounds".to_string(),
            location: None,
            counterexample: vec![],
            time_seconds: 2.5,
        }]);
        let mut mapping = VcHarnessMapping::new();
        mapping.insert("bar", "bounds_check", "mod_bar_bounds");
        merge_kani_results_into_responses(&mut responses, &kani_result, &mapping);
        let kani_result = responses[0].auto_vc_results[0].kani_result.as_ref();
        assert!(kani_result.is_some());
        match kani_result.unwrap() {
            KaniVcResult::Failed { description, .. } => {
                assert_eq!(description, "array index out of bounds");
            }
            _ => panic!("Expected Failed result"),
        }
    }

    #[test]
    fn test_merge_kani_results_multiple_responses() {
        let mut responses = vec![
            make_response_with_auto_vc("foo", "overflow"),
            make_response_with_auto_vc("bar", "bounds"),
        ];
        let kani_result = make_kani_run_result(vec![
            kani_runner::KaniHarnessResult::Success {
                harness_name: "kani_harnesses::mod_foo::proof_overflow".to_string(),
                time_seconds: 1.0,
            },
            kani_runner::KaniHarnessResult::Failure {
                harness_name: "kani_harnesses::mod_bar::proof_bounds".to_string(),
                description: "assertion failed".to_string(),
                location: None,
                counterexample: vec![],
                time_seconds: 2.0,
            },
        ]);
        let mut mapping = VcHarnessMapping::new();
        mapping.insert("foo", "overflow", "mod_foo");
        mapping.insert("bar", "bounds", "mod_bar");
        merge_kani_results_into_responses(&mut responses, &kani_result, &mapping);

        // First response should have Verified
        match responses[0].auto_vc_results[0].kani_result.as_ref() {
            Some(KaniVcResult::Verified { .. }) => {}
            _ => panic!("Expected Verified for foo"),
        }

        // Second response should have Failed
        match responses[1].auto_vc_results[0].kani_result.as_ref() {
            Some(KaniVcResult::Failed { .. }) => {}
            _ => panic!("Expected Failed for bar"),
        }
    }

    // =========================================================================
    // Tests for VcHarnessMapping
    // =========================================================================

    #[test]
    fn test_vc_harness_mapping_new() {
        let mapping = VcHarnessMapping::new();
        assert!(mapping.get("foo", "bar").is_none());
    }

    #[test]
    fn test_vc_harness_mapping_insert_and_get() {
        let mut mapping = VcHarnessMapping::new();
        mapping.insert("function_a", "vc_1", "module_a_1");
        assert_eq!(
            mapping.get("function_a", "vc_1"),
            Some(&"module_a_1".to_string())
        );
    }

    #[test]
    fn test_vc_harness_mapping_multiple_entries() {
        let mut mapping = VcHarnessMapping::new();
        mapping.insert("func_a", "vc_1", "mod_a_1");
        mapping.insert("func_a", "vc_2", "mod_a_2");
        mapping.insert("func_b", "vc_1", "mod_b_1");

        assert_eq!(mapping.get("func_a", "vc_1"), Some(&"mod_a_1".to_string()));
        assert_eq!(mapping.get("func_a", "vc_2"), Some(&"mod_a_2".to_string()));
        assert_eq!(mapping.get("func_b", "vc_1"), Some(&"mod_b_1".to_string()));
        assert!(mapping.get("func_b", "vc_2").is_none());
    }

    #[test]
    fn test_vc_harness_mapping_overwrite() {
        let mut mapping = VcHarnessMapping::new();
        mapping.insert("func", "vc", "old_module");
        mapping.insert("func", "vc", "new_module");
        assert_eq!(mapping.get("func", "vc"), Some(&"new_module".to_string()));
    }

    // =========================================================================
    // Tests for VerboseSummary add_time (additional coverage)
    // =========================================================================

    #[test]
    fn test_verbose_summary_add_time() {
        let mut summary = VerboseSummary::default();
        summary.add_time(1.5);
        summary.add_time(2.5);
        assert!((summary.total_time_seconds - 4.0).abs() < 0.001);
    }

    #[test]
    fn test_verbose_summary_add_time_zero() {
        let mut summary = VerboseSummary::default();
        summary.add_time(0.0);
        assert!((summary.total_time_seconds - 0.0).abs() < 0.001);
    }

    #[test]
    fn test_verbose_summary_add_time_multiple() {
        let mut summary = VerboseSummary::default();
        summary.add_time(0.1);
        summary.add_time(0.2);
        summary.add_time(0.3);
        assert!((summary.total_time_seconds - 0.6).abs() < 0.001);
    }

    // =========================================================================
    // Additional format_source_location edge case tests
    // =========================================================================

    #[test]
    fn test_format_source_location_empty_file_nonzero_line_zero_col() {
        // Empty file but line > 0 and col=0 uses <unknown>
        assert_eq!(format_source_location("", 42, 0), "<unknown>:42");
    }

    #[test]
    fn test_format_source_location_relative_nested_path() {
        // Relative path should extract just filename
        assert_eq!(
            format_source_location("src/lib/utils.swift", 100, 1),
            "utils.swift:100:1"
        );
    }

    #[test]
    fn test_format_source_location_windows_style_path_on_unix() {
        // On Unix, backslashes are literal characters in filenames, not separators
        // So the entire string is treated as the "filename"
        assert_eq!(
            format_source_location("C:\\Users\\test\\file.swift", 1, 1),
            "C:\\Users\\test\\file.swift:1:1"
        );
    }

    #[test]
    fn test_format_source_location_path_with_embedded_spaces() {
        // Path with spaces in directory and filename
        assert_eq!(
            format_source_location("/path/with spaces/file name.swift", 5, 3),
            "file name.swift:5:3"
        );
    }

    #[test]
    fn test_format_source_location_minimum_line_col() {
        // Line 1 col 1 - minimum valid values
        assert_eq!(format_source_location("x.swift", 1, 1), "x.swift:1:1");
    }

    #[test]
    fn test_format_source_location_large_line_and_col() {
        // Large line and column numbers
        assert_eq!(
            format_source_location("big.swift", 99999, 9999),
            "big.swift:99999:9999"
        );
    }

    #[test]
    fn test_format_source_location_hidden_file() {
        // Filename with leading dot (hidden file)
        assert_eq!(
            format_source_location(".hidden.swift", 10, 5),
            ".hidden.swift:10:5"
        );
    }

    #[test]
    fn test_format_source_location_no_extension_file() {
        // Filename with no extension
        assert_eq!(
            format_source_location("/path/Makefile", 42, 1),
            "Makefile:42:1"
        );
    }

    #[test]
    fn test_format_source_location_deep_nested_unix_path() {
        // Deep nested path should extract just filename
        assert_eq!(
            format_source_location("/a/b/c/d/e/f/g/deep.swift", 42, 10),
            "deep.swift:42:10"
        );
    }

    // =========================================================================
    // Tests for emit_verbose_vc_line (side effects on VerboseSummary)
    // =========================================================================

    #[test]
    fn test_emit_verbose_vc_line_verified_increments_ok() {
        let info = VcProgressInfo {
            total_vcs: 5,
            completed_vcs: 1,
            vc_name: "bounds_check".to_string(),
            is_spec: false,
            result: SwiftVerifyResult::Verified { time_seconds: 0.5 },
        };
        let mut summary = VerboseSummary::default();
        emit_verbose_vc_line(&info, "test_func", false, &mut summary);
        assert_eq!(summary.ok, 1);
        assert_eq!(summary.fail, 0);
        assert_eq!(summary.warn, 0);
        assert_eq!(summary.err, 0);
        assert!((summary.total_time_seconds - 0.5).abs() < 0.001);
    }

    #[test]
    fn test_emit_verbose_vc_line_failed_increments_fail() {
        let info = VcProgressInfo {
            total_vcs: 5,
            completed_vcs: 2,
            vc_name: "overflow_check".to_string(),
            is_spec: true,
            result: SwiftVerifyResult::Failed {
                counterexample: vec![("x".to_string(), "256".to_string())],
                time_seconds: 1.2,
            },
        };
        let mut summary = VerboseSummary::default();
        emit_verbose_vc_line(&info, "compute", false, &mut summary);
        assert_eq!(summary.ok, 0);
        assert_eq!(summary.fail, 1);
        assert_eq!(summary.warn, 0);
        assert_eq!(summary.err, 0);
        assert!((summary.total_time_seconds - 1.2).abs() < 0.001);
    }

    #[test]
    fn test_emit_verbose_vc_line_unknown_increments_warn() {
        let info = VcProgressInfo {
            total_vcs: 3,
            completed_vcs: 3,
            vc_name: "complex_check".to_string(),
            is_spec: false,
            result: SwiftVerifyResult::Unknown {
                reason: "solver limit".to_string(),
                time_seconds: 5.0,
            },
        };
        let mut summary = VerboseSummary::default();
        emit_verbose_vc_line(&info, "analyze", true, &mut summary);
        assert_eq!(summary.ok, 0);
        assert_eq!(summary.fail, 0);
        assert_eq!(summary.warn, 1);
        assert_eq!(summary.err, 0);
        assert!((summary.total_time_seconds - 5.0).abs() < 0.001);
    }

    #[test]
    fn test_emit_verbose_vc_line_timeout_increments_warn() {
        let info = VcProgressInfo {
            total_vcs: 2,
            completed_vcs: 1,
            vc_name: "long_check".to_string(),
            is_spec: true,
            result: SwiftVerifyResult::Timeout {
                timeout_seconds: 30.0,
            },
        };
        let mut summary = VerboseSummary::default();
        emit_verbose_vc_line(&info, "slow_func", false, &mut summary);
        assert_eq!(summary.ok, 0);
        assert_eq!(summary.fail, 0);
        assert_eq!(summary.warn, 1);
        assert_eq!(summary.err, 0);
        // Timeout result has timeout_seconds which is used as time
        assert!((summary.total_time_seconds - 30.0).abs() < 0.001);
    }

    #[test]
    fn test_emit_verbose_vc_line_error_increments_err() {
        let info = VcProgressInfo {
            total_vcs: 4,
            completed_vcs: 2,
            vc_name: "broken_check".to_string(),
            is_spec: false,
            result: SwiftVerifyResult::Error {
                message: "internal error".to_string(),
            },
        };
        let mut summary = VerboseSummary::default();
        emit_verbose_vc_line(&info, "bad_func", false, &mut summary);
        assert_eq!(summary.ok, 0);
        assert_eq!(summary.fail, 0);
        assert_eq!(summary.warn, 0);
        assert_eq!(summary.err, 1);
        // Error has no time_seconds, returns 0.0
        assert!((summary.total_time_seconds - 0.0).abs() < 0.001);
    }

    #[test]
    fn test_emit_verbose_vc_line_multiple_results() {
        let mut summary = VerboseSummary::default();

        // Add a verified result
        let info1 = VcProgressInfo {
            total_vcs: 4,
            completed_vcs: 1,
            vc_name: "check1".to_string(),
            is_spec: false,
            result: SwiftVerifyResult::Verified { time_seconds: 0.1 },
        };
        emit_verbose_vc_line(&info1, "func", false, &mut summary);

        // Add a failed result
        let info2 = VcProgressInfo {
            total_vcs: 4,
            completed_vcs: 2,
            vc_name: "check2".to_string(),
            is_spec: true,
            result: SwiftVerifyResult::Failed {
                counterexample: vec![],
                time_seconds: 0.2,
            },
        };
        emit_verbose_vc_line(&info2, "func", false, &mut summary);

        // Add an unknown result
        let info3 = VcProgressInfo {
            total_vcs: 4,
            completed_vcs: 3,
            vc_name: "check3".to_string(),
            is_spec: false,
            result: SwiftVerifyResult::Unknown {
                reason: "limit".to_string(),
                time_seconds: 0.3,
            },
        };
        emit_verbose_vc_line(&info3, "func", false, &mut summary);

        // Add an error result
        let info4 = VcProgressInfo {
            total_vcs: 4,
            completed_vcs: 4,
            vc_name: "check4".to_string(),
            is_spec: false,
            result: SwiftVerifyResult::Error {
                message: "oops".to_string(),
            },
        };
        emit_verbose_vc_line(&info4, "func", false, &mut summary);

        assert_eq!(summary.ok, 1);
        assert_eq!(summary.fail, 1);
        assert_eq!(summary.warn, 1);
        assert_eq!(summary.err, 1);
        assert_eq!(summary.total(), 4);
        assert!((summary.total_time_seconds - 0.6).abs() < 0.001);
    }

    #[test]
    fn test_emit_verbose_vc_line_with_color_flag() {
        // The color flag doesn't affect summary counts, just output format
        let info = VcProgressInfo {
            total_vcs: 1,
            completed_vcs: 1,
            vc_name: "test".to_string(),
            is_spec: true,
            result: SwiftVerifyResult::Verified { time_seconds: 0.05 },
        };

        let mut summary_no_color = VerboseSummary::default();
        emit_verbose_vc_line(&info, "func", false, &mut summary_no_color);

        let mut summary_with_color = VerboseSummary::default();
        emit_verbose_vc_line(&info, "func", true, &mut summary_with_color);

        // Both should have same summary values
        assert_eq!(summary_no_color.ok, summary_with_color.ok);
        assert_eq!(summary_no_color.fail, summary_with_color.fail);
        assert_eq!(summary_no_color.warn, summary_with_color.warn);
        assert_eq!(summary_no_color.err, summary_with_color.err);
    }

    #[test]
    fn test_emit_verbose_vc_line_spec_vs_auto_vc() {
        // is_spec flag doesn't affect summary counts, just output format
        let info_spec = VcProgressInfo {
            total_vcs: 2,
            completed_vcs: 1,
            vc_name: "test".to_string(),
            is_spec: true,
            result: SwiftVerifyResult::Verified { time_seconds: 0.1 },
        };
        let info_auto = VcProgressInfo {
            total_vcs: 2,
            completed_vcs: 2,
            vc_name: "test".to_string(),
            is_spec: false,
            result: SwiftVerifyResult::Verified { time_seconds: 0.1 },
        };

        let mut summary = VerboseSummary::default();
        emit_verbose_vc_line(&info_spec, "func", false, &mut summary);
        emit_verbose_vc_line(&info_auto, "func", false, &mut summary);

        assert_eq!(summary.ok, 2);
        assert!((summary.total_time_seconds - 0.2).abs() < 0.001);
    }

    // =========================================================================
    // render_progress_bar tests
    // =========================================================================

    #[test]
    fn test_render_progress_bar_zero_total() {
        let result = progress::render_progress_bar(0, 0, 10);
        assert_eq!(result, "[          ]   0%");
    }

    #[test]
    fn test_render_progress_bar_zero_completed() {
        let result = progress::render_progress_bar(0, 10, 10);
        assert_eq!(result, "[          ]   0%");
    }

    #[test]
    fn test_render_progress_bar_half_complete() {
        let result = progress::render_progress_bar(5, 10, 10);
        assert_eq!(result, "[====>     ]  50%");
    }

    #[test]
    fn test_render_progress_bar_fully_complete() {
        let result = progress::render_progress_bar(10, 10, 10);
        assert_eq!(result, "[==========] 100%");
    }

    #[test]
    fn test_render_progress_bar_one_of_ten() {
        let result = progress::render_progress_bar(1, 10, 10);
        // 1/10 = 10%, filled = 1
        assert_eq!(result, "[>         ]  10%");
    }

    #[test]
    fn test_render_progress_bar_nine_of_ten() {
        let result = progress::render_progress_bar(9, 10, 10);
        // 9/10 = 90%, filled = 9
        assert_eq!(result, "[========> ]  90%");
    }

    #[test]
    fn test_render_progress_bar_narrow_width() {
        let result = progress::render_progress_bar(5, 10, 5);
        // 50% complete, width 5, filled = 2
        assert_eq!(result, "[=>   ]  50%");
    }

    #[test]
    fn test_render_progress_bar_wide_width() {
        let result = progress::render_progress_bar(5, 10, 20);
        // 50% complete, width 20, filled = 10
        assert_eq!(result, "[=========>          ]  50%");
    }

    #[test]
    fn test_render_progress_bar_single_item() {
        let result = progress::render_progress_bar(1, 1, 10);
        assert_eq!(result, "[==========] 100%");
    }

    #[test]
    fn test_render_progress_bar_zero_width() {
        let result = progress::render_progress_bar(5, 10, 0);
        // Width 0 means no bar characters
        assert_eq!(result, "[]  50%");
    }

    #[test]
    fn test_render_progress_bar_almost_complete() {
        let result = progress::render_progress_bar(99, 100, 10);
        // 99% complete, filled = 9
        assert_eq!(result, "[========> ]  99%");
    }

    #[test]
    fn test_render_progress_bar_small_progress_large_total() {
        let result = progress::render_progress_bar(1, 1000, 10);
        // 0.1% rounds to 0%, filled = 0
        assert_eq!(result, "[          ]   0%");
    }

    // =========================================================================
    // VcProgressState tests
    // =========================================================================

    #[test]
    fn test_vc_progress_state_new() {
        let state = progress::VcProgressState::new();
        let (completed, total) = state.get();
        assert_eq!(completed, 0);
        assert_eq!(total, 0);
    }

    #[test]
    fn test_vc_progress_state_reset() {
        let state = progress::VcProgressState::new();
        state.reset(42);
        let (completed, total) = state.get();
        assert_eq!(completed, 0);
        assert_eq!(total, 42);
    }

    #[test]
    fn test_vc_progress_state_set_completed() {
        let state = progress::VcProgressState::new();
        state.reset(10);
        state.set_completed(5);
        let (completed, total) = state.get();
        assert_eq!(completed, 5);
        assert_eq!(total, 10);
    }

    #[test]
    fn test_vc_progress_state_multiple_updates() {
        let state = progress::VcProgressState::new();
        state.reset(20);

        state.set_completed(5);
        let (c1, t1) = state.get();
        assert_eq!(c1, 5);
        assert_eq!(t1, 20);

        state.set_completed(10);
        let (c2, t2) = state.get();
        assert_eq!(c2, 10);
        assert_eq!(t2, 20);

        state.set_completed(20);
        let (c3, t3) = state.get();
        assert_eq!(c3, 20);
        assert_eq!(t3, 20);
    }

    #[test]
    fn test_vc_progress_state_reset_clears_completed() {
        let state = progress::VcProgressState::new();
        state.reset(10);
        state.set_completed(5);

        // Reset should clear completed back to 0
        state.reset(30);
        let (completed, total) = state.get();
        assert_eq!(completed, 0);
        assert_eq!(total, 30);
    }

    #[test]
    fn test_vc_progress_state_zero_total() {
        let state = progress::VcProgressState::new();
        state.reset(0);
        let (completed, total) = state.get();
        assert_eq!(completed, 0);
        assert_eq!(total, 0);
    }
}
