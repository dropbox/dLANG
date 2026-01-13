//! trust-upstream: tRust upstream Rust tracking and sync tool
//!
//! Automatically tracks Rust releases, analyzes impact on tRust, and
//! manages the sync process to keep tRust current with upstream rustc.

use anyhow::Result;
use clap::{Parser, Subcommand};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

mod analyzer;
mod db;
mod monitor;
mod sync;

pub use analyzer::ImpactAnalyzer;
pub use db::SyncDatabase;
pub use monitor::ReleaseMonitor;
pub use sync::SyncPipeline;

#[derive(Parser)]
#[command(name = "trust-upstream")]
#[command(about = "tRust upstream Rust tracking and sync tool")]
#[command(version)]
struct Cli {
    #[command(subcommand)]
    command: Commands,

    /// Enable verbose output
    #[arg(short, long, global = true)]
    verbose: bool,

    /// Path to tRust root directory
    #[arg(long, global = true, default_value = ".")]
    trust_root: String,
}

#[derive(Subcommand)]
enum Commands {
    /// Check for new Rust releases
    Monitor {
        /// Check immediately instead of using cache
        #[arg(long)]
        check_now: bool,

        /// Output format (human, json)
        #[arg(long, default_value = "human")]
        format: String,
    },

    /// Analyze impact of upgrading to a specific version
    Analyze {
        /// Target version to analyze (e.g., 1.84.0)
        version: String,

        /// Output format (human, json)
        #[arg(long, default_value = "human")]
        format: String,
    },

    /// Show current sync status
    Status {
        /// Output format (human, json)
        #[arg(long, default_value = "human")]
        format: String,
    },

    /// Perform upstream sync
    Sync {
        /// Target version to sync to
        #[arg(long)]
        to: String,

        /// Dry run - show what would happen without making changes
        #[arg(long)]
        dry_run: bool,

        /// Resume a previously failed sync
        #[arg(long)]
        resume: bool,

        /// Rollback a failed sync
        #[arg(long)]
        rollback: bool,

        /// Skip tests after sync
        #[arg(long)]
        skip_tests: bool,
    },

    /// Show sync history
    History {
        /// Number of entries to show
        #[arg(long, default_value = "10")]
        last: usize,

        /// Show verbose details
        #[arg(long)]
        verbose: bool,
    },

    /// Generate sync report
    Report {
        /// Sync ID to report on (default: latest)
        #[arg(long)]
        sync_id: Option<String>,

        /// Output file path
        #[arg(long)]
        output: Option<String>,
    },

    /// Initialize the tracking database
    Init,
}

#[tokio::main]
async fn main() -> Result<()> {
    let cli = Cli::parse();

    // Initialize logging
    let filter = if cli.verbose {
        "trust_upstream=debug,info"
    } else {
        "trust_upstream=info,warn"
    };

    tracing_subscriber::registry()
        .with(
            tracing_subscriber::EnvFilter::try_from_default_env().unwrap_or_else(|_| filter.into()),
        )
        .with(tracing_subscriber::fmt::layer())
        .init();

    let trust_root = std::path::PathBuf::from(&cli.trust_root);

    match cli.command {
        Commands::Monitor { check_now, format } => {
            cmd_monitor(&trust_root, check_now, &format).await
        }
        Commands::Analyze { version, format } => cmd_analyze(&trust_root, &version, &format),
        Commands::Status { format } => cmd_status(&trust_root, &format),
        Commands::Sync {
            to,
            dry_run,
            resume,
            rollback,
            skip_tests,
        } => cmd_sync(&trust_root, &to, dry_run, resume, rollback, skip_tests),
        Commands::History { last, verbose } => cmd_history(&trust_root, last, verbose),
        Commands::Report { sync_id, output } => cmd_report(&trust_root, sync_id, output),
        Commands::Init => cmd_init(&trust_root).await,
    }
}

async fn cmd_monitor(trust_root: &std::path::Path, check_now: bool, format: &str) -> Result<()> {
    let monitor = ReleaseMonitor::new(trust_root)?;

    let releases = if check_now {
        monitor.fetch_releases().await?
    } else {
        monitor.get_cached_releases()?
    };

    let current = monitor.get_current_version()?;
    let latest = releases.current_stable.clone();

    if format == "json" {
        let output = serde_json::json!({
            "current_base": current,
            "latest_stable": latest,
            "releases_behind": releases.releases_behind(&current),
            "available_versions": releases.versions_after(&current),
            "last_check": releases.last_check,
        });
        println!("{}", serde_json::to_string_pretty(&output)?);
    } else {
        println!("=== Rust Release Status ===");
        println!();
        println!("tRust base version:  {current}");
        println!("Latest stable Rust:  {latest}");
        println!();

        let behind = releases.releases_behind(&current);
        if behind == 0 {
            println!("✓ tRust is up to date!");
        } else {
            println!("⚠ tRust is {behind} release(s) behind");
            println!();
            println!("Available versions to sync:");
            for ver in releases.versions_after(&current) {
                println!("  - {ver}");
            }
        }
    }

    Ok(())
}

fn cmd_analyze(trust_root: &std::path::Path, version: &str, format: &str) -> Result<()> {
    let analyzer = ImpactAnalyzer::new(trust_root)?;
    let report = analyzer.analyze(version)?;

    if format == "json" {
        println!("{}", serde_json::to_string_pretty(&report)?);
    } else {
        println!("=== Impact Analysis: {version} ===");
        println!();
        println!("From version:     {}", report.from_version);
        println!("To version:       {}", report.to_version);
        println!("Overall risk:     {:?}", report.overall_risk);
        println!("Estimated effort: {}", report.estimated_effort);
        println!();

        if report.affected_files.is_empty() {
            println!("No tRust integration points affected.");
        } else {
            println!("Affected files:");
            for file in &report.affected_files {
                println!("  {} ({:?})", file.path, file.risk);
                for change in &file.changes {
                    println!("    - {change}");
                }
            }
        }

        if !report.conflicts_expected.is_empty() {
            println!();
            println!("Expected conflicts:");
            for conflict in &report.conflicts_expected {
                println!("  - {conflict}");
            }
        }
    }

    Ok(())
}

fn cmd_status(trust_root: &std::path::Path, format: &str) -> Result<()> {
    let monitor = ReleaseMonitor::new(trust_root)?;
    let db = SyncDatabase::open(trust_root)?;

    let current = monitor.get_current_version()?;
    let releases = monitor.get_cached_releases().unwrap_or_default();
    let latest = releases.current_stable.clone();
    let behind = releases.releases_behind(&current);
    let ahead = {
        let current_minor = current
            .split('.')
            .nth(1)
            .and_then(|s| s.parse::<usize>().ok())
            .unwrap_or(0);
        let latest_minor = latest
            .split('.')
            .nth(1)
            .and_then(|s| s.parse::<usize>().ok())
            .unwrap_or(0);
        current_minor.saturating_sub(latest_minor)
    };
    let last_sync = db.get_last_sync()?;

    if format == "json" {
        let status = if current == "unknown" || latest == "unknown" {
            "unknown"
        } else if ahead > 0 {
            "ahead"
        } else if behind == 0 {
            "current"
        } else if behind == 1 {
            "slightly_behind"
        } else {
            "critical_behind"
        };

        let output = serde_json::json!({
            "current_base": current,
            "latest_stable": latest,
            "releases_behind": behind,
            "releases_ahead": ahead,
            "status": status,
            "last_sync": last_sync.map(|s| serde_json::json!({
                "id": s.id,
                "to_version": s.to_version,
                "completed_at": s.completed_at,
                "status": s.status,
            })),
        });
        println!("{}", serde_json::to_string_pretty(&output)?);
    } else {
        println!("=== tRust Upstream Sync Status ===");
        println!();
        println!("Current base:    {current}");
        println!("Latest stable:   {latest}");
        if ahead > 0 && current != "unknown" && latest != "unknown" {
            println!("Releases ahead:  {ahead}");
        }
        println!("Releases behind: {behind}");
        println!();

        if current == "unknown" || latest == "unknown" {
            println!("Status: ? UNKNOWN (run: trust-upstream monitor --check-now)");
        } else if ahead > 0 {
            println!("Status: ✓ AHEAD OF STABLE (using nightly)");
        } else if behind == 0 {
            println!("Status: ✓ CURRENT");
        } else if behind == 1 {
            println!("Status: ⚠ SLIGHTLY BEHIND (sync soon)");
        } else {
            println!("Status: ✗ CRITICAL - {behind} releases behind!");
            println!();
            println!("ACTION REQUIRED: Run sync before other work");
            println!("  trust-upstream sync --to <next_version>");
        }

        if let Some(sync) = last_sync {
            println!();
            println!("Last sync:");
            println!("  To version:  {}", sync.to_version);
            println!("  Status:      {}", sync.status);
            if let Some(completed) = sync.completed_at {
                println!("  Completed:   {completed}");
            }
        }
    }

    Ok(())
}

fn cmd_sync(
    trust_root: &std::path::Path,
    to_version: &str,
    dry_run: bool,
    resume: bool,
    rollback: bool,
    skip_tests: bool,
) -> Result<()> {
    let pipeline = SyncPipeline::new(trust_root)?;

    if rollback {
        println!("Rolling back last sync...");
        pipeline.rollback()?;
        println!("Rollback complete.");
        return Ok(());
    }

    if resume {
        println!("Resuming previous sync...");
        pipeline.resume()?;
        return Ok(());
    }

    println!("=== Syncing to {to_version} ===");
    println!();

    if dry_run {
        println!("[DRY RUN] Would perform the following:");
        pipeline.dry_run(to_version)?;
        return Ok(());
    }

    let result = pipeline.run(to_version, skip_tests)?;

    if result.success {
        println!();
        println!("✓ Sync to {to_version} complete!");
        println!();
        println!("Summary:");
        println!("  Conflicts resolved: {}", result.conflicts_resolved);
        println!(
            "  Tests passed:       {}/{}",
            result.tests_passed, result.tests_total
        );
        println!("  Build time:         {}s", result.build_time_secs);
    } else {
        println!();
        println!("✗ Sync failed!");
        println!();
        println!("Error: {}", result.error.unwrap_or_default());
        println!();
        println!("To retry: trust-upstream sync --to {to_version} --resume");
        println!("To rollback: trust-upstream sync --rollback");
    }

    Ok(())
}

fn cmd_history(trust_root: &std::path::Path, last: usize, verbose: bool) -> Result<()> {
    let db = SyncDatabase::open(trust_root)?;
    let syncs = db.get_recent_syncs(last)?;

    if syncs.is_empty() {
        println!("No sync history found.");
        return Ok(());
    }

    println!("=== Sync History ===");
    println!();

    for sync in syncs {
        println!(
            "{} {} → {} [{}]",
            sync.started_at.format("%Y-%m-%d"),
            sync.from_version,
            sync.to_version,
            sync.status
        );

        if verbose {
            println!("  ID: {}", sync.id);
            if let Some(completed) = sync.completed_at {
                println!("  Completed: {completed}");
            }
            println!(
                "  Conflicts: {} ({} auto-resolved)",
                sync.conflicts_count, sync.conflicts_auto_resolved
            );
            println!("  Tests: {}/{}", sync.tests_passed, sync.tests_total());
            println!();
        }
    }

    Ok(())
}

fn cmd_report(
    trust_root: &std::path::Path,
    sync_id: Option<String>,
    output: Option<String>,
) -> Result<()> {
    let db = SyncDatabase::open(trust_root)?;

    let sync = if let Some(id) = sync_id {
        db.get_sync(&id)?
    } else {
        db.get_last_sync()?
    };

    let Some(sync) = sync else {
        println!("No sync found.");
        return Ok(());
    };

    let report = format!(
        r"# Sync Report: {} → {}

**Date**: {}
**Status**: {}
**Duration**: {}

## Metrics

| Metric | Value |
|--------|-------|
| Conflicts | {} |
| Auto-resolved | {} |
| Manual | {} |
| Tests passed | {} |
| Tests failed | {} |
| Build time | {}s |

## Files Changed

{}

## Notes

{}
",
        sync.from_version,
        sync.to_version,
        sync.started_at.format("%Y-%m-%d %H:%M:%S"),
        sync.status,
        sync.duration_str(),
        sync.conflicts_count,
        sync.conflicts_auto_resolved,
        sync.conflicts_manual_resolved,
        sync.tests_passed,
        sync.tests_total() - sync.tests_passed,
        sync.build_time_secs.unwrap_or(0),
        db::SyncOperation::affected_files_str(),
        sync.notes.as_deref().unwrap_or("None"),
    );

    if let Some(path) = output {
        std::fs::write(&path, &report)?;
        println!("Report written to: {path}");
    } else {
        println!("{report}");
    }

    Ok(())
}

async fn cmd_init(trust_root: &std::path::Path) -> Result<()> {
    println!("Initializing trust-upstream tracking database...");

    let db = SyncDatabase::create(trust_root)?;
    db.initialize_schema()?;

    println!("✓ Database initialized at ~/.trust/sync_history.db");

    // Also fetch initial releases
    println!("Fetching current Rust releases...");
    let monitor = ReleaseMonitor::new(trust_root)?;
    let releases = monitor.fetch_releases().await?;

    println!("✓ Found {} releases", releases.releases.len());
    println!("✓ Latest stable: {}", releases.current_stable);

    Ok(())
}
