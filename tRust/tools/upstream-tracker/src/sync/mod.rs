//! Sync pipeline - orchestrates the upstream sync process

use anyhow::{bail, Context, Result};
use std::path::{Path, PathBuf};
use std::process::Command;

use crate::db::SyncDatabase;

/// Orchestrates the upstream sync process
pub struct SyncPipeline {
    trust_root: PathBuf,
    upstream_dir: PathBuf,
    db: SyncDatabase,
}

#[derive(Debug)]
pub struct SyncResult {
    pub success: bool,
    pub from_version: String,
    pub to_version: String,
    pub conflicts_resolved: usize,
    pub tests_passed: usize,
    pub tests_total: usize,
    pub build_time_secs: u64,
    pub error: Option<String>,
}

impl SyncPipeline {
    pub fn new(trust_root: &Path) -> Result<Self> {
        let upstream_dir = trust_root.join("upstream/rustc");
        let db = SyncDatabase::open(trust_root)?;

        Ok(Self {
            trust_root: trust_root.to_path_buf(),
            upstream_dir,
            db,
        })
    }

    /// Show what would happen without making changes
    pub fn dry_run(&self, to_version: &str) -> Result<()> {
        let from_version = self.get_current_version()?;

        println!("Dry run: {from_version} -> {to_version}");
        println!();
        println!("Steps that would be performed:");
        println!("  1. Fetch upstream tag {to_version}");
        println!("  2. Create sync branch: sync/{to_version}");
        println!("  3. Rebase tRust changes onto {to_version}");
        println!("  4. Resolve conflicts (if any)");
        println!("  5. Update version file to {to_version}");
        println!("  6. Build stage1 compiler (~30-60 min)");
        println!("  7. Run tRust tests");
        println!("  8. Merge to main branch");
        println!();

        // Show expected conflicts
        let analyzer = crate::ImpactAnalyzer::new(&self.trust_root)?;
        let report = analyzer.analyze(to_version)?;

        if report.conflicts_expected.is_empty() {
            println!("No conflicts expected.");
        } else {
            println!("Expected conflicts:");
            for conflict in &report.conflicts_expected {
                println!("  - {conflict}");
            }
        }

        println!();
        println!("Estimated effort: {}", report.estimated_effort);

        Ok(())
    }

    /// Run the full sync pipeline
    pub fn run(&self, to_version: &str, skip_tests: bool) -> Result<SyncResult> {
        let from_version = self.get_current_version()?;
        let sync_id = self.db.start_sync(&from_version, to_version)?;

        tracing::info!(
            "Starting sync {} -> {} (id: {})",
            from_version,
            to_version,
            sync_id
        );

        let mut result = SyncResult {
            success: false,
            from_version,
            to_version: to_version.to_string(),
            conflicts_resolved: 0,
            tests_passed: 0,
            tests_total: 0,
            build_time_secs: 0,
            error: None,
        };

        // Helper macro to handle stage failures consistently
        macro_rules! fail_stage {
            ($result:expr, $db:expr, $sync_id:expr, $msg:expr) => {{
                let error_msg = $msg;
                $result.error = Some(error_msg.clone());
                $db.fail_sync($sync_id, &error_msg)?;
                return Ok($result);
            }};
        }

        // Stage 1: Prepare
        println!("Stage 1/6: Preparing...");
        if let Err(e) = self.prepare(to_version) {
            fail_stage!(result, self.db, &sync_id, format!("Prepare failed: {}", e));
        }

        // Stage 2: Rebase
        println!("Stage 2/6: Rebasing...");
        match self.rebase(to_version) {
            Ok(conflicts) => {
                result.conflicts_resolved = conflicts;
            }
            Err(e) => {
                fail_stage!(result, self.db, &sync_id, format!("Rebase failed: {}", e));
            }
        }

        // Stage 3: Adapt
        println!("Stage 3/6: Adapting tRust code...");
        if let Err(e) = self.adapt() {
            fail_stage!(
                result,
                self.db,
                &sync_id,
                format!("Adaptation failed: {}", e)
            );
        }

        // Stage 4: Build
        println!("Stage 4/6: Building stage1 compiler...");
        let build_start = std::time::Instant::now();
        if let Err(e) = self.build() {
            fail_stage!(result, self.db, &sync_id, format!("Build failed: {}", e));
        }
        result.build_time_secs = build_start.elapsed().as_secs();

        // Stage 5: Test
        if skip_tests {
            println!("Stage 5/6: Skipping tests (--skip-tests)");
        } else {
            println!("Stage 5/6: Running tests...");
            match self.test() {
                Ok((passed, total)) => {
                    result.tests_passed = passed;
                    result.tests_total = total;
                    if passed < total {
                        fail_stage!(
                            result,
                            self.db,
                            &sync_id,
                            format!("Tests failed: {}/{}", passed, total)
                        );
                    }
                }
                Err(e) => {
                    fail_stage!(
                        result,
                        self.db,
                        &sync_id,
                        format!("Test execution failed: {}", e)
                    );
                }
            }
        }

        // Stage 6: Finalize
        println!("Stage 6/6: Finalizing...");
        if let Err(e) = self.finalize(to_version) {
            fail_stage!(result, self.db, &sync_id, format!("Finalize failed: {}", e));
        }

        result.success = true;
        self.db.complete_sync(&sync_id, &result)?;

        Ok(result)
    }

    /// Resume a previously failed sync
    pub fn resume(&self) -> Result<()> {
        let last_sync = self.db.get_last_sync()?.context("No previous sync found")?;

        if last_sync.status == "success" {
            bail!("Last sync was successful, nothing to resume");
        }

        tracing::info!("Resuming sync to {}", last_sync.to_version);

        // Check if we're on the sync branch
        let current_branch = self.get_current_branch()?;
        let expected_branch = format!("sync/{}", last_sync.to_version);

        if current_branch != expected_branch {
            println!("Switching to sync branch: {expected_branch}");
            Command::new("git")
                .args(["checkout", &expected_branch])
                .current_dir(&self.upstream_dir)
                .status()?;
        }

        // Check for rebase in progress
        let rebase_dir = self.upstream_dir.join(".git/rebase-merge");
        if rebase_dir.exists() {
            println!("Rebase in progress. Please resolve conflicts and run:");
            println!("  git rebase --continue");
            println!("Then run: trust-upstream sync --resume");
            return Ok(());
        }

        // Continue with remaining stages
        println!("Continuing from last checkpoint...");
        let result = self.run(&last_sync.to_version, false)?;

        if result.success {
            println!("Resume completed successfully!");
        } else {
            println!("Resume failed: {:?}", result.error);
        }

        Ok(())
    }

    /// Rollback a failed sync
    pub fn rollback(&self) -> Result<()> {
        let last_sync = self.db.get_last_sync()?.context("No previous sync found")?;

        tracing::info!("Rolling back sync to {}", last_sync.to_version);

        // Abort any in-progress rebase
        let rebase_dir = self.upstream_dir.join(".git/rebase-merge");
        if rebase_dir.exists() {
            Command::new("git")
                .args(["rebase", "--abort"])
                .current_dir(&self.upstream_dir)
                .status()?;
        }

        // Switch back to main
        Command::new("git")
            .args(["checkout", "main"])
            .current_dir(&self.upstream_dir)
            .status()?;

        // Delete sync branch
        let sync_branch = format!("sync/{}", last_sync.to_version);
        Command::new("git")
            .args(["branch", "-D", &sync_branch])
            .current_dir(&self.upstream_dir)
            .status()
            .ok(); // Ignore if branch doesn't exist

        self.db.rollback_sync(&last_sync.id)?;

        Ok(())
    }

    // --- Internal helpers ---

    fn get_current_version(&self) -> Result<String> {
        let version_file = self.upstream_dir.join("src/version");
        if version_file.exists() {
            Ok(std::fs::read_to_string(&version_file)?.trim().to_string())
        } else {
            Ok("unknown".to_string())
        }
    }

    fn get_current_branch(&self) -> Result<String> {
        let output = Command::new("git")
            .args(["branch", "--show-current"])
            .current_dir(&self.upstream_dir)
            .output()?;
        Ok(String::from_utf8_lossy(&output.stdout).trim().to_string())
    }

    fn prepare(&self, to_version: &str) -> Result<()> {
        // Fetch upstream tags
        Command::new("git")
            .args(["fetch", "origin", "--tags"])
            .current_dir(&self.upstream_dir)
            .status()
            .context("Failed to fetch upstream tags")?;

        // Create sync branch
        let sync_branch = format!("sync/{to_version}");
        Command::new("git")
            .args(["checkout", "-B", &sync_branch])
            .current_dir(&self.upstream_dir)
            .status()
            .context("Failed to create sync branch")?;

        Ok(())
    }

    fn rebase(&self, to_version: &str) -> Result<usize> {
        let output = Command::new("git")
            .args(["rebase", to_version])
            .current_dir(&self.upstream_dir)
            .output()?;

        if output.status.success() {
            return Ok(0);
        }
        let stderr = String::from_utf8_lossy(&output.stderr);
        if stderr.contains("CONFLICT") {
            bail!("Rebase conflicts detected. Manual resolution needed:\n{stderr}");
        }
        bail!("Rebase failed: {stderr}");
    }

    fn adapt(&self) -> Result<()> {
        // Check if rustc_verify still compiles
        let output = Command::new("cargo")
            .args(["check", "-p", "rustc_verify"])
            .current_dir(&self.upstream_dir)
            .output()?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            bail!("rustc_verify compilation failed:\n{stderr}");
        }

        Ok(())
    }

    fn build(&self) -> Result<()> {
        let status = Command::new("./x")
            .args(["build", "--stage", "1"])
            .current_dir(&self.upstream_dir)
            .status()
            .context("Failed to run x build")?;

        if !status.success() {
            bail!("Stage1 build failed");
        }

        Ok(())
    }

    fn test(&self) -> Result<(usize, usize)> {
        // Run tRust integration tests
        let output = Command::new("cargo")
            .args(["test"])
            .current_dir(&self.trust_root)
            .output()?;

        let stdout = String::from_utf8_lossy(&output.stdout);

        // Parse test results (simple heuristic)
        let mut passed = 0;
        let mut total = 0;

        for line in stdout.lines() {
            if line.contains("test result:") {
                // Parse "test result: ok. X passed; Y failed"
                if let Some(pos) = line.find("passed") {
                    let before = &line[..pos];
                    if let Some(num_str) = before.split_whitespace().last() {
                        passed = num_str.parse().unwrap_or(0);
                    }
                }
                if let Some(pos) = line.find("failed") {
                    let before = &line[..pos];
                    if let Some(num_str) = before.split_whitespace().last() {
                        let failed: usize = num_str.parse().unwrap_or(0);
                        total = passed + failed;
                    }
                }
            }
        }

        if total == 0 {
            total = passed; // If no failures reported
        }

        Ok((passed, total))
    }

    fn finalize(&self, to_version: &str) -> Result<()> {
        // Update version file
        let version_file = self.upstream_dir.join("src/version");
        std::fs::write(&version_file, to_version)?;

        // Commit version update
        Command::new("git")
            .args(["add", "src/version"])
            .current_dir(&self.upstream_dir)
            .status()?;

        Command::new("git")
            .args(["commit", "--amend", "--no-edit"])
            .current_dir(&self.upstream_dir)
            .status()?;

        // Merge to main
        Command::new("git")
            .args(["checkout", "main"])
            .current_dir(&self.upstream_dir)
            .status()?;

        let sync_branch = format!("sync/{to_version}");
        Command::new("git")
            .args(["merge", &sync_branch])
            .current_dir(&self.upstream_dir)
            .status()?;

        Ok(())
    }
}
