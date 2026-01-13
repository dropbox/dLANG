//! Impact analyzer - determines which upstream changes affect tRust

use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::path::{Path, PathBuf};
use std::process::Command;

/// tRust integration points that need to be monitored
const INTEGRATION_POINTS: &[(&str, &str, RiskLevel)] = &[
    (
        "compiler/rustc_interface/src/passes.rs",
        "Verification hook",
        RiskLevel::High,
    ),
    (
        "compiler/rustc_feature/src/builtin_attrs.rs",
        "Verification attributes",
        RiskLevel::High,
    ),
    (
        "compiler/rustc_session/src/options.rs",
        "-Zverify flag",
        RiskLevel::Medium,
    ),
    (
        "compiler/rustc_middle/src/ty/",
        "Type context APIs",
        RiskLevel::Medium,
    ),
    (
        "compiler/rustc_mir_build/",
        "MIR generation",
        RiskLevel::Medium,
    ),
    ("compiler/rustc_hir/", "HIR types", RiskLevel::Low),
];

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum RiskLevel {
    Low,
    Medium,
    High,
    Critical,
}

/// Analyzes the impact of upgrading to a specific rustc version
pub struct ImpactAnalyzer {
    #[allow(dead_code)]
    trust_root: PathBuf,
    upstream_dir: PathBuf,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ImpactReport {
    pub from_version: String,
    pub to_version: String,
    pub analysis_date: String,
    pub overall_risk: RiskLevel,
    pub affected_files: Vec<AffectedFile>,
    pub estimated_effort: String,
    pub auto_mergeable: bool,
    pub conflicts_expected: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AffectedFile {
    pub path: String,
    pub risk: RiskLevel,
    pub changes: Vec<String>,
    pub trust_action: String,
}

impl ImpactAnalyzer {
    pub fn new(trust_root: &Path) -> Result<Self> {
        let upstream_dir = trust_root.join("upstream/rustc");
        Ok(Self {
            trust_root: trust_root.to_path_buf(),
            upstream_dir,
        })
    }

    /// Analyze the impact of upgrading to a specific version
    pub fn analyze(&self, to_version: &str) -> Result<ImpactReport> {
        let from_version = self.get_current_version()?;

        tracing::info!("Analyzing impact: {} -> {}", from_version, to_version);

        // Fetch the target version tag
        self.fetch_version_tag(to_version)?;

        // Get diff for integration points
        let affected_files = self.analyze_integration_points(&from_version, to_version)?;

        // Calculate overall risk
        let overall_risk = affected_files
            .iter()
            .map(|f| f.risk)
            .max()
            .unwrap_or(RiskLevel::Low);

        // Estimate effort based on risk and file count
        let estimated_effort = match (affected_files.len(), overall_risk) {
            (0, _) => "0 commits (no changes needed)",
            (1..=2, RiskLevel::Low) => "1 commit",
            (1..=2, RiskLevel::Medium) => "1-2 commits",
            (1..=2, RiskLevel::High) => "2-3 commits",
            (3..=5, _) => "3-5 commits",
            _ => "5+ commits",
        }
        .to_string();

        // Determine if auto-merge is possible
        let auto_mergeable = overall_risk == RiskLevel::Low && affected_files.len() <= 2;

        // Predict conflicts
        let conflicts_expected: Vec<String> = affected_files
            .iter()
            .filter(|f| f.risk >= RiskLevel::High)
            .map(|f| format!("{} ({})", f.path, f.trust_action))
            .collect();

        Ok(ImpactReport {
            from_version,
            to_version: to_version.to_string(),
            analysis_date: chrono::Utc::now().format("%Y-%m-%d").to_string(),
            overall_risk,
            affected_files,
            estimated_effort,
            auto_mergeable,
            conflicts_expected,
        })
    }

    fn get_current_version(&self) -> Result<String> {
        let version_file = self.upstream_dir.join("src/version");
        if version_file.exists() {
            Ok(std::fs::read_to_string(&version_file)?.trim().to_string())
        } else {
            Ok("unknown".to_string())
        }
    }

    fn fetch_version_tag(&self, version: &str) -> Result<()> {
        tracing::info!("Fetching tag {} from upstream...", version);

        let output = Command::new("git")
            .args(["fetch", "origin", "tag", version, "--no-tags"])
            .current_dir(&self.upstream_dir)
            .output()
            .context("Failed to fetch version tag")?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            tracing::warn!("Tag fetch warning: {}", stderr);
        }

        Ok(())
    }

    fn analyze_integration_points(&self, from: &str, to: &str) -> Result<Vec<AffectedFile>> {
        let mut affected = Vec::new();

        for (path, description, risk) in INTEGRATION_POINTS {
            let changes = self.get_changes_for_path(from, to, path)?;

            if !changes.is_empty() {
                affected.push(AffectedFile {
                    path: (*path).to_string(),
                    risk: *risk,
                    changes,
                    trust_action: format!(
                        "Review and re-apply tRust modifications ({description})"
                    ),
                });
            }
        }

        Ok(affected)
    }

    fn get_changes_for_path(&self, from: &str, to: &str, path: &str) -> Result<Vec<String>> {
        let output = Command::new("git")
            .args(["diff", "--stat", &format!("{from}..{to}"), "--", path])
            .current_dir(&self.upstream_dir)
            .output();

        let Ok(output) = output else {
            return Ok(Vec::new());
        };

        if !output.status.success() {
            return Ok(Vec::new());
        }

        let diff_stat = String::from_utf8_lossy(&output.stdout);

        if diff_stat.trim().is_empty() {
            return Ok(Vec::new());
        }

        // Get a summary of changes
        let summary_output = Command::new("git")
            .args(["log", "--oneline", &format!("{from}..{to}"), "--", path])
            .current_dir(&self.upstream_dir)
            .output()?;

        let log = String::from_utf8_lossy(&summary_output.stdout);
        let changes: Vec<String> = log
            .lines()
            .take(5) // Limit to 5 most recent changes
            .map(std::string::ToString::to_string)
            .collect();

        Ok(changes)
    }
}

impl PartialOrd for RiskLevel {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for RiskLevel {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let self_val = match self {
            Self::Low => 0,
            Self::Medium => 1,
            Self::High => 2,
            Self::Critical => 3,
        };
        let other_val = match other {
            Self::Low => 0,
            Self::Medium => 1,
            Self::High => 2,
            Self::Critical => 3,
        };
        self_val.cmp(&other_val)
    }
}
