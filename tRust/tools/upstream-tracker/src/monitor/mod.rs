//! Release monitoring - tracks Rust releases from GitHub

use anyhow::{Context, Result};
use chrono::{DateTime, Utc};
use serde::{Deserialize, Serialize};
use std::path::{Path, PathBuf};

const GITHUB_RELEASES_URL: &str = "https://api.github.com/repos/rust-lang/rust/releases";
const CACHE_FILE: &str = ".trust/releases_cache.json";

/// Monitors Rust releases from GitHub
pub struct ReleaseMonitor {
    trust_root: PathBuf,
    cache_path: PathBuf,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReleaseDatabase {
    pub releases: Vec<RustRelease>,
    pub current_stable: String,
    pub last_check: DateTime<Utc>,
}

impl Default for ReleaseDatabase {
    fn default() -> Self {
        Self {
            releases: Vec::new(),
            current_stable: "unknown".to_string(),
            last_check: Utc::now(),
        }
    }
}

impl ReleaseDatabase {
    /// Count how many releases we're behind
    #[must_use]
    pub fn releases_behind(&self, current: &str) -> usize {
        let current_minor = parse_minor_version(current);
        let latest_minor = parse_minor_version(&self.current_stable);
        latest_minor.saturating_sub(current_minor)
    }

    /// Get versions after the given version
    #[must_use]
    pub fn versions_after(&self, current: &str) -> Vec<String> {
        let current_minor = parse_minor_version(current);
        self.releases
            .iter()
            .filter(|r| parse_minor_version(&r.version) > current_minor)
            .map(|r| r.version.clone())
            .collect()
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RustRelease {
    pub version: String,
    pub tag: String,
    pub release_date: Option<DateTime<Utc>>,
    pub blog_post: Option<String>,
    pub changelog_url: Option<String>,
    pub prerelease: bool,
}

#[derive(Debug, Deserialize)]
struct GitHubRelease {
    tag_name: String,
    published_at: Option<String>,
    prerelease: bool,
    #[allow(dead_code)]
    html_url: String,
}

impl ReleaseMonitor {
    pub fn new(trust_root: &Path) -> Result<Self> {
        let home = dirs::home_dir().context("Cannot find home directory")?;
        let cache_path = home.join(CACHE_FILE);

        Ok(Self {
            trust_root: trust_root.to_path_buf(),
            cache_path,
        })
    }

    /// Get the current tRust base version from the upstream rustc
    pub fn get_current_version(&self) -> Result<String> {
        let version_file = self.trust_root.join("upstream/rustc/src/version");

        if version_file.exists() {
            let version = std::fs::read_to_string(&version_file)?;
            Ok(version.trim().to_string())
        } else {
            // Try to get from rustc --version
            let output =
                std::process::Command::new(self.trust_root.join("build/host/stage1/bin/rustc"))
                    .arg("--version")
                    .output();

            if let Ok(output) = output {
                let version_str = String::from_utf8_lossy(&output.stdout);
                // Parse "rustc 1.83.0-dev" -> "1.83.0"
                if let Some(ver) = version_str.split_whitespace().nth(1) {
                    return Ok(ver.split('-').next().unwrap_or(ver).to_string());
                }
            }

            Ok("unknown".to_string())
        }
    }

    /// Fetch releases from GitHub API
    pub async fn fetch_releases(&self) -> Result<ReleaseDatabase> {
        tracing::info!("Fetching releases from GitHub...");

        let client = reqwest::Client::builder()
            .user_agent("trust-upstream/0.1.0")
            .build()?;

        let response: Vec<GitHubRelease> =
            client.get(GITHUB_RELEASES_URL).send().await?.json().await?;

        let releases: Vec<RustRelease> = response
            .into_iter()
            .filter(|r| r.tag_name.starts_with('1') && !r.prerelease)
            .map(|r| {
                let release_date = r.published_at.and_then(|s| {
                    DateTime::parse_from_rfc3339(&s)
                        .ok()
                        .map(|d| d.with_timezone(&Utc))
                });

                RustRelease {
                    version: r.tag_name.clone(),
                    tag: r.tag_name.clone(),
                    release_date,
                    blog_post: Some(format!(
                        "https://blog.rust-lang.org/{}/Rust-{}.html",
                        release_date
                            .map(|d| d.format("%Y/%m/%d").to_string())
                            .unwrap_or_default(),
                        r.tag_name.replace('.', "-")
                    )),
                    changelog_url: Some(format!(
                        "https://github.com/rust-lang/rust/blob/{}/RELEASES.md",
                        r.tag_name
                    )),
                    prerelease: r.prerelease,
                }
            })
            .collect();

        let current_stable = releases
            .first()
            .map_or_else(|| "unknown".to_string(), |r| r.version.clone());

        let db = ReleaseDatabase {
            releases,
            current_stable,
            last_check: Utc::now(),
        };

        // Cache the results
        self.save_cache(&db)?;

        Ok(db)
    }

    /// Get cached releases
    pub fn get_cached_releases(&self) -> Result<ReleaseDatabase> {
        if self.cache_path.exists() {
            let content = std::fs::read_to_string(&self.cache_path)?;
            let db: ReleaseDatabase = serde_json::from_str(&content)?;
            Ok(db)
        } else {
            Ok(ReleaseDatabase::default())
        }
    }

    fn save_cache(&self, db: &ReleaseDatabase) -> Result<()> {
        if let Some(parent) = self.cache_path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        let content = serde_json::to_string_pretty(db)?;
        std::fs::write(&self.cache_path, content)?;
        Ok(())
    }
}

/// Parse minor version number from version string (e.g., "1.84.0" -> 84)
fn parse_minor_version(version: &str) -> usize {
    version
        .split('.')
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(0)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_minor_version() {
        assert_eq!(parse_minor_version("1.83.0"), 83);
        assert_eq!(parse_minor_version("1.84.0"), 84);
        assert_eq!(parse_minor_version("1.91.1"), 91);
    }

    #[test]
    fn test_releases_behind() {
        let db = ReleaseDatabase {
            releases: vec![],
            current_stable: "1.91.0".to_string(),
            last_check: Utc::now(),
        };

        assert_eq!(db.releases_behind("1.83.0"), 8);
        assert_eq!(db.releases_behind("1.90.0"), 1);
        assert_eq!(db.releases_behind("1.91.0"), 0);
    }
}
