//! Database for tracking sync operations

use anyhow::{Context, Result};
use chrono::{DateTime, Utc};
use rusqlite::{params, Connection};
use serde::{Deserialize, Serialize};
use std::path::Path;

const DB_FILE: &str = ".trust/sync_history.db";

/// Database for tracking sync operations
pub struct SyncDatabase {
    conn: Connection,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SyncOperation {
    pub id: String,
    pub from_version: String,
    pub to_version: String,
    pub started_at: DateTime<Utc>,
    pub completed_at: Option<DateTime<Utc>>,
    pub status: String,
    pub conflicts_count: usize,
    pub conflicts_auto_resolved: usize,
    pub conflicts_manual_resolved: usize,
    pub tests_passed: usize,
    pub tests_failed: usize,
    pub build_time_secs: Option<u64>,
    pub error_message: Option<String>,
    pub notes: Option<String>,
}

impl SyncOperation {
    #[must_use]
    pub const fn tests_total(&self) -> usize {
        self.tests_passed + self.tests_failed
    }

    #[must_use]
    pub fn duration_str(&self) -> String {
        if let Some(completed) = self.completed_at {
            let duration = completed - self.started_at;
            let secs = duration.num_seconds();
            if secs < 60 {
                format!("{secs}s")
            } else if secs < 3600 {
                format!("{}m {}s", secs / 60, secs % 60)
            } else {
                format!("{}h {}m", secs / 3600, (secs % 3600) / 60)
            }
        } else {
            "in progress".to_string()
        }
    }

    #[must_use]
    pub fn affected_files_str() -> String {
        // This would be populated from a related table
        "See conflict resolutions table".to_string()
    }
}

impl SyncDatabase {
    /// Open an existing database
    pub fn open(trust_root: &Path) -> Result<Self> {
        let home = dirs::home_dir().context("Cannot find home directory")?;
        let db_path = home.join(DB_FILE);

        if !db_path.exists() {
            return Self::create(trust_root);
        }

        let conn = Connection::open(&db_path)?;
        Ok(Self { conn })
    }

    /// Create a new database
    pub fn create(_trust_root: &Path) -> Result<Self> {
        let home = dirs::home_dir().context("Cannot find home directory")?;
        let db_path = home.join(DB_FILE);

        if let Some(parent) = db_path.parent() {
            std::fs::create_dir_all(parent)?;
        }

        let conn = Connection::open(&db_path)?;
        let db = Self { conn };
        db.initialize_schema()?;
        Ok(db)
    }

    /// Initialize the database schema
    pub fn initialize_schema(&self) -> Result<()> {
        self.conn.execute_batch(
            r"
            CREATE TABLE IF NOT EXISTS sync_operations (
                id TEXT PRIMARY KEY,
                from_version TEXT NOT NULL,
                to_version TEXT NOT NULL,
                started_at TEXT NOT NULL,
                completed_at TEXT,
                status TEXT NOT NULL DEFAULT 'pending',
                conflicts_count INTEGER DEFAULT 0,
                conflicts_auto_resolved INTEGER DEFAULT 0,
                conflicts_manual_resolved INTEGER DEFAULT 0,
                tests_passed INTEGER DEFAULT 0,
                tests_failed INTEGER DEFAULT 0,
                build_time_secs INTEGER,
                error_message TEXT,
                notes TEXT
            );

            CREATE TABLE IF NOT EXISTS conflict_resolutions (
                id TEXT PRIMARY KEY,
                sync_id TEXT NOT NULL REFERENCES sync_operations(id),
                file_path TEXT NOT NULL,
                conflict_type TEXT NOT NULL,
                resolution_type TEXT NOT NULL,
                resolution_description TEXT,
                created_at TEXT NOT NULL
            );

            CREATE INDEX IF NOT EXISTS idx_sync_started ON sync_operations(started_at DESC);
            CREATE INDEX IF NOT EXISTS idx_conflict_sync ON conflict_resolutions(sync_id);
            ",
        )?;

        Ok(())
    }

    /// Start a new sync operation
    pub fn start_sync(&self, from_version: &str, to_version: &str) -> Result<String> {
        let id = format!("sync-{}-{}", to_version, Utc::now().format("%Y%m%d%H%M%S"));
        let now = Utc::now().to_rfc3339();

        self.conn.execute(
            "INSERT INTO sync_operations (id, from_version, to_version, started_at, status)
             VALUES (?1, ?2, ?3, ?4, 'in_progress')",
            params![id, from_version, to_version, now],
        )?;

        Ok(id)
    }

    /// Mark a sync as complete
    pub fn complete_sync(&self, sync_id: &str, result: &crate::sync::SyncResult) -> Result<()> {
        let now = Utc::now().to_rfc3339();

        self.conn.execute(
            "UPDATE sync_operations SET
                completed_at = ?1,
                status = 'success',
                conflicts_count = ?2,
                tests_passed = ?3,
                tests_failed = ?4,
                build_time_secs = ?5
             WHERE id = ?6",
            params![
                now,
                result.conflicts_resolved,
                result.tests_passed,
                result.tests_total - result.tests_passed,
                result.build_time_secs,
                sync_id
            ],
        )?;

        Ok(())
    }

    /// Mark a sync as failed
    pub fn fail_sync(&self, sync_id: &str, error: &str) -> Result<()> {
        let now = Utc::now().to_rfc3339();

        self.conn.execute(
            "UPDATE sync_operations SET
                completed_at = ?1,
                status = 'failed',
                error_message = ?2
             WHERE id = ?3",
            params![now, error, sync_id],
        )?;

        Ok(())
    }

    /// Mark a sync as rolled back
    pub fn rollback_sync(&self, sync_id: &str) -> Result<()> {
        let now = Utc::now().to_rfc3339();

        self.conn.execute(
            "UPDATE sync_operations SET
                completed_at = ?1,
                status = 'rolled_back'
             WHERE id = ?2",
            params![now, sync_id],
        )?;

        Ok(())
    }

    /// Get the most recent sync
    pub fn get_last_sync(&self) -> Result<Option<SyncOperation>> {
        let mut stmt = self
            .conn
            .prepare("SELECT * FROM sync_operations ORDER BY started_at DESC LIMIT 1")?;

        let mut rows = stmt.query([])?;

        if let Some(row) = rows.next()? {
            Ok(Some(Self::row_to_sync_operation(row)?))
        } else {
            Ok(None)
        }
    }

    /// Get a specific sync by ID
    pub fn get_sync(&self, sync_id: &str) -> Result<Option<SyncOperation>> {
        let mut stmt = self
            .conn
            .prepare("SELECT * FROM sync_operations WHERE id = ?1")?;

        let mut rows = stmt.query(params![sync_id])?;

        if let Some(row) = rows.next()? {
            Ok(Some(Self::row_to_sync_operation(row)?))
        } else {
            Ok(None)
        }
    }

    /// Get recent syncs
    pub fn get_recent_syncs(&self, limit: usize) -> Result<Vec<SyncOperation>> {
        let mut stmt = self
            .conn
            .prepare("SELECT * FROM sync_operations ORDER BY started_at DESC LIMIT ?1")?;

        let mut rows = stmt.query(params![limit])?;
        let mut syncs = Vec::new();

        while let Some(row) = rows.next()? {
            syncs.push(Self::row_to_sync_operation(row)?);
        }

        Ok(syncs)
    }

    fn row_to_sync_operation(row: &rusqlite::Row) -> Result<SyncOperation> {
        let started_at_str: String = row.get("started_at")?;
        let started_at = DateTime::parse_from_rfc3339(&started_at_str)?.with_timezone(&Utc);

        let completed_at_str: Option<String> = row.get("completed_at")?;
        let completed_at = completed_at_str
            .and_then(|s| DateTime::parse_from_rfc3339(&s).ok())
            .map(|d| d.with_timezone(&Utc));

        Ok(SyncOperation {
            id: row.get("id")?,
            from_version: row.get("from_version")?,
            to_version: row.get("to_version")?,
            started_at,
            completed_at,
            status: row.get("status")?,
            conflicts_count: usize::try_from(row.get::<_, i64>("conflicts_count")?).unwrap_or(0),
            conflicts_auto_resolved: usize::try_from(row.get::<_, i64>("conflicts_auto_resolved")?)
                .unwrap_or(0),
            conflicts_manual_resolved: usize::try_from(
                row.get::<_, i64>("conflicts_manual_resolved")?,
            )
            .unwrap_or(0),
            tests_passed: usize::try_from(row.get::<_, i64>("tests_passed")?).unwrap_or(0),
            tests_failed: usize::try_from(row.get::<_, i64>("tests_failed")?).unwrap_or(0),
            build_time_secs: row
                .get::<_, Option<i64>>("build_time_secs")?
                .and_then(|v| u64::try_from(v).ok()),
            error_message: row.get("error_message")?,
            notes: row.get("notes")?,
        })
    }
}
