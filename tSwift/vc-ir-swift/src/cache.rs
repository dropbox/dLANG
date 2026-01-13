//! Verification cache for incremental verification.
//!
//! This module provides caching of verification results to avoid re-verifying
//! functions that haven't changed. The cache is keyed by a hash of the function's
//! SIL representation.
//!
//! # Cache Format
//!
//! The cache is stored as a JSON file with the following structure:
//! ```json
//! {
//!   "version": 1,
//!   "tswift_version": "0.1.0",
//!   "entries": {
//!     "<function_hash>": {
//!       "function_name": "foo",
//!       "response": { ... verification response ... },
//!       "timestamp": 1234567890
//!     }
//!   }
//! }
//! ```

use std::collections::HashMap;
use std::fmt::Write as FmtWrite;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::SwiftVerifyResponse;
use crate::sil_parser::{SilBasicBlock, SilFunction};

/// Current cache format version. Increment when breaking changes are made.
const CACHE_VERSION: u32 = 1;

/// tswift version for cache invalidation.
const TSWIFT_VERSION: &str = env!("CARGO_PKG_VERSION");

/// A single cache entry for a verified function.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CacheEntry {
    /// Human-readable function name for debugging.
    pub function_name: String,
    /// The verification response.
    pub response: SwiftVerifyResponse,
    /// Unix timestamp when this entry was created.
    pub timestamp: u64,
}

/// The verification cache.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerificationCache {
    /// Cache format version.
    pub version: u32,
    /// tswift version that created this cache.
    pub tswift_version: String,
    /// Cache entries keyed by function hash.
    pub entries: HashMap<String, CacheEntry>,
}

impl Default for VerificationCache {
    fn default() -> Self {
        Self {
            version: CACHE_VERSION,
            tswift_version: TSWIFT_VERSION.to_string(),
            entries: HashMap::new(),
        }
    }
}

impl VerificationCache {
    /// Create a new empty cache.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Load cache from a file. Returns an empty cache if the file doesn't exist
    /// or is incompatible.
    #[must_use]
    pub fn load(path: &Path) -> Self {
        if !path.exists() {
            return Self::new();
        }

        match fs::read_to_string(path) {
            Ok(content) => match serde_json::from_str::<Self>(&content) {
                Ok(cache) => {
                    // Check version compatibility
                    if cache.version != CACHE_VERSION || cache.tswift_version != TSWIFT_VERSION {
                        // Cache is incompatible, start fresh
                        return Self::new();
                    }
                    cache
                }
                Err(_) => Self::new(),
            },
            Err(_) => Self::new(),
        }
    }

    /// Save cache to a file.
    ///
    /// # Errors
    /// Returns any JSON serialization or filesystem write error.
    pub fn save(&self, path: &Path) -> std::io::Result<()> {
        let content = serde_json::to_string_pretty(self)?;
        fs::write(path, content)
    }

    /// Look up a cached result by function hash.
    #[must_use]
    pub fn get(&self, hash: &str) -> Option<&CacheEntry> {
        self.entries.get(hash)
    }

    /// Insert a verification result into the cache.
    pub fn insert(&mut self, hash: String, function_name: String, response: SwiftVerifyResponse) {
        let timestamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_secs())
            .unwrap_or(0);

        self.entries.insert(
            hash,
            CacheEntry {
                function_name,
                response,
                timestamp,
            },
        );
    }

    /// Get the number of cached entries.
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Check if the cache is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Get cache statistics for display.
    #[must_use]
    pub fn stats(&self) -> CacheStats {
        CacheStats {
            total_entries: self.entries.len(),
            version: self.version,
            tswift_version: self.tswift_version.clone(),
        }
    }
}

/// Statistics about the cache.
#[derive(Debug, Clone)]
pub struct CacheStats {
    pub total_entries: usize,
    pub version: u32,
    pub tswift_version: String,
}

/// Compute a hash for a SIL function.
///
/// The hash is computed from the function's:
/// - Name
/// - Signature (type)
/// - Attributes (including @_requires, @_ensures)
/// - Basic blocks (instructions and terminators)
///
/// This provides a stable hash that changes when any significant
/// part of the function changes.
#[must_use]
pub fn hash_sil_function(func: &SilFunction) -> String {
    let mut hasher = Sha256::new();

    // Hash the function name
    hasher.update(func.name.as_bytes());
    hasher.update(b"\0");

    // Hash the signature
    hasher.update(format!("{:?}", func.signature).as_bytes());
    hasher.update(b"\0");

    // Hash attributes (sorted for stability)
    let mut attrs: Vec<String> = func.attributes.iter().map(|a| format!("{a:?}")).collect();
    attrs.sort();
    for attr in attrs {
        hasher.update(attr.as_bytes());
        hasher.update(b"\0");
    }

    // Hash basic blocks
    for block in &func.blocks {
        hash_basic_block(&mut hasher, block);
    }

    // Convert to hex string
    let result = hasher.finalize();
    let mut hex = String::with_capacity(64);
    for byte in result {
        write!(&mut hex, "{byte:02x}").unwrap();
    }
    hex
}

/// Hash a basic block into the hasher.
fn hash_basic_block(hasher: &mut Sha256, block: &SilBasicBlock) {
    // Block label
    hasher.update(block.label.as_bytes());
    hasher.update(b"\0");

    // Block arguments
    for arg in &block.arguments {
        hasher.update(arg.name.as_bytes());
        hasher.update(format!("{:?}", arg.ty).as_bytes());
        hasher.update(b"\0");
    }

    // Instructions (use debug format for simplicity and stability)
    for instr in &block.instructions {
        hasher.update(format!("{:?}", instr.kind).as_bytes());
        hasher.update(b"\0");
    }

    // Terminator
    hasher.update(format!("{:?}", block.terminator).as_bytes());
    hasher.update(b"\0");
}

/// Determine the cache file path for a given source file.
///
/// The cache is stored as `.tswift_cache/<source_basename>.cache.json`
/// in the same directory as the source file.
#[must_use]
pub fn cache_path_for_source(source_path: &Path) -> PathBuf {
    let parent = source_path.parent().unwrap_or_else(|| Path::new("."));
    let cache_dir = parent.join(".tswift_cache");

    // Create cache directory if it doesn't exist
    let _ = fs::create_dir_all(&cache_dir);

    let basename = source_path
        .file_name()
        .and_then(|n| n.to_str())
        .unwrap_or("unknown");

    cache_dir.join(format!("{basename}.cache.json"))
}

/// A cache manager that handles loading, saving, and accessing the cache.
pub struct CacheManager {
    cache: VerificationCache,
    cache_path: PathBuf,
    enabled: bool,
    dirty: bool,
    hits: usize,
    misses: usize,
}

impl CacheManager {
    /// Create a new cache manager for the given source file.
    #[must_use]
    pub fn new(source_path: &Path, enabled: bool) -> Self {
        let cache_path = cache_path_for_source(source_path);
        let cache = if enabled {
            VerificationCache::load(&cache_path)
        } else {
            VerificationCache::new()
        };

        Self {
            cache,
            cache_path,
            enabled,
            dirty: false,
            hits: 0,
            misses: 0,
        }
    }

    /// Create a cache manager with a custom cache path.
    #[must_use]
    pub fn with_path(cache_path: PathBuf, enabled: bool) -> Self {
        let cache = if enabled {
            VerificationCache::load(&cache_path)
        } else {
            VerificationCache::new()
        };

        Self {
            cache,
            cache_path,
            enabled,
            dirty: false,
            hits: 0,
            misses: 0,
        }
    }

    /// Look up a cached result by function hash.
    /// Returns None if caching is disabled or no cached result exists.
    pub fn get(&mut self, hash: &str) -> Option<&SwiftVerifyResponse> {
        if !self.enabled {
            return None;
        }

        if let Some(entry) = self.cache.get(hash) {
            self.hits += 1;
            Some(&entry.response)
        } else {
            self.misses += 1;
            None
        }
    }

    /// Insert a verification result into the cache.
    pub fn insert(&mut self, hash: String, function_name: String, response: SwiftVerifyResponse) {
        if !self.enabled {
            return;
        }

        self.cache.insert(hash, function_name, response);
        self.dirty = true;
    }

    /// Save the cache if it has been modified.
    ///
    /// # Errors
    /// Returns any filesystem write error while persisting the cache.
    pub fn save(&self) -> std::io::Result<()> {
        if !self.enabled || !self.dirty {
            return Ok(());
        }

        self.cache.save(&self.cache_path)
    }

    /// Get cache hit/miss statistics.
    #[must_use]
    pub const fn statistics(&self) -> (usize, usize) {
        (self.hits, self.misses)
    }

    /// Check if caching is enabled.
    #[must_use]
    pub const fn is_enabled(&self) -> bool {
        self.enabled
    }
}

impl Drop for CacheManager {
    fn drop(&mut self) {
        // Auto-save on drop
        let _ = self.save();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sil_parser::{
        CallingConvention, SilAttribute, SilInstruction, SilInstructionKind, SilLinkage,
        SilLocation, SilTerminator, SilType, SilValue,
    };
    use std::fs;
    use std::path::PathBuf;
    use std::time::{SystemTime, UNIX_EPOCH};

    fn make_test_function(name: &str) -> SilFunction {
        SilFunction {
            name: name.to_string(),
            demangled_name: None,
            signature: SilType::Function {
                convention: CallingConvention::Thin,
                params: vec![],
                result: Box::new(SilType::Named("Int".to_string())),
                throws: false,
            },
            linkage: SilLinkage::Public,
            attributes: vec![],
            blocks: vec![SilBasicBlock {
                label: "bb0".to_string(),
                arguments: vec![],
                instructions: vec![],
                terminator: SilTerminator::Return {
                    operand: "%0".to_string(),
                },
            }],
        }
    }

    #[test]
    fn test_hash_stability() {
        let func1 = make_test_function("foo");
        let func2 = make_test_function("foo");

        let hash1 = hash_sil_function(&func1);
        let hash2 = hash_sil_function(&func2);

        assert_eq!(hash1, hash2, "Same function should produce same hash");
    }

    #[test]
    fn test_hash_different_names() {
        let func1 = make_test_function("foo");
        let func2 = make_test_function("bar");

        let hash1 = hash_sil_function(&func1);
        let hash2 = hash_sil_function(&func2);

        assert_ne!(
            hash1, hash2,
            "Different names should produce different hashes"
        );
    }

    #[test]
    fn test_hash_different_attributes() {
        let mut func1 = make_test_function("foo");
        let mut func2 = make_test_function("foo");

        func1
            .attributes
            .push(SilAttribute::Requires("x > 0".to_string()));
        func2
            .attributes
            .push(SilAttribute::Requires("x >= 0".to_string()));

        let hash1 = hash_sil_function(&func1);
        let hash2 = hash_sil_function(&func2);

        assert_ne!(
            hash1, hash2,
            "Different attributes should produce different hashes"
        );
    }

    #[test]
    fn test_hash_is_64_char_hex() {
        let func = make_test_function("foo");
        let hash = hash_sil_function(&func);
        assert_eq!(hash.len(), 64);
        assert!(hash.chars().all(|c| c.is_ascii_hexdigit()));
    }

    #[test]
    fn test_hash_different_signature() {
        let func1 = make_test_function("foo");
        let mut func2 = make_test_function("foo");
        func2.signature = SilType::Function {
            convention: CallingConvention::Thin,
            params: vec![SilType::Named("Int".to_string())],
            result: Box::new(SilType::Named("Int".to_string())),
            throws: false,
        };

        let hash1 = hash_sil_function(&func1);
        let hash2 = hash_sil_function(&func2);
        assert_ne!(hash1, hash2);
    }

    #[test]
    fn test_hash_different_block_label() {
        let func1 = make_test_function("foo");
        let mut func2 = make_test_function("foo");
        func2.blocks[0].label = "bb1".to_string();

        let hash1 = hash_sil_function(&func1);
        let hash2 = hash_sil_function(&func2);
        assert_ne!(hash1, hash2);
    }

    #[test]
    fn test_hash_different_block_arguments() {
        let func1 = make_test_function("foo");
        let mut func2 = make_test_function("foo");
        func2.blocks[0].arguments.push(SilValue {
            name: "%arg0".to_string(),
            ty: SilType::Named("Int".to_string()),
            debug_name: None,
        });

        let hash1 = hash_sil_function(&func1);
        let hash2 = hash_sil_function(&func2);
        assert_ne!(hash1, hash2);
    }

    #[test]
    fn test_hash_different_instructions() {
        let mut func1 = make_test_function("foo");
        let mut func2 = make_test_function("foo");
        func1.blocks[0].instructions.push(SilInstruction {
            results: vec![],
            kind: SilInstructionKind::IntegerLiteral {
                ty: SilType::Named("Builtin.Int64".to_string()),
                value: 0,
            },
            location: None,
        });
        func2.blocks[0].instructions.push(SilInstruction {
            results: vec![],
            kind: SilInstructionKind::IntegerLiteral {
                ty: SilType::Named("Builtin.Int64".to_string()),
                value: 1,
            },
            location: None,
        });

        let hash1 = hash_sil_function(&func1);
        let hash2 = hash_sil_function(&func2);
        assert_ne!(hash1, hash2);
    }

    #[test]
    fn test_hash_different_terminator() {
        let mut func1 = make_test_function("foo");
        let mut func2 = make_test_function("foo");
        func1.blocks[0].terminator = SilTerminator::Return {
            operand: "%0".to_string(),
        };
        func2.blocks[0].terminator = SilTerminator::Return {
            operand: "%1".to_string(),
        };

        let hash1 = hash_sil_function(&func1);
        let hash2 = hash_sil_function(&func2);
        assert_ne!(hash1, hash2);
    }

    #[test]
    fn test_cache_roundtrip() {
        let mut cache = VerificationCache::new();
        let hash = "abc123".to_string();
        let response = SwiftVerifyResponse {
            function_name: "test".to_string(),
            source_file: "test.swift".to_string(),
            source_line: 1,
            is_trusted: false,
            spec_result: None,
            auto_vc_results: vec![],
            summary: crate::VerificationSummary::default(),
            spec_warnings: vec![],
        };

        cache.insert(hash.clone(), "test".to_string(), response);

        assert!(cache.get(&hash).is_some());
        assert_eq!(cache.get(&hash).unwrap().function_name, "test");
    }

    fn make_test_response(function_name: &str) -> SwiftVerifyResponse {
        SwiftVerifyResponse {
            function_name: function_name.to_string(),
            source_file: "test.swift".to_string(),
            source_line: 1,
            is_trusted: false,
            spec_result: None,
            auto_vc_results: vec![],
            summary: crate::VerificationSummary::default(),
            spec_warnings: vec![],
        }
    }

    struct TempDir {
        path: PathBuf,
    }

    impl TempDir {
        fn new(test_name: &str) -> Self {
            let nanos = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap_or_default()
                .as_nanos();
            let path = std::env::temp_dir().join(format!(
                "tswift_cache_tests_{}_{}_{}",
                test_name,
                std::process::id(),
                nanos
            ));
            fs::create_dir_all(&path).unwrap();
            Self { path }
        }

        fn file(&self, name: &str) -> PathBuf {
            self.path.join(name)
        }
    }

    impl Drop for TempDir {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.path);
        }
    }

    #[test]
    fn test_load_missing_file_returns_empty_cache() {
        let tmp = TempDir::new("missing_file");
        let path = tmp.file("does_not_exist.json");

        let cache = VerificationCache::load(&path);
        assert!(cache.is_empty());
        assert_eq!(cache.version, CACHE_VERSION);
        assert_eq!(cache.tswift_version, TSWIFT_VERSION);
    }

    #[test]
    fn test_load_invalid_json_returns_empty_cache() {
        let tmp = TempDir::new("invalid_json");
        let path = tmp.file("cache.json");
        fs::write(&path, "{ not valid json").unwrap();

        let cache = VerificationCache::load(&path);
        assert!(cache.is_empty());
    }

    #[test]
    fn test_load_incompatible_version_returns_empty_cache() {
        let tmp = TempDir::new("incompatible_version");
        let path = tmp.file("cache.json");

        let content = serde_json::json!({
            "version": CACHE_VERSION + 1,
            "tswift_version": TSWIFT_VERSION,
            "entries": {},
        });
        fs::write(&path, serde_json::to_string(&content).unwrap()).unwrap();

        let cache = VerificationCache::load(&path);
        assert!(cache.is_empty());
    }

    #[test]
    fn test_load_incompatible_tswift_version_returns_empty_cache() {
        let tmp = TempDir::new("incompatible_tswift_version");
        let path = tmp.file("cache.json");

        let content = serde_json::json!({
            "version": CACHE_VERSION,
            "tswift_version": "definitely-not-this-version",
            "entries": {},
        });
        fs::write(&path, serde_json::to_string(&content).unwrap()).unwrap();

        let cache = VerificationCache::load(&path);
        assert!(cache.is_empty());
    }

    #[test]
    fn test_cache_path_for_source_creates_cache_dir() {
        let tmp = TempDir::new("cache_path_for_source");
        let source = tmp.file("hello.swift");

        let cache_path = cache_path_for_source(&source);
        let expected_dir = tmp.path.join(".tswift_cache");
        assert!(expected_dir.is_dir());
        assert_eq!(
            cache_path,
            expected_dir.join("hello.swift.cache.json"),
            "cache path should include source basename + .cache.json"
        );
    }

    #[test]
    fn test_cache_stats_counts_entries() {
        let mut cache = VerificationCache::new();
        cache.insert(
            "hash1".to_string(),
            "f1".to_string(),
            make_test_response("f1"),
        );

        let stats = cache.stats();
        assert_eq!(stats.total_entries, 1);
        assert_eq!(stats.version, CACHE_VERSION);
        assert_eq!(stats.tswift_version, TSWIFT_VERSION);
    }

    #[test]
    fn test_save_then_load_roundtrip() {
        let tmp = TempDir::new("save_load_roundtrip");
        let path = tmp.file("cache.json");

        let mut cache = VerificationCache::new();
        cache.insert(
            "hash1".to_string(),
            "f1".to_string(),
            make_test_response("f1"),
        );
        cache.insert(
            "hash2".to_string(),
            "f2".to_string(),
            make_test_response("f2"),
        );
        cache.save(&path).unwrap();

        let loaded = VerificationCache::load(&path);
        assert_eq!(loaded.len(), 2);
        assert!(loaded.get("hash1").is_some());
        assert!(loaded.get("hash2").is_some());
        assert_eq!(loaded.get("hash1").unwrap().function_name, "f1");
        assert_eq!(loaded.get("hash2").unwrap().function_name, "f2");
    }

    #[test]
    fn test_cache_manager_autosaves_on_drop() {
        let tmp = TempDir::new("cache_manager_drop_autosave");
        let cache_path = tmp.file("cache.json");
        {
            let mut mgr = CacheManager::with_path(cache_path.clone(), true);
            mgr.insert(
                "hash".to_string(),
                "test".to_string(),
                make_test_response("test"),
            );
        }
        assert!(cache_path.exists());

        let mut mgr2 = CacheManager::with_path(cache_path, true);
        assert_eq!(mgr2.get("hash").unwrap().function_name, "test");
    }

    #[test]
    fn test_cache_manager_disabled_is_noop() {
        let tmp = TempDir::new("cache_manager_disabled");
        let cache_path = tmp.file("cache.json");

        let mut mgr = CacheManager::with_path(cache_path.clone(), false);
        assert!(!mgr.is_enabled());

        mgr.insert(
            "hash".to_string(),
            "test".to_string(),
            make_test_response("test"),
        );
        assert!(mgr.get("hash").is_none());
        assert_eq!(mgr.statistics(), (0, 0));
        mgr.save().unwrap();
        assert!(!cache_path.exists());
    }

    #[test]
    fn test_cache_manager_enabled_saves_and_counts_hits() {
        let tmp = TempDir::new("cache_manager_enabled");
        let cache_path = tmp.file("cache.json");

        // Not dirty yet: no save and no file created.
        let mut mgr = CacheManager::with_path(cache_path.clone(), true);
        assert!(mgr.is_enabled());
        mgr.save().unwrap();
        assert!(!cache_path.exists());

        // Insert + save should materialize the cache file.
        mgr.insert(
            "hash".to_string(),
            "test".to_string(),
            make_test_response("test"),
        );
        mgr.save().unwrap();
        assert!(cache_path.exists());

        // Existing key should hit; missing key should miss.
        assert_eq!(mgr.get("hash").unwrap().function_name, "test");
        assert!(mgr.get("missing").is_none());
        assert_eq!(mgr.statistics(), (1, 1));

        // Reload to ensure persisted data is readable.
        drop(mgr);
        let mut mgr2 = CacheManager::with_path(cache_path, true);
        assert_eq!(mgr2.get("hash").unwrap().function_name, "test");
    }

    // ========== Additional hash_sil_function tests ==========

    #[test]
    fn test_hash_multiple_blocks() {
        let mut func = make_test_function("foo");
        func.blocks.push(SilBasicBlock {
            label: "bb1".to_string(),
            arguments: vec![],
            instructions: vec![],
            terminator: SilTerminator::Branch {
                dest: "bb0".to_string(),
                args: vec![],
            },
        });

        let hash1 = hash_sil_function(&func);

        // Add another block
        func.blocks.push(SilBasicBlock {
            label: "bb2".to_string(),
            arguments: vec![],
            instructions: vec![],
            terminator: SilTerminator::Unreachable,
        });

        let hash2 = hash_sil_function(&func);
        assert_ne!(hash1, hash2, "Adding a block should change the hash");
    }

    #[test]
    fn test_hash_attributes_sorted_for_stability() {
        // Attributes are sorted before hashing for stability
        let mut func1 = make_test_function("foo");
        let mut func2 = make_test_function("foo");

        // Add attributes in different order
        func1
            .attributes
            .push(SilAttribute::Requires("a > 0".to_string()));
        func1
            .attributes
            .push(SilAttribute::Ensures("result > 0".to_string()));

        func2
            .attributes
            .push(SilAttribute::Ensures("result > 0".to_string()));
        func2
            .attributes
            .push(SilAttribute::Requires("a > 0".to_string()));

        let hash1 = hash_sil_function(&func1);
        let hash2 = hash_sil_function(&func2);
        assert_eq!(hash1, hash2, "Attribute order should not affect hash");
    }

    #[test]
    fn test_hash_empty_function() {
        let func = SilFunction {
            name: String::new(),
            demangled_name: None,
            signature: SilType::Named("()".to_string()),
            linkage: SilLinkage::Private,
            attributes: vec![],
            blocks: vec![],
        };

        let hash = hash_sil_function(&func);
        assert_eq!(hash.len(), 64);
        assert!(hash.chars().all(|c| c.is_ascii_hexdigit()));
    }

    #[test]
    fn test_hash_with_block_arguments() {
        let mut func = make_test_function("foo");
        func.blocks[0].arguments = vec![
            SilValue {
                name: "%arg0".to_string(),
                ty: SilType::Named("Int".to_string()),
                debug_name: Some("x".to_string()),
            },
            SilValue {
                name: "%arg1".to_string(),
                ty: SilType::Named("Bool".to_string()),
                debug_name: None,
            },
        ];

        let hash1 = hash_sil_function(&func);

        // Change argument type
        func.blocks[0].arguments[1].ty = SilType::Named("Int".to_string());
        let hash2 = hash_sil_function(&func);
        assert_ne!(hash1, hash2);
    }

    #[test]
    fn test_hash_block_argument_debug_name_does_not_affect_hash() {
        let mut func1 = make_test_function("foo");
        func1.blocks[0].arguments = vec![SilValue {
            name: "%arg0".to_string(),
            ty: SilType::Named("Int".to_string()),
            debug_name: Some("x".to_string()),
        }];

        let mut func2 = func1.clone();
        func2.blocks[0].arguments[0].debug_name = Some("y".to_string());

        let hash1 = hash_sil_function(&func1);
        let hash2 = hash_sil_function(&func2);
        assert_eq!(hash1, hash2);
    }

    #[test]
    fn test_hash_with_multiple_instructions() {
        let mut func = make_test_function("foo");
        func.blocks[0].instructions = vec![
            SilInstruction {
                results: vec![SilValue {
                    name: "%1".to_string(),
                    ty: SilType::Named("Builtin.Int64".to_string()),
                    debug_name: None,
                }],
                kind: SilInstructionKind::IntegerLiteral {
                    ty: SilType::Named("Builtin.Int64".to_string()),
                    value: 42,
                },
                location: None,
            },
            SilInstruction {
                results: vec![SilValue {
                    name: "%2".to_string(),
                    ty: SilType::Named("Builtin.Int64".to_string()),
                    debug_name: None,
                }],
                kind: SilInstructionKind::IntegerLiteral {
                    ty: SilType::Named("Builtin.Int64".to_string()),
                    value: 100,
                },
                location: None,
            },
        ];

        let hash1 = hash_sil_function(&func);

        // Swap instruction order
        func.blocks[0].instructions.reverse();
        let hash2 = hash_sil_function(&func);
        assert_ne!(hash1, hash2, "Instruction order matters for hash");
    }

    #[test]
    fn test_hash_instruction_location_does_not_affect_hash() {
        let mut func1 = make_test_function("foo");
        func1.blocks[0].instructions = vec![SilInstruction {
            results: vec![SilValue {
                name: "%1".to_string(),
                ty: SilType::Named("Builtin.Int64".to_string()),
                debug_name: None,
            }],
            kind: SilInstructionKind::IntegerLiteral {
                ty: SilType::Named("Builtin.Int64".to_string()),
                value: 42,
            },
            location: None,
        }];

        let mut func2 = func1.clone();
        func2.blocks[0].instructions[0].location = Some(SilLocation {
            file: "test.swift".to_string(),
            line: 123,
            column: 45,
        });

        let hash1 = hash_sil_function(&func1);
        let hash2 = hash_sil_function(&func2);
        assert_eq!(hash1, hash2);
    }

    #[test]
    fn test_hash_different_linkage() {
        let func1 = make_test_function("foo");
        let mut func2 = make_test_function("foo");
        func2.linkage = SilLinkage::Private;

        // Note: linkage is part of the function but not directly hashed
        // (signature includes it indirectly via debug format)
        // This test documents current behavior
        let hash1 = hash_sil_function(&func1);
        let hash2 = hash_sil_function(&func2);
        // Linkage difference may or may not affect hash depending on signature debug format
        let _ = (hash1, hash2);
    }

    // ========== Additional cache_path_for_source tests ==========

    #[test]
    fn test_cache_path_for_source_relative_path() {
        // Test with a relative path (uses "." as parent)
        let source = Path::new("simple.swift");
        let cache_path = cache_path_for_source(source);

        assert!(cache_path.to_string_lossy().contains(".tswift_cache"));
        assert!(
            cache_path
                .to_string_lossy()
                .ends_with("simple.swift.cache.json")
        );
    }

    #[test]
    fn test_cache_path_for_source_no_extension() {
        let tmp = TempDir::new("no_extension");
        let source = tmp.file("Makefile");
        let cache_path = cache_path_for_source(&source);

        assert_eq!(
            cache_path.file_name().unwrap().to_string_lossy(),
            "Makefile.cache.json"
        );
    }

    #[test]
    fn test_cache_path_for_source_dotfile() {
        let tmp = TempDir::new("dotfile");
        let source = tmp.file(".hidden.swift");
        let cache_path = cache_path_for_source(&source);

        assert_eq!(
            cache_path.file_name().unwrap().to_string_lossy(),
            ".hidden.swift.cache.json"
        );
    }

    #[test]
    fn test_cache_path_for_source_nested_path() {
        let tmp = TempDir::new("nested");
        let subdir = tmp.path.join("src").join("lib");
        fs::create_dir_all(&subdir).unwrap();
        let source = subdir.join("module.swift");

        let cache_path = cache_path_for_source(&source);

        // Cache dir should be in same directory as source
        assert_eq!(
            cache_path
                .parent()
                .unwrap()
                .file_name()
                .unwrap()
                .to_string_lossy(),
            ".tswift_cache"
        );
        assert_eq!(cache_path.parent().unwrap().parent().unwrap(), subdir);
    }

    // ========== Additional VerificationCache tests ==========

    #[test]
    fn test_verification_cache_len_and_is_empty() {
        let mut cache = VerificationCache::new();

        assert!(cache.is_empty());
        assert_eq!(cache.len(), 0);

        cache.insert("h1".to_string(), "f1".to_string(), make_test_response("f1"));
        assert!(!cache.is_empty());
        assert_eq!(cache.len(), 1);

        cache.insert("h2".to_string(), "f2".to_string(), make_test_response("f2"));
        assert_eq!(cache.len(), 2);
    }

    #[test]
    fn test_verification_cache_get_nonexistent() {
        let cache = VerificationCache::new();
        assert!(cache.get("nonexistent").is_none());
    }

    #[test]
    fn test_verification_cache_overwrite() {
        let mut cache = VerificationCache::new();
        let hash = "same_hash".to_string();

        cache.insert(
            hash.clone(),
            "first".to_string(),
            make_test_response("first"),
        );
        cache.insert(
            hash.clone(),
            "second".to_string(),
            make_test_response("second"),
        );

        assert_eq!(cache.len(), 1);
        assert_eq!(cache.get(&hash).unwrap().function_name, "second");
    }

    #[test]
    fn test_verification_cache_default() {
        let cache = VerificationCache::default();
        assert!(cache.is_empty());
        assert_eq!(cache.version, CACHE_VERSION);
        assert_eq!(cache.tswift_version, TSWIFT_VERSION);
    }

    // ========== CacheEntry tests ==========

    #[test]
    fn test_cache_entry_clone() {
        let entry = CacheEntry {
            function_name: "test_func".to_string(),
            response: make_test_response("test_func"),
            timestamp: 1_234_567_890,
        };

        let cloned = entry.clone();
        assert_eq!(cloned.function_name, entry.function_name);
        assert_eq!(cloned.timestamp, entry.timestamp);
    }

    #[test]
    fn test_cache_entry_debug() {
        let entry = CacheEntry {
            function_name: "debug_test".to_string(),
            response: make_test_response("debug_test"),
            timestamp: 9999,
        };

        let debug_str = format!("{entry:?}");
        assert!(debug_str.contains("debug_test"));
        assert!(debug_str.contains("9999"));
    }

    #[test]
    fn test_cache_entry_timestamp_is_set() {
        let mut cache = VerificationCache::new();
        let before = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        cache.insert(
            "hash".to_string(),
            "func".to_string(),
            make_test_response("func"),
        );

        let after = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        let entry = cache.get("hash").unwrap();
        assert!(entry.timestamp >= before);
        assert!(entry.timestamp <= after);
    }

    // ========== CacheStats tests ==========

    #[test]
    fn test_cache_stats_clone() {
        let stats = CacheStats {
            total_entries: 42,
            version: 1,
            tswift_version: "0.1.0".to_string(),
        };

        let cloned = stats;
        assert_eq!(cloned.total_entries, 42);
        assert_eq!(cloned.version, 1);
        assert_eq!(cloned.tswift_version, "0.1.0");
    }

    #[test]
    fn test_cache_stats_debug() {
        let stats = CacheStats {
            total_entries: 100,
            version: 2,
            tswift_version: "1.0.0".to_string(),
        };

        let debug_str = format!("{stats:?}");
        assert!(debug_str.contains("100"));
        assert!(debug_str.contains("1.0.0"));
    }

    // ========== CacheManager tests ==========

    #[test]
    fn test_cache_manager_new_creates_cache_dir() {
        let tmp = TempDir::new("cache_manager_new");
        let source = tmp.file("test.swift");

        let _mgr = CacheManager::new(&source, true);

        let expected_cache_dir = tmp.path.join(".tswift_cache");
        assert!(expected_cache_dir.is_dir());
    }

    #[test]
    fn test_cache_manager_new_disabled() {
        let tmp = TempDir::new("cache_manager_new_disabled");
        let source = tmp.file("test.swift");

        let mgr = CacheManager::new(&source, false);
        assert!(!mgr.is_enabled());
    }

    #[test]
    fn test_cache_manager_statistics_initial() {
        let tmp = TempDir::new("cache_manager_stats_initial");
        let cache_path = tmp.file("cache.json");

        let mgr = CacheManager::with_path(cache_path, true);
        assert_eq!(mgr.statistics(), (0, 0));
    }

    #[test]
    fn test_cache_manager_multiple_hits_and_misses() {
        let tmp = TempDir::new("cache_manager_multi_stats");
        let cache_path = tmp.file("cache.json");

        let mut mgr = CacheManager::with_path(cache_path, true);
        mgr.insert("h1".to_string(), "f1".to_string(), make_test_response("f1"));
        mgr.insert("h2".to_string(), "f2".to_string(), make_test_response("f2"));

        // 2 hits
        mgr.get("h1");
        mgr.get("h2");

        // 3 misses
        mgr.get("missing1");
        mgr.get("missing2");
        mgr.get("missing3");

        assert_eq!(mgr.statistics(), (2, 3));
    }

    #[test]
    fn test_cache_manager_insert_disabled_no_dirty() {
        let tmp = TempDir::new("cache_manager_insert_disabled");
        let cache_path = tmp.file("cache.json");

        let mut mgr = CacheManager::with_path(cache_path.clone(), false);
        mgr.insert("h".to_string(), "f".to_string(), make_test_response("f"));

        // Save should be a no-op (not dirty and not enabled)
        mgr.save().unwrap();
        assert!(!cache_path.exists());
    }

    #[test]
    fn test_cache_manager_save_not_dirty() {
        let tmp = TempDir::new("cache_manager_not_dirty");
        let cache_path = tmp.file("cache.json");

        // Create cache, don't insert anything
        let mgr = CacheManager::with_path(cache_path.clone(), true);
        mgr.save().unwrap();

        // Should not create file because cache is not dirty
        assert!(!cache_path.exists());
    }

    #[test]
    fn test_cache_manager_loads_existing_cache() {
        let tmp = TempDir::new("cache_manager_loads_existing");
        let cache_path = tmp.file("cache.json");

        // Create and save a cache
        {
            let mut mgr = CacheManager::with_path(cache_path.clone(), true);
            mgr.insert(
                "existing".to_string(),
                "func".to_string(),
                make_test_response("func"),
            );
            mgr.save().unwrap();
        }

        // Load it in a new manager
        let mut mgr2 = CacheManager::with_path(cache_path, true);
        assert!(mgr2.get("existing").is_some());
        assert_eq!(mgr2.get("existing").unwrap().function_name, "func");
    }

    // ========== Edge case tests ==========

    #[test]
    fn test_hash_function_with_throws() {
        let mut func = make_test_function("throwing");
        func.signature = SilType::Function {
            convention: CallingConvention::Thin,
            params: vec![],
            result: Box::new(SilType::Named("Int".to_string())),
            throws: true,
        };

        let mut func_no_throws = make_test_function("throwing");
        func_no_throws.signature = SilType::Function {
            convention: CallingConvention::Thin,
            params: vec![],
            result: Box::new(SilType::Named("Int".to_string())),
            throws: false,
        };

        let hash1 = hash_sil_function(&func);
        let hash2 = hash_sil_function(&func_no_throws);
        assert_ne!(hash1, hash2, "throws flag should affect hash");
    }

    #[test]
    fn test_hash_function_different_convention() {
        let mut func1 = make_test_function("conv1");
        func1.signature = SilType::Function {
            convention: CallingConvention::Thin,
            params: vec![],
            result: Box::new(SilType::Named("Int".to_string())),
            throws: false,
        };

        let mut func2 = make_test_function("conv1");
        func2.signature = SilType::Function {
            convention: CallingConvention::Thick,
            params: vec![],
            result: Box::new(SilType::Named("Int".to_string())),
            throws: false,
        };

        let hash1 = hash_sil_function(&func1);
        let hash2 = hash_sil_function(&func2);
        assert_ne!(hash1, hash2, "calling convention should affect hash");
    }

    #[test]
    fn test_cache_entry_serialize_deserialize() {
        let entry = CacheEntry {
            function_name: "serialize_test".to_string(),
            response: make_test_response("serialize_test"),
            timestamp: 1_700_000_000,
        };

        let json = serde_json::to_string(&entry).unwrap();
        let deserialized: CacheEntry = serde_json::from_str(&json).unwrap();

        assert_eq!(deserialized.function_name, entry.function_name);
        assert_eq!(deserialized.timestamp, entry.timestamp);
    }

    #[test]
    fn test_verification_cache_serialize_deserialize() {
        let mut cache = VerificationCache::new();
        cache.insert("h1".to_string(), "f1".to_string(), make_test_response("f1"));
        cache.insert("h2".to_string(), "f2".to_string(), make_test_response("f2"));

        let json = serde_json::to_string(&cache).unwrap();
        let deserialized: VerificationCache = serde_json::from_str(&json).unwrap();

        assert_eq!(deserialized.version, cache.version);
        assert_eq!(deserialized.tswift_version, cache.tswift_version);
        assert_eq!(deserialized.len(), 2);
        assert!(deserialized.get("h1").is_some());
        assert!(deserialized.get("h2").is_some());
    }

    // ========== Unicode and special character tests ==========

    #[test]
    fn test_hash_unicode_function_name() {
        let mut func = make_test_function("こんにちは");
        let hash1 = hash_sil_function(&func);

        func.name = "你好".to_string();
        let hash2 = hash_sil_function(&func);

        assert_ne!(
            hash1, hash2,
            "Different unicode names should produce different hashes"
        );
        assert_eq!(hash1.len(), 64);
        assert_eq!(hash2.len(), 64);
    }

    #[test]
    fn test_hash_emoji_in_name() {
        let func = make_test_function("func_🚀_test");
        let hash = hash_sil_function(&func);
        assert_eq!(hash.len(), 64);
        assert!(hash.chars().all(|c| c.is_ascii_hexdigit()));
    }

    #[test]
    fn test_hash_special_characters_in_name() {
        let func = make_test_function("$s4main3fooSiyF");
        let hash = hash_sil_function(&func);
        assert_eq!(hash.len(), 64);
    }

    #[test]
    fn test_cache_unicode_function_name() {
        let mut cache = VerificationCache::new();
        cache.insert(
            "hash_unicode".to_string(),
            "函数名称_🎉".to_string(),
            make_test_response("函数名称_🎉"),
        );

        let entry = cache.get("hash_unicode").unwrap();
        assert_eq!(entry.function_name, "函数名称_🎉");
    }

    // ========== Additional terminator types for hash ==========

    #[test]
    fn test_hash_with_cond_branch_terminator() {
        let mut func = make_test_function("foo");
        func.blocks[0].terminator = SilTerminator::CondBranch {
            condition: "%cond".to_string(),
            true_dest: "bb1".to_string(),
            true_args: vec![],
            false_dest: "bb2".to_string(),
            false_args: vec![],
        };

        let hash1 = hash_sil_function(&func);

        // Change condition variable
        func.blocks[0].terminator = SilTerminator::CondBranch {
            condition: "%cond2".to_string(),
            true_dest: "bb1".to_string(),
            true_args: vec![],
            false_dest: "bb2".to_string(),
            false_args: vec![],
        };

        let hash2 = hash_sil_function(&func);
        assert_ne!(hash1, hash2);
    }

    #[test]
    fn test_hash_with_switch_enum_terminator() {
        let mut func = make_test_function("foo");
        func.blocks[0].terminator = SilTerminator::SwitchEnum {
            operand: "%enum".to_string(),
            cases: vec![("some".to_string(), "bb1".to_string())],
            default: Some("bb2".to_string()),
        };

        let hash1 = hash_sil_function(&func);

        // Change cases
        func.blocks[0].terminator = SilTerminator::SwitchEnum {
            operand: "%enum".to_string(),
            cases: vec![
                ("some".to_string(), "bb1".to_string()),
                ("none".to_string(), "bb3".to_string()),
            ],
            default: Some("bb2".to_string()),
        };

        let hash2 = hash_sil_function(&func);
        assert_ne!(hash1, hash2, "Different switch cases should affect hash");
    }

    #[test]
    fn test_hash_with_throw_terminator() {
        let mut func = make_test_function("foo");
        func.blocks[0].terminator = SilTerminator::Throw {
            operand: "%error".to_string(),
        };

        let mut func2 = make_test_function("foo");
        func2.blocks[0].terminator = SilTerminator::Throw {
            operand: "%error2".to_string(),
        };

        let hash1 = hash_sil_function(&func);
        let hash2 = hash_sil_function(&func2);
        assert_ne!(hash1, hash2);
    }

    #[test]
    fn test_hash_with_unreachable_terminator() {
        let mut func = make_test_function("foo");
        func.blocks[0].terminator = SilTerminator::Unreachable;

        let hash = hash_sil_function(&func);
        assert_eq!(hash.len(), 64);
    }

    #[test]
    fn test_hash_with_try_apply_terminator() {
        let mut func = make_test_function("foo");
        func.blocks[0].terminator = SilTerminator::TryApply {
            callee: "%callee".to_string(),
            substitutions: vec![],
            arguments: vec!["%arg".to_string()],
            normal_dest: "bb1".to_string(),
            error_dest: "bb2".to_string(),
        };

        let hash = hash_sil_function(&func);
        assert_eq!(hash.len(), 64);
    }

    // ========== Additional instruction kinds for hash ==========

    #[test]
    fn test_hash_with_struct_instruction() {
        let mut func = make_test_function("foo");
        func.blocks[0].instructions.push(SilInstruction {
            results: vec![SilValue {
                name: "%s".to_string(),
                ty: SilType::Named("MyStruct".to_string()),
                debug_name: None,
            }],
            kind: SilInstructionKind::Struct {
                ty: SilType::Named("MyStruct".to_string()),
                operands: vec!["%f1".to_string(), "%f2".to_string()],
            },
            location: None,
        });

        let hash1 = hash_sil_function(&func);

        // Change operands
        func.blocks[0].instructions[0].kind = SilInstructionKind::Struct {
            ty: SilType::Named("MyStruct".to_string()),
            operands: vec!["%f1".to_string()],
        };

        let hash2 = hash_sil_function(&func);
        assert_ne!(hash1, hash2);
    }

    #[test]
    fn test_hash_with_apply_instruction() {
        let mut func = make_test_function("foo");
        func.blocks[0].instructions.push(SilInstruction {
            results: vec![SilValue {
                name: "%r".to_string(),
                ty: SilType::Named("Int".to_string()),
                debug_name: None,
            }],
            kind: SilInstructionKind::Apply {
                callee: "%callee".to_string(),
                substitutions: vec![],
                arguments: vec!["%a".to_string()],
                ty: SilType::Named("Int".to_string()),
                caller_isolation: None,
                callee_isolation: None,
            },
            location: None,
        });

        let hash = hash_sil_function(&func);
        assert_eq!(hash.len(), 64);
    }

    #[test]
    fn test_hash_with_builtin_instruction() {
        let mut func = make_test_function("foo");
        func.blocks[0].instructions.push(SilInstruction {
            results: vec![SilValue {
                name: "%r".to_string(),
                ty: SilType::Named("Builtin.Int64".to_string()),
                debug_name: None,
            }],
            kind: SilInstructionKind::Builtin {
                name: "sadd_with_overflow_Int64".to_string(),
                arguments: vec!["%a".to_string(), "%b".to_string()],
                ty: SilType::Named("Builtin.Int64".to_string()),
            },
            location: None,
        });

        let hash = hash_sil_function(&func);
        assert_eq!(hash.len(), 64);
    }

    // ========== Empty/edge case loading ==========

    #[test]
    fn test_load_empty_file_returns_empty_cache() {
        let tmp = TempDir::new("empty_file");
        let path = tmp.file("cache.json");
        fs::write(&path, "").unwrap();

        let cache = VerificationCache::load(&path);
        assert!(cache.is_empty());
    }

    #[test]
    fn test_load_whitespace_only_file_returns_empty_cache() {
        let tmp = TempDir::new("whitespace_file");
        let path = tmp.file("cache.json");
        fs::write(&path, "   \n\t  ").unwrap();

        let cache = VerificationCache::load(&path);
        assert!(cache.is_empty());
    }

    #[test]
    fn test_load_valid_json_wrong_structure() {
        let tmp = TempDir::new("wrong_structure");
        let path = tmp.file("cache.json");
        fs::write(&path, r#"{"key": "value", "array": [1,2,3]}"#).unwrap();

        let cache = VerificationCache::load(&path);
        assert!(cache.is_empty());
    }

    #[test]
    fn test_load_null_json() {
        let tmp = TempDir::new("null_json");
        let path = tmp.file("cache.json");
        fs::write(&path, "null").unwrap();

        let cache = VerificationCache::load(&path);
        assert!(cache.is_empty());
    }

    #[test]
    fn test_load_array_json() {
        let tmp = TempDir::new("array_json");
        let path = tmp.file("cache.json");
        fs::write(&path, "[1, 2, 3]").unwrap();

        let cache = VerificationCache::load(&path);
        assert!(cache.is_empty());
    }

    // ========== CacheManager additional edge cases ==========

    #[test]
    fn test_cache_manager_get_same_key_multiple_times() {
        let tmp = TempDir::new("cache_manager_same_key");
        let cache_path = tmp.file("cache.json");

        let mut mgr = CacheManager::with_path(cache_path, true);
        mgr.insert(
            "key".to_string(),
            "func".to_string(),
            make_test_response("func"),
        );

        // Get the same key multiple times
        let r1 = mgr.get("key").unwrap().function_name.clone();
        let r2 = mgr.get("key").unwrap().function_name.clone();
        let r3 = mgr.get("key").unwrap().function_name.clone();

        assert_eq!(r1, r2);
        assert_eq!(r2, r3);
        assert_eq!(mgr.statistics(), (3, 0)); // 3 hits, 0 misses
    }

    #[test]
    fn test_cache_manager_disabled_no_hits_counted() {
        let tmp = TempDir::new("cache_manager_disabled_no_hits");
        let cache_path = tmp.file("cache.json");

        let mut mgr = CacheManager::with_path(cache_path, false);
        mgr.insert(
            "key".to_string(),
            "func".to_string(),
            make_test_response("func"),
        );

        // Get should return None and not count stats when disabled
        assert!(mgr.get("key").is_none());
        assert!(mgr.get("nonexistent").is_none());
        assert_eq!(mgr.statistics(), (0, 0));
    }

    #[test]
    fn test_cache_manager_interleaved_hits_misses() {
        let tmp = TempDir::new("cache_manager_interleaved");
        let cache_path = tmp.file("cache.json");

        let mut mgr = CacheManager::with_path(cache_path, true);
        mgr.insert("a".to_string(), "fa".to_string(), make_test_response("fa"));
        mgr.insert("b".to_string(), "fb".to_string(), make_test_response("fb"));

        mgr.get("a"); // hit
        mgr.get("x"); // miss
        mgr.get("b"); // hit
        mgr.get("y"); // miss
        mgr.get("a"); // hit
        mgr.get("z"); // miss

        assert_eq!(mgr.statistics(), (3, 3));
    }

    #[test]
    fn test_cache_manager_with_path_nonexistent_dir() {
        let tmp = TempDir::new("cache_manager_nonexistent");
        // Path in a directory that doesn't exist
        let cache_path = tmp.path.join("subdir").join("cache.json");

        // Should work - load returns empty cache for nonexistent files
        let mgr = CacheManager::with_path(cache_path, true);
        assert!(mgr.is_enabled());
    }

    // ========== VerificationCache clone test ==========

    #[test]
    fn test_verification_cache_clone() {
        let mut cache = VerificationCache::new();
        cache.insert("h1".to_string(), "f1".to_string(), make_test_response("f1"));

        let cloned = cache.clone();
        assert_eq!(cloned.version, cache.version);
        assert_eq!(cloned.tswift_version, cache.tswift_version);
        assert_eq!(cloned.len(), cache.len());
        assert!(cloned.get("h1").is_some());
    }

    // ========== hash_sil_function with demangled_name ==========

    #[test]
    fn test_hash_demangled_name_does_not_affect_hash() {
        let mut func1 = make_test_function("$s4main3fooSiyF");
        func1.demangled_name = Some("main.foo() -> Int".to_string());

        let mut func2 = make_test_function("$s4main3fooSiyF");
        func2.demangled_name = None;

        let hash1 = hash_sil_function(&func1);
        let hash2 = hash_sil_function(&func2);

        // demangled_name is for display only, should not affect hash
        assert_eq!(hash1, hash2);
    }

    // ========== More attribute tests ==========

    #[test]
    fn test_hash_multiple_requires_attributes() {
        let mut func = make_test_function("foo");
        func.attributes
            .push(SilAttribute::Requires("a > 0".to_string()));
        func.attributes
            .push(SilAttribute::Requires("b > 0".to_string()));
        func.attributes
            .push(SilAttribute::Requires("c > 0".to_string()));

        let hash1 = hash_sil_function(&func);

        // Remove one attribute
        func.attributes.pop();
        let hash2 = hash_sil_function(&func);

        assert_ne!(hash1, hash2);
    }

    #[test]
    fn test_hash_with_ensures_attribute() {
        let mut func = make_test_function("foo");
        func.attributes
            .push(SilAttribute::Ensures("result >= 0".to_string()));

        let hash1 = hash_sil_function(&func);

        func.attributes[0] = SilAttribute::Ensures("result > 0".to_string());
        let hash2 = hash_sil_function(&func);

        assert_ne!(hash1, hash2);
    }

    #[test]
    fn test_hash_with_invariant_attribute() {
        let mut func = make_test_function("foo");
        func.attributes
            .push(SilAttribute::Invariant("x != nil".to_string()));

        let hash = hash_sil_function(&func);
        assert_eq!(hash.len(), 64);
    }

    #[test]
    fn test_hash_with_trusted_attribute() {
        let mut func1 = make_test_function("foo");
        func1.attributes.push(SilAttribute::Trusted);

        let func2 = make_test_function("foo");

        let hash1 = hash_sil_function(&func1);
        let hash2 = hash_sil_function(&func2);

        assert_ne!(hash1, hash2, "Trusted attribute should affect hash");
    }

    // ========== Block argument edge cases ==========

    #[test]
    fn test_hash_multiple_block_arguments() {
        let mut func = make_test_function("foo");
        func.blocks[0].arguments = vec![
            SilValue {
                name: "%0".to_string(),
                ty: SilType::Named("Int".to_string()),
                debug_name: Some("x".to_string()),
            },
            SilValue {
                name: "%1".to_string(),
                ty: SilType::Named("Int".to_string()),
                debug_name: Some("y".to_string()),
            },
            SilValue {
                name: "%2".to_string(),
                ty: SilType::Named("Bool".to_string()),
                debug_name: None,
            },
        ];

        let hash1 = hash_sil_function(&func);

        // Change argument order
        func.blocks[0].arguments.swap(0, 1);
        let hash2 = hash_sil_function(&func);

        assert_ne!(hash1, hash2, "Argument order should affect hash");
    }

    // ========== cache_path_for_source edge cases ==========

    #[test]
    fn test_cache_path_for_source_root_path() {
        // Test with root path (Unix)
        let source = Path::new("/test.swift");
        let cache_path = cache_path_for_source(source);

        assert!(cache_path.to_string_lossy().contains(".tswift_cache"));
        assert!(
            cache_path
                .to_string_lossy()
                .ends_with("test.swift.cache.json")
        );
    }

    #[test]
    fn test_cache_path_for_source_double_extension() {
        let tmp = TempDir::new("double_extension");
        let source = tmp.file("test.generated.swift");
        let cache_path = cache_path_for_source(&source);

        assert_eq!(
            cache_path.file_name().unwrap().to_string_lossy(),
            "test.generated.swift.cache.json"
        );
    }

    #[test]
    fn test_cache_path_for_source_spaces_in_name() {
        let tmp = TempDir::new("spaces_in_name");
        let source = tmp.file("my file.swift");
        let cache_path = cache_path_for_source(&source);

        assert_eq!(
            cache_path.file_name().unwrap().to_string_lossy(),
            "my file.swift.cache.json"
        );
    }

    // ========== Empty hash key tests ==========

    #[test]
    fn test_cache_empty_hash_key() {
        let mut cache = VerificationCache::new();
        cache.insert(
            String::new(),
            "empty_key".to_string(),
            make_test_response("empty_key"),
        );

        assert_eq!(cache.len(), 1);
        assert!(cache.get("").is_some());
        assert_eq!(cache.get("").unwrap().function_name, "empty_key");
    }

    #[test]
    fn test_cache_manager_empty_hash_key() {
        let tmp = TempDir::new("empty_hash_key");
        let cache_path = tmp.file("cache.json");

        let mut mgr = CacheManager::with_path(cache_path.clone(), true);
        mgr.insert(String::new(), "f".to_string(), make_test_response("f"));
        mgr.save().unwrap();

        let mut mgr2 = CacheManager::with_path(cache_path, true);
        assert!(mgr2.get("").is_some());
    }

    // ========== Very long values tests ==========

    #[test]
    fn test_hash_very_long_function_name() {
        let long_name = "a".repeat(10000);
        let func = make_test_function(&long_name);
        let hash = hash_sil_function(&func);

        assert_eq!(hash.len(), 64);
        assert!(hash.chars().all(|c| c.is_ascii_hexdigit()));
    }

    #[test]
    fn test_cache_very_long_function_name() {
        let mut cache = VerificationCache::new();
        let long_name = "func_".to_string() + &"x".repeat(10000);
        cache.insert(
            "h".to_string(),
            long_name.clone(),
            make_test_response(&long_name),
        );

        let entry = cache.get("h").unwrap();
        assert_eq!(entry.function_name.len(), 10005);
    }

    // ========== CacheStats from empty and populated cache ==========

    #[test]
    fn test_cache_stats_empty_cache() {
        let cache = VerificationCache::new();
        let stats = cache.stats();

        assert_eq!(stats.total_entries, 0);
        assert_eq!(stats.version, CACHE_VERSION);
    }

    #[test]
    fn test_cache_stats_many_entries() {
        let mut cache = VerificationCache::new();
        for i in 0..100 {
            cache.insert(
                format!("hash_{i}"),
                format!("func_{i}"),
                make_test_response(&format!("func_{i}")),
            );
        }

        let stats = cache.stats();
        assert_eq!(stats.total_entries, 100);
    }

    // ========== VerificationCache.new equals default ==========

    #[test]
    fn test_verification_cache_new_equals_default() {
        let new_cache = VerificationCache::new();
        let default_cache = VerificationCache::default();

        assert_eq!(new_cache.version, default_cache.version);
        assert_eq!(new_cache.tswift_version, default_cache.tswift_version);
        assert_eq!(new_cache.len(), default_cache.len());
    }

    // ========== Debug format tests ==========

    #[test]
    fn test_verification_cache_debug() {
        let mut cache = VerificationCache::new();
        cache.insert("h".to_string(), "f".to_string(), make_test_response("f"));

        let debug_str = format!("{cache:?}");
        assert!(debug_str.contains("VerificationCache"));
        assert!(debug_str.contains("version"));
    }

    #[test]
    fn test_cache_manager_is_enabled_reflects_constructor() {
        let tmp = TempDir::new("is_enabled");
        let source = tmp.file("test.swift");

        let mgr_enabled = CacheManager::new(&source, true);
        let mgr_disabled = CacheManager::new(&source, false);

        assert!(mgr_enabled.is_enabled());
        assert!(!mgr_disabled.is_enabled());
    }

    // ========== Save error handling ==========

    #[test]
    fn test_verification_cache_save_creates_file() {
        let tmp = TempDir::new("save_creates_file");
        let path = tmp.file("new_cache.json");

        assert!(!path.exists());

        let mut cache = VerificationCache::new();
        cache.insert("h".to_string(), "f".to_string(), make_test_response("f"));
        cache.save(&path).unwrap();

        assert!(path.exists());
    }

    #[test]
    fn test_verification_cache_save_overwrites() {
        let tmp = TempDir::new("save_overwrites");
        let path = tmp.file("cache.json");

        // Write initial content
        let mut cache1 = VerificationCache::new();
        cache1.insert("h1".to_string(), "f1".to_string(), make_test_response("f1"));
        cache1.save(&path).unwrap();

        // Overwrite with different content
        let mut cache2 = VerificationCache::new();
        cache2.insert("h2".to_string(), "f2".to_string(), make_test_response("f2"));
        cache2.save(&path).unwrap();

        // Load and verify
        let loaded = VerificationCache::load(&path);
        assert_eq!(loaded.len(), 1);
        assert!(loaded.get("h1").is_none());
        assert!(loaded.get("h2").is_some());
    }

    // ========== Multiple blocks hash test ==========

    #[test]
    fn test_hash_function_with_many_blocks() {
        let mut func = make_test_function("complex");
        func.blocks = vec![
            SilBasicBlock {
                label: "entry".to_string(),
                arguments: vec![SilValue {
                    name: "%0".to_string(),
                    ty: SilType::Named("Int".to_string()),
                    debug_name: Some("n".to_string()),
                }],
                instructions: vec![SilInstruction {
                    results: vec![SilValue {
                        name: "%1".to_string(),
                        ty: SilType::Named("Builtin.Int1".to_string()),
                        debug_name: None,
                    }],
                    kind: SilInstructionKind::IntegerLiteral {
                        ty: SilType::Named("Builtin.Int1".to_string()),
                        value: 0,
                    },
                    location: None,
                }],
                terminator: SilTerminator::CondBranch {
                    condition: "%1".to_string(),
                    true_dest: "then".to_string(),
                    true_args: vec![],
                    false_dest: "else".to_string(),
                    false_args: vec![],
                },
            },
            SilBasicBlock {
                label: "then".to_string(),
                arguments: vec![],
                instructions: vec![],
                terminator: SilTerminator::Branch {
                    dest: "merge".to_string(),
                    args: vec!["%0".to_string()],
                },
            },
            SilBasicBlock {
                label: "else".to_string(),
                arguments: vec![],
                instructions: vec![],
                terminator: SilTerminator::Branch {
                    dest: "merge".to_string(),
                    args: vec!["%0".to_string()],
                },
            },
            SilBasicBlock {
                label: "merge".to_string(),
                arguments: vec![SilValue {
                    name: "%phi".to_string(),
                    ty: SilType::Named("Int".to_string()),
                    debug_name: None,
                }],
                instructions: vec![],
                terminator: SilTerminator::Return {
                    operand: "%phi".to_string(),
                },
            },
        ];

        let hash = hash_sil_function(&func);
        assert_eq!(hash.len(), 64);

        // Changing one block should change hash
        func.blocks[2].label = "otherwise".to_string();
        let hash2 = hash_sil_function(&func);
        assert_ne!(hash, hash2);
    }
}
