//! PathBuf/Path integration test (Phase 10.1)
//! Tests PathBuf and Path contracts.
//!
//! PathBuf is an owned mutable path, Path is a borrowed path slice.
//! Key provable properties:
//! - PathBuf::capacity() returns >= 0 (usize is unsigned)
//!
//! Most Path/PathBuf operations are string-based and runtime-dependent,
//! so they are documented contracts without strong postconditions.

use std::path::{Path, PathBuf};

// Test 1: PathBuf::new creates empty path
fn test_pathbuf_new() -> PathBuf {
    PathBuf::new()
}

// Test 2: PathBuf::with_capacity creates path with preallocated buffer
fn test_pathbuf_with_capacity(capacity: usize) -> PathBuf {
    PathBuf::with_capacity(capacity)
}

// Test 3: PathBuf::capacity returns non-negative value
#[ensures("result >= 0")]
fn test_pathbuf_capacity(path: &PathBuf) -> usize {
    path.capacity()
}

// Test 4: Path::new creates path reference
fn test_path_new<'a>(s: &'a str) -> &'a Path {
    Path::new(s)
}

// Test 5: Path::is_absolute check
fn test_path_is_absolute(path: &Path) -> bool {
    path.is_absolute()
}

// Test 6: Path::is_relative check (complement of is_absolute)
fn test_path_is_relative(path: &Path) -> bool {
    path.is_relative()
}

// Test 7: Path::has_root check
fn test_path_has_root(path: &Path) -> bool {
    path.has_root()
}

// Test 8: Path::parent returns Option<&Path>
fn test_path_parent<'a>(path: &'a Path) -> Option<&'a Path> {
    path.parent()
}

// Test 9: Path::file_name returns Option<&OsStr>
fn test_path_file_name(path: &Path) -> Option<&std::ffi::OsStr> {
    path.file_name()
}

// Test 10: Path::extension returns Option<&OsStr>
fn test_path_extension(path: &Path) -> Option<&std::ffi::OsStr> {
    path.extension()
}

// Test 11: Path::file_stem returns Option<&OsStr>
fn test_path_file_stem(path: &Path) -> Option<&std::ffi::OsStr> {
    path.file_stem()
}

// Test 12: Path::join creates new PathBuf
fn test_path_join(path: &Path, other: &Path) -> PathBuf {
    path.join(other)
}

// Test 13: PathBuf::push appends component
fn test_pathbuf_push(path: &mut PathBuf, component: &Path) {
    path.push(component);
}

fn main() {
    // Test PathBuf creation
    let empty_path = test_pathbuf_new();
    println!("Empty PathBuf: {:?}", empty_path);

    let preallocated = test_pathbuf_with_capacity(100);
    println!("Preallocated PathBuf capacity: {}", test_pathbuf_capacity(&preallocated));

    // Test Path operations
    let absolute_path = Path::new("/usr/bin");
    let relative_path = Path::new("src/main.rs");

    println!("Path /usr/bin:");
    println!("  is_absolute: {}", test_path_is_absolute(absolute_path));
    println!("  is_relative: {}", test_path_is_relative(absolute_path));
    println!("  has_root: {}", test_path_has_root(absolute_path));

    println!("Path src/main.rs:");
    println!("  is_absolute: {}", test_path_is_absolute(relative_path));
    println!("  is_relative: {}", test_path_is_relative(relative_path));
    println!("  has_root: {}", test_path_has_root(relative_path));

    // Test parent
    let path_with_parent = Path::new("/home/user/file.txt");
    if let Some(parent) = test_path_parent(path_with_parent) {
        println!("Parent of /home/user/file.txt: {:?}", parent);
    }

    // Test file_name and extension
    let file_path = Path::new("document.pdf");
    if let Some(name) = test_path_file_name(file_path) {
        println!("File name of document.pdf: {:?}", name);
    }
    if let Some(ext) = test_path_extension(file_path) {
        println!("Extension of document.pdf: {:?}", ext);
    }
    if let Some(stem) = test_path_file_stem(file_path) {
        println!("File stem of document.pdf: {:?}", stem);
    }

    // Test join
    let base = Path::new("/home/user");
    let file = Path::new("document.txt");
    let joined = test_path_join(base, file);
    println!("Joined path: {:?}", joined);

    // Test push
    let mut mutable_path = PathBuf::from("/home");
    test_pathbuf_push(&mut mutable_path, Path::new("user"));
    println!("After push: {:?}", mutable_path);

    println!("All path tests completed!");
}
