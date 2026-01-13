//! ACSL specification parsing
//!
//! Parses ACSL (ANSI/ISO C Specification Language) comments from C files.
//! ACSL is the specification language used by Frama-C.
//!
//! # ACSL Syntax
//!
//! ```c
//! /*@ requires x > 0;
//!     ensures \result == x * 2;
//! */
//! int double_it(int x) { return x + x; }
//! ```

use crate::error::{TcError, TcResult};
use std::path::Path;

/// Specification for a function
#[derive(Debug, Clone)]
pub struct FunctionSpec {
    /// Function name
    pub name: String,
    /// Preconditions (requires clauses)
    pub requires: Vec<String>,
    /// Postconditions (ensures clauses)
    pub ensures: Vec<String>,
    /// Loop invariants
    pub loop_invariants: Vec<String>,
    /// Assigns clauses (modified locations)
    pub assigns: Vec<String>,
    /// Decreases clause (for termination)
    pub decreases: Option<String>,
    /// Source location
    pub location: AcslLocation,
}

/// Source location for ACSL spec
#[derive(Debug, Clone, Default)]
pub struct AcslLocation {
    pub file: String,
    pub line: u32,
}

impl FunctionSpec {
    /// Create a new empty function spec
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            requires: vec![],
            ensures: vec![],
            loop_invariants: vec![],
            assigns: vec![],
            decreases: None,
            location: AcslLocation::default(),
        }
    }
}

/// Extract ACSL specifications from a C file
///
/// Scans the file for ACSL comments (/*@ ... */) and parses them.
///
/// # Arguments
///
/// * `path` - Path to the C file
///
/// # Returns
///
/// List of function specifications
pub fn extract_specs(path: &Path) -> TcResult<Vec<FunctionSpec>> {
    if !path.exists() {
        return Err(TcError::FileNotFound(path.display().to_string()));
    }

    let content = std::fs::read_to_string(path)?;

    // TODO: Implement actual ACSL parsing
    // For now, do a simple scan for ACSL comment markers
    //
    // Real implementation would:
    // 1. Scan for /*@ ... */ comments
    // 2. Parse ACSL syntax (requires, ensures, etc.)
    // 3. Associate specs with following function declarations

    tracing::info!("Extracting ACSL specs from: {}", path.display());

    let mut specs = vec![];
    let mut in_acsl = false;
    let mut current_spec = String::new();
    let mut spec_line = 0u32;
    let file_str = path.display().to_string();

    for (line_num, line) in content.lines().enumerate() {
        let line_num = (line_num + 1) as u32;

        if line.contains("/*@") {
            in_acsl = true;
            spec_line = line_num;
            current_spec.clear();
            // Get content after /*@
            if let Some(idx) = line.find("/*@") {
                current_spec.push_str(&line[idx + 3..]);
            }
        } else if in_acsl {
            if line.contains("*/") {
                in_acsl = false;
                // Get content before */
                if let Some(idx) = line.find("*/") {
                    current_spec.push_str(&line[..idx]);
                }

                // Parse the collected ACSL spec
                if let Some(spec) = parse_acsl_comment(&current_spec, &file_str, spec_line) {
                    specs.push(spec);
                }
            } else {
                current_spec.push('\n');
                current_spec.push_str(line.trim());
            }
        }
    }

    Ok(specs)
}

/// Parse an ACSL comment into a FunctionSpec
fn parse_acsl_comment(content: &str, file: &str, line: u32) -> Option<FunctionSpec> {
    let mut spec = FunctionSpec::new("unknown");
    spec.location = AcslLocation {
        file: file.to_string(),
        line,
    };

    // Simple parsing: look for requires and ensures
    for part in content.split(';') {
        let part = part.trim();
        if part.starts_with("requires") {
            let clause = part.strip_prefix("requires").unwrap().trim();
            spec.requires.push(clause.to_string());
        } else if part.starts_with("ensures") {
            let clause = part.strip_prefix("ensures").unwrap().trim();
            spec.ensures.push(clause.to_string());
        } else if part.starts_with("assigns") {
            let clause = part.strip_prefix("assigns").unwrap().trim();
            spec.assigns.push(clause.to_string());
        } else if part.starts_with("decreases") {
            let clause = part.strip_prefix("decreases").unwrap().trim();
            spec.decreases = Some(clause.to_string());
        } else if part.starts_with("loop invariant") {
            let clause = part.strip_prefix("loop invariant").unwrap().trim();
            spec.loop_invariants.push(clause.to_string());
        }
    }

    // Only return if we found something
    if spec.requires.is_empty() && spec.ensures.is_empty() {
        None
    } else {
        Some(spec)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;
    use tempfile::NamedTempFile;

    #[test]
    fn test_extract_specs_simple() {
        let mut file = NamedTempFile::new().unwrap();
        writeln!(file, "/*@ requires x > 0;").unwrap();
        writeln!(file, "    ensures \\result == x * 2;").unwrap();
        writeln!(file, "*/").unwrap();
        writeln!(file, "int double_it(int x) {{ return x + x; }}").unwrap();

        let specs = extract_specs(file.path()).unwrap();
        assert_eq!(specs.len(), 1);
        assert_eq!(specs[0].requires.len(), 1);
        assert_eq!(specs[0].ensures.len(), 1);
        assert!(specs[0].requires[0].contains("x > 0"));
    }

    #[test]
    fn test_extract_specs_empty_file() {
        let mut file = NamedTempFile::new().unwrap();
        writeln!(file, "int main() {{ return 0; }}").unwrap();

        let specs = extract_specs(file.path()).unwrap();
        assert!(specs.is_empty());
    }

    #[test]
    fn test_parse_acsl_comment() {
        let spec = parse_acsl_comment(
            "requires x > 0; ensures \\result >= 0",
            "test.c",
            1,
        )
        .unwrap();

        assert_eq!(spec.requires.len(), 1);
        assert_eq!(spec.ensures.len(), 1);
    }
}
