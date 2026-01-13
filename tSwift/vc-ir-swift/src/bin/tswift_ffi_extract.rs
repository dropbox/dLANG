//! tswift-ffi-extract CLI: Extract `_ffi_*` annotated declarations from Swift source.
//!
//! Output is JSON Lines (one `SwiftFfiDeclaration` per line).
//!
//! Usage:
//!   tswift-ffi-extract <file.swift> [file2.swift ...]
//!   tswift-ffi-extract --pretty <file.swift>
//!   tswift-ffi-extract --help

use std::env;
use std::fs;
use std::process::ExitCode;

use vc_ir_swift::{SwiftFfiDeclaration, parse_swift_ffi_declarations_from_source};

fn main() -> ExitCode {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 || args.iter().any(|a| a == "--help" || a == "-h") {
        print_help();
        return ExitCode::SUCCESS;
    }

    let pretty = args.iter().any(|a| a == "--pretty");
    let paths: Vec<&str> = args
        .iter()
        .skip(1)
        .filter(|a| !a.starts_with('-'))
        .map(String::as_str)
        .collect();

    if paths.is_empty() {
        eprintln!("error: no input files");
        return ExitCode::from(2);
    }

    for path in paths {
        let content = match fs::read_to_string(path) {
            Ok(c) => c,
            Err(e) => {
                eprintln!("error reading '{path}': {e}");
                return ExitCode::from(2);
            }
        };

        let decls = parse_swift_ffi_declarations_from_source(&content, path);
        for decl in decls {
            if let Err(e) = print_decl(&decl, pretty) {
                eprintln!("error serializing '{path}': {e}");
                return ExitCode::from(2);
            }
        }
    }

    ExitCode::SUCCESS
}

fn print_help() {
    println!(
        r"tswift-ffi-extract - Extract `_ffi_*` annotated declarations from Swift source

USAGE:
    tswift-ffi-extract [OPTIONS] <FILE>...

OPTIONS:
    --pretty    Pretty-print JSON output
    -h, --help  Show this help message

OUTPUT:
    JSON Lines: one SwiftFfiDeclaration per line"
    );
}

fn print_decl(decl: &SwiftFfiDeclaration, pretty: bool) -> Result<(), serde_json::Error> {
    if pretty {
        println!("{}", serde_json::to_string_pretty(decl)?);
    } else {
        println!("{}", serde_json::to_string(decl)?);
    }
    Ok(())
}

// Helper functions used only in tests
#[cfg(test)]
mod helpers {
    use super::*;

    /// Serialize a declaration to JSON string (for testing)
    pub fn decl_to_json(
        decl: &SwiftFfiDeclaration,
        pretty: bool,
    ) -> Result<String, serde_json::Error> {
        if pretty {
            serde_json::to_string_pretty(decl)
        } else {
            serde_json::to_string(decl)
        }
    }

    /// Check if arguments indicate help mode
    pub fn is_help_requested(args: &[String]) -> bool {
        args.len() < 2 || args.iter().any(|a| a == "--help" || a == "-h")
    }

    /// Check if pretty mode is requested
    pub fn is_pretty_mode(args: &[String]) -> bool {
        args.iter().any(|a| a == "--pretty")
    }

    /// Extract file paths from arguments
    pub fn extract_paths(args: &[String]) -> Vec<&str> {
        args.iter()
            .skip(1)
            .filter(|a| !a.starts_with('-'))
            .map(String::as_str)
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::helpers::*;
    use super::*;

    // ============================================================
    // is_help_requested tests
    // ============================================================

    #[test]
    fn test_is_help_requested_no_args() {
        let args = vec!["tswift-ffi-extract".to_string()];
        assert!(is_help_requested(&args));
    }

    #[test]
    fn test_is_help_requested_with_help_flag() {
        let args = vec!["tswift-ffi-extract".to_string(), "--help".to_string()];
        assert!(is_help_requested(&args));
    }

    #[test]
    fn test_is_help_requested_with_h_flag() {
        let args = vec!["tswift-ffi-extract".to_string(), "-h".to_string()];
        assert!(is_help_requested(&args));
    }

    #[test]
    fn test_is_help_requested_with_file() {
        let args = vec!["tswift-ffi-extract".to_string(), "file.swift".to_string()];
        assert!(!is_help_requested(&args));
    }

    #[test]
    fn test_is_help_requested_help_with_files() {
        let args = vec![
            "tswift-ffi-extract".to_string(),
            "file.swift".to_string(),
            "--help".to_string(),
        ];
        assert!(is_help_requested(&args));
    }

    // ============================================================
    // is_pretty_mode tests
    // ============================================================

    #[test]
    fn test_is_pretty_mode_false() {
        let args = vec!["tswift-ffi-extract".to_string(), "file.swift".to_string()];
        assert!(!is_pretty_mode(&args));
    }

    #[test]
    fn test_is_pretty_mode_true() {
        let args = vec![
            "tswift-ffi-extract".to_string(),
            "--pretty".to_string(),
            "file.swift".to_string(),
        ];
        assert!(is_pretty_mode(&args));
    }

    #[test]
    fn test_is_pretty_mode_at_end() {
        let args = vec![
            "tswift-ffi-extract".to_string(),
            "file.swift".to_string(),
            "--pretty".to_string(),
        ];
        assert!(is_pretty_mode(&args));
    }

    // ============================================================
    // extract_paths tests
    // ============================================================

    #[test]
    fn test_extract_paths_single_file() {
        let args = vec!["tswift-ffi-extract".to_string(), "file.swift".to_string()];
        let paths = extract_paths(&args);
        assert_eq!(paths, vec!["file.swift"]);
    }

    #[test]
    fn test_extract_paths_multiple_files() {
        let args = vec![
            "tswift-ffi-extract".to_string(),
            "a.swift".to_string(),
            "b.swift".to_string(),
            "c.swift".to_string(),
        ];
        let paths = extract_paths(&args);
        assert_eq!(paths, vec!["a.swift", "b.swift", "c.swift"]);
    }

    #[test]
    fn test_extract_paths_with_flags() {
        let args = vec![
            "tswift-ffi-extract".to_string(),
            "--pretty".to_string(),
            "file.swift".to_string(),
        ];
        let paths = extract_paths(&args);
        assert_eq!(paths, vec!["file.swift"]);
    }

    #[test]
    fn test_extract_paths_flags_only() {
        let args = vec![
            "tswift-ffi-extract".to_string(),
            "--pretty".to_string(),
            "--help".to_string(),
        ];
        let paths = extract_paths(&args);
        assert!(paths.is_empty());
    }

    #[test]
    fn test_extract_paths_empty() {
        let args = vec!["tswift-ffi-extract".to_string()];
        let paths = extract_paths(&args);
        assert!(paths.is_empty());
    }

    // ============================================================
    // decl_to_json tests
    // ============================================================

    #[test]
    fn test_decl_to_json_compact() {
        let decl = SwiftFfiDeclaration {
            swift_name: "testFunc".to_string(),
            parameters: vec![],
            return_type: "Void".to_string(),
            source_file: "test.swift".to_string(),
            source_line: 1,
            attributes: vec![],
        };
        let json = decl_to_json(&decl, false).unwrap();
        assert!(json.contains("\"swift_name\":\"testFunc\""));
        assert!(!json.contains('\n'));
    }

    #[test]
    fn test_decl_to_json_pretty() {
        let decl = SwiftFfiDeclaration {
            swift_name: "testFunc".to_string(),
            parameters: vec![],
            return_type: "Void".to_string(),
            source_file: "test.swift".to_string(),
            source_line: 1,
            attributes: vec![],
        };
        let json = decl_to_json(&decl, true).unwrap();
        assert!(json.contains("\"swift_name\": \"testFunc\""));
        assert!(json.contains('\n'));
    }

    #[test]
    fn test_decl_to_json_with_params() {
        let decl = SwiftFfiDeclaration {
            swift_name: "add".to_string(),
            parameters: vec![
                ("a".to_string(), "Int".to_string()),
                ("b".to_string(), "Int".to_string()),
            ],
            return_type: "Int".to_string(),
            source_file: "math.swift".to_string(),
            source_line: 10,
            attributes: vec![],
        };
        let json = decl_to_json(&decl, false).unwrap();
        assert!(json.contains("\"parameters\":"));
        assert!(json.contains("\"a\""));
        assert!(json.contains("\"b\""));
    }

    #[test]
    fn test_decl_to_json_with_attributes() {
        use vc_ir_swift::SwiftFfiAttribute;
        let decl = SwiftFfiDeclaration {
            swift_name: "safeAdd".to_string(),
            parameters: vec![("x".to_string(), "Int".to_string())],
            return_type: "Int".to_string(),
            source_file: "safe.swift".to_string(),
            source_line: 5,
            attributes: vec![SwiftFfiAttribute::Requires {
                condition: "x > 0".to_string(),
            }],
        };
        let json = decl_to_json(&decl, false).unwrap();
        assert!(json.contains("attributes"));
        assert!(json.contains("x > 0"));
    }

    #[test]
    fn test_decl_to_json_empty_return() {
        let decl = SwiftFfiDeclaration {
            swift_name: "doNothing".to_string(),
            parameters: vec![],
            return_type: "()".to_string(),
            source_file: "test.swift".to_string(),
            source_line: 1,
            attributes: vec![],
        };
        let json = decl_to_json(&decl, false).unwrap();
        assert!(json.contains("\"return_type\":\"()\""));
    }

    #[test]
    fn test_decl_to_json_special_chars_in_name() {
        let decl = SwiftFfiDeclaration {
            swift_name: "test_func_123".to_string(),
            parameters: vec![],
            return_type: "Void".to_string(),
            source_file: "test.swift".to_string(),
            source_line: 1,
            attributes: vec![],
        };
        let json = decl_to_json(&decl, false).unwrap();
        assert!(json.contains("test_func_123"));
    }

    // ============================================================
    // Integration tests for argument parsing
    // ============================================================

    #[test]
    fn test_help_and_files_together() {
        let args = vec![
            "tswift-ffi-extract".to_string(),
            "file1.swift".to_string(),
            "file2.swift".to_string(),
            "-h".to_string(),
        ];
        // Help flag takes precedence
        assert!(is_help_requested(&args));
        // But paths can still be extracted
        let paths = extract_paths(&args);
        assert_eq!(paths.len(), 2);
    }

    #[test]
    fn test_pretty_and_multiple_files() {
        let args = vec![
            "tswift-ffi-extract".to_string(),
            "--pretty".to_string(),
            "a.swift".to_string(),
            "b.swift".to_string(),
        ];
        assert!(is_pretty_mode(&args));
        let paths = extract_paths(&args);
        assert_eq!(paths, vec!["a.swift", "b.swift"]);
    }
}
