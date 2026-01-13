//! Error types for the VC IR Swift bridge.

use thiserror::Error;

/// Errors that can occur when processing Swift verification conditions.
#[derive(Debug, Error)]
pub enum VcBridgeError {
    /// Failed to parse JSON input
    #[error("JSON parse error: {0}")]
    JsonParse(#[from] serde_json::Error),

    /// Invalid expression kind in JSON
    #[error("Invalid expression kind: {0}")]
    InvalidExprKind(String),

    /// Missing required field in JSON
    #[error("Missing required field: {0}")]
    MissingField(String),

    /// Invalid type specification
    #[error("Invalid type: {0}")]
    InvalidType(String),

    /// Invalid auto-VC kind
    #[error("Invalid auto-VC kind: {0}")]
    InvalidAutoVcKind(String),

    /// Conversion error
    #[error("Conversion error: {0}")]
    Conversion(String),

    /// Verification backend error
    #[error("Backend error: {0}")]
    Backend(String),
}

/// Result type alias for VC bridge operations.
pub type VcBridgeResult<T> = Result<T, VcBridgeError>;

#[cfg(test)]
mod tests {
    use super::*;

    // ==========================================================================
    // Error variant creation tests
    // ==========================================================================

    #[test]
    fn test_invalid_expr_kind_creation() {
        let err = VcBridgeError::InvalidExprKind("unknown_kind".to_string());
        assert!(matches!(err, VcBridgeError::InvalidExprKind(_)));
    }

    #[test]
    fn test_missing_field_creation() {
        let err = VcBridgeError::MissingField("required_field".to_string());
        assert!(matches!(err, VcBridgeError::MissingField(_)));
    }

    #[test]
    fn test_invalid_type_creation() {
        let err = VcBridgeError::InvalidType("BadType".to_string());
        assert!(matches!(err, VcBridgeError::InvalidType(_)));
    }

    #[test]
    fn test_invalid_auto_vc_kind_creation() {
        let err = VcBridgeError::InvalidAutoVcKind("unknown_vc".to_string());
        assert!(matches!(err, VcBridgeError::InvalidAutoVcKind(_)));
    }

    #[test]
    fn test_conversion_error_creation() {
        let err = VcBridgeError::Conversion("conversion failed".to_string());
        assert!(matches!(err, VcBridgeError::Conversion(_)));
    }

    #[test]
    fn test_backend_error_creation() {
        let err = VcBridgeError::Backend("solver timeout".to_string());
        assert!(matches!(err, VcBridgeError::Backend(_)));
    }

    // ==========================================================================
    // Display trait (error message) tests
    // ==========================================================================

    #[test]
    fn test_invalid_expr_kind_display() {
        let err = VcBridgeError::InvalidExprKind("weird_expr".to_string());
        let msg = format!("{err}");
        assert_eq!(msg, "Invalid expression kind: weird_expr");
    }

    #[test]
    fn test_missing_field_display() {
        let err = VcBridgeError::MissingField("function_name".to_string());
        let msg = format!("{err}");
        assert_eq!(msg, "Missing required field: function_name");
    }

    #[test]
    fn test_invalid_type_display() {
        let err = VcBridgeError::InvalidType("Float128".to_string());
        let msg = format!("{err}");
        assert_eq!(msg, "Invalid type: Float128");
    }

    #[test]
    fn test_invalid_auto_vc_kind_display() {
        let err = VcBridgeError::InvalidAutoVcKind("NonExistent".to_string());
        let msg = format!("{err}");
        assert_eq!(msg, "Invalid auto-VC kind: NonExistent");
    }

    #[test]
    fn test_conversion_error_display() {
        let err = VcBridgeError::Conversion("SIL translation failed".to_string());
        let msg = format!("{err}");
        assert_eq!(msg, "Conversion error: SIL translation failed");
    }

    #[test]
    fn test_backend_error_display() {
        let err = VcBridgeError::Backend("Z4 returned unknown".to_string());
        let msg = format!("{err}");
        assert_eq!(msg, "Backend error: Z4 returned unknown");
    }

    // ==========================================================================
    // From<serde_json::Error> conversion test
    // ==========================================================================

    #[test]
    fn test_json_parse_from_conversion() {
        // Create an invalid JSON to get a serde_json::Error
        let invalid_json = r#"{ "broken": "#;
        let json_err: serde_json::Error =
            serde_json::from_str::<serde_json::Value>(invalid_json).unwrap_err();

        let vc_err: VcBridgeError = json_err.into();
        assert!(matches!(vc_err, VcBridgeError::JsonParse(_)));
    }

    #[test]
    fn test_json_parse_display() {
        let invalid_json = r#"{ "broken": "#;
        let json_err = serde_json::from_str::<serde_json::Value>(invalid_json).unwrap_err();
        let vc_err: VcBridgeError = json_err.into();

        let msg = format!("{vc_err}");
        assert!(msg.starts_with("JSON parse error:"));
    }

    // ==========================================================================
    // VcBridgeResult type alias tests
    // ==========================================================================

    #[test]
    fn test_vc_bridge_result_ok() {
        let result: VcBridgeResult<i32> = Ok(42);
        assert!(result.is_ok_and(|value| value == 42));
    }

    #[test]
    fn test_vc_bridge_result_err() {
        fn returns_err() -> VcBridgeResult<i32> {
            Err(VcBridgeError::Backend("test error".to_string()))
        }
        let result = returns_err();
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), VcBridgeError::Backend(_)));
    }

    #[test]
    fn test_vc_bridge_result_question_mark_operator() {
        fn inner() -> VcBridgeResult<i32> {
            Err(VcBridgeError::Conversion("inner error".to_string()))
        }

        fn outer() -> VcBridgeResult<i32> {
            let _ = inner()?;
            Ok(0)
        }

        let result = outer();
        assert!(result.is_err());
    }

    // ==========================================================================
    // Debug trait tests
    // ==========================================================================

    #[test]
    fn test_error_debug_format() {
        let err = VcBridgeError::InvalidExprKind("test".to_string());
        let debug_str = format!("{err:?}");
        assert!(debug_str.contains("InvalidExprKind"));
        assert!(debug_str.contains("test"));
    }

    // ==========================================================================
    // Error trait source() tests
    // ==========================================================================

    #[test]
    fn test_json_parse_error_has_source() {
        use std::error::Error;

        let invalid_json = r#"{ "broken": "#;
        let json_err = serde_json::from_str::<serde_json::Value>(invalid_json).unwrap_err();
        let vc_err: VcBridgeError = json_err.into();

        // JsonParse variant wraps the original error, so source() should return it
        let source = vc_err.source();
        assert!(source.is_some());
    }

    #[test]
    fn test_non_wrapped_errors_have_no_source() {
        use std::error::Error;

        let err = VcBridgeError::Backend("test".to_string());
        assert!(err.source().is_none());

        let err = VcBridgeError::Conversion("test".to_string());
        assert!(err.source().is_none());

        let err = VcBridgeError::InvalidExprKind("test".to_string());
        assert!(err.source().is_none());

        let err = VcBridgeError::InvalidType("test".to_string());
        assert!(err.source().is_none());

        let err = VcBridgeError::InvalidAutoVcKind("test".to_string());
        assert!(err.source().is_none());

        let err = VcBridgeError::MissingField("test".to_string());
        assert!(err.source().is_none());
    }

    // ==========================================================================
    // Edge case tests
    // ==========================================================================

    #[test]
    fn test_empty_string_error_messages() {
        // Errors with empty strings should still format correctly
        let err = VcBridgeError::InvalidExprKind(String::new());
        assert_eq!(format!("{err}"), "Invalid expression kind: ");

        let err = VcBridgeError::MissingField(String::new());
        assert_eq!(format!("{err}"), "Missing required field: ");
    }

    #[test]
    fn test_unicode_in_error_messages() {
        let err = VcBridgeError::Backend("エラー: solver failed".to_string());
        let msg = format!("{err}");
        assert!(msg.contains("エラー"));
    }

    #[test]
    fn test_multiline_error_message() {
        let err = VcBridgeError::Conversion("line 1\nline 2\nline 3".to_string());
        let msg = format!("{err}");
        assert!(msg.contains("line 1\nline 2\nline 3"));
    }

    #[test]
    fn test_long_error_message() {
        let long_msg = "x".repeat(10000);
        let err = VcBridgeError::Backend(long_msg.clone());
        let msg = format!("{err}");
        assert!(msg.contains(&long_msg));
    }

    // ==========================================================================
    // Send + Sync trait bound tests (important for async/threaded code)
    // ==========================================================================

    #[test]
    fn test_error_is_send() {
        fn assert_send<T: Send>() {}
        assert_send::<VcBridgeError>();
    }

    #[test]
    fn test_error_is_sync() {
        fn assert_sync<T: Sync>() {}
        assert_sync::<VcBridgeError>();
    }

    #[test]
    fn test_result_is_send() {
        fn assert_send<T: Send>() {}
        assert_send::<VcBridgeResult<i32>>();
    }

    #[test]
    fn test_result_is_sync() {
        fn assert_sync<T: Sync>() {}
        assert_sync::<VcBridgeResult<i32>>();
    }

    // ==========================================================================
    // Error trait implementation tests
    // ==========================================================================

    #[test]
    fn test_error_implements_std_error() {
        fn assert_error<T: std::error::Error>() {}
        assert_error::<VcBridgeError>();
    }

    #[test]
    fn test_error_into_box_dyn_error() {
        let err = VcBridgeError::Backend("test".to_string());
        let boxed: Box<dyn std::error::Error> = Box::new(err);
        assert!(boxed.to_string().contains("Backend error"));
    }

    #[test]
    fn test_error_into_box_dyn_error_send_sync() {
        let err = VcBridgeError::Backend("test".to_string());
        let boxed: Box<dyn std::error::Error + Send + Sync> = Box::new(err);
        assert!(boxed.to_string().contains("Backend error"));
    }

    // ==========================================================================
    // JSON parse error variant tests
    // ==========================================================================

    #[test]
    fn test_json_parse_eof_error() {
        let json = r#"{"incomplete": true"#;
        let err: VcBridgeError = serde_json::from_str::<serde_json::Value>(json)
            .unwrap_err()
            .into();
        assert!(matches!(err, VcBridgeError::JsonParse(_)));
        let msg = format!("{err}");
        assert!(msg.contains("JSON parse error"));
    }

    #[test]
    fn test_json_parse_type_mismatch() {
        // Trying to parse a string as a number
        let json = r#""not a number""#;
        let result: Result<i32, _> = serde_json::from_str(json);
        let err: VcBridgeError = result.unwrap_err().into();
        assert!(matches!(err, VcBridgeError::JsonParse(_)));
    }

    #[test]
    fn test_json_parse_invalid_syntax() {
        let json = r"{{{}}}";
        let err: VcBridgeError = serde_json::from_str::<serde_json::Value>(json)
            .unwrap_err()
            .into();
        assert!(matches!(err, VcBridgeError::JsonParse(_)));
    }

    #[test]
    fn test_json_parse_trailing_chars() {
        let json = r#"{"valid": true}extra"#;
        let err: VcBridgeError = serde_json::from_str::<serde_json::Value>(json)
            .unwrap_err()
            .into();
        assert!(matches!(err, VcBridgeError::JsonParse(_)));
    }

    #[test]
    fn test_json_parse_empty_input() {
        let json = "";
        let err: VcBridgeError = serde_json::from_str::<serde_json::Value>(json)
            .unwrap_err()
            .into();
        assert!(matches!(err, VcBridgeError::JsonParse(_)));
    }

    // ==========================================================================
    // Result combinator tests
    // ==========================================================================

    #[test]
    fn test_result_map_ok() {
        let result: VcBridgeResult<i32> = Ok(10);
        let mapped = result.map(|x| x * 2);
        assert_eq!(mapped.unwrap(), 20);
    }

    #[test]
    fn test_result_map_err() {
        let result: VcBridgeResult<i32> = Err(VcBridgeError::Backend("test".to_string()));
        let mapped = result.map(|x| x * 2);
        assert!(mapped.is_err());
    }

    #[test]
    fn test_result_map_err_transform() {
        let result: VcBridgeResult<i32> = Err(VcBridgeError::Backend("original".to_string()));
        let transformed = result.map_err(|_| VcBridgeError::Conversion("transformed".to_string()));
        assert!(matches!(transformed, Err(VcBridgeError::Conversion(_))));
    }

    #[test]
    fn test_result_and_then_success() {
        fn double(x: i32) -> VcBridgeResult<i32> {
            if x < 0 {
                return Err(VcBridgeError::Backend("negative input".to_string()));
            }
            Ok(x * 2)
        }

        let result: VcBridgeResult<i32> = Ok(5);
        let chained = result.and_then(double);
        assert_eq!(chained.unwrap(), 10);
    }

    #[test]
    fn test_result_and_then_first_error() {
        fn double(x: i32) -> VcBridgeResult<i32> {
            if x < 0 {
                return Err(VcBridgeError::Backend("negative input".to_string()));
            }
            Ok(x * 2)
        }

        let result: VcBridgeResult<i32> = Err(VcBridgeError::Backend("first".to_string()));
        let chained = result.and_then(double);
        assert!(chained.is_err());
    }

    #[test]
    fn test_result_and_then_second_error() {
        fn fails(_: i32) -> VcBridgeResult<i32> {
            Err(VcBridgeError::Backend("second".to_string()))
        }

        let result: VcBridgeResult<i32> = Ok(5);
        let chained = result.and_then(fails);
        let err = chained.unwrap_err();
        assert!(format!("{err}").contains("second"));
    }

    #[test]
    fn test_result_or_else_success() {
        fn fallback(err: VcBridgeError) -> VcBridgeResult<i32> {
            match err {
                VcBridgeError::Backend(_) => Ok(42),
                other => Err(other),
            }
        }

        let result: VcBridgeResult<i32> = Ok(10);
        let recovered = result.or_else(fallback);
        assert_eq!(recovered.unwrap(), 10);
    }

    #[test]
    fn test_result_or_else_recovery() {
        fn fallback(err: VcBridgeError) -> VcBridgeResult<i32> {
            match err {
                VcBridgeError::Backend(_) => Ok(42),
                other => Err(other),
            }
        }

        let result: VcBridgeResult<i32> = Err(VcBridgeError::Backend("error".to_string()));
        let recovered = result.or_else(fallback);
        assert_eq!(recovered.unwrap(), 42);
    }

    #[test]
    #[allow(clippy::unnecessary_literal_unwrap)]
    fn test_result_unwrap_or() {
        let result: VcBridgeResult<i32> = Err(VcBridgeError::Backend("err".to_string()));
        assert_eq!(result.unwrap_or(99), 99);
    }

    #[test]
    #[allow(
        clippy::unnecessary_literal_unwrap,
        clippy::unnecessary_lazy_evaluations
    )]
    fn test_result_unwrap_or_else() {
        let result: VcBridgeResult<i32> = Err(VcBridgeError::Backend("err".to_string()));
        assert_eq!(result.unwrap_or_else(|_| 100), 100);
    }

    // ==========================================================================
    // Special character tests
    // ==========================================================================

    #[test]
    fn test_error_with_tab_characters() {
        let err = VcBridgeError::Backend("col1\tcol2\tcol3".to_string());
        let msg = format!("{err}");
        assert!(msg.contains('\t'));
    }

    #[test]
    fn test_error_with_carriage_return() {
        let err = VcBridgeError::Backend("line1\r\nline2".to_string());
        let msg = format!("{err}");
        assert!(msg.contains("\r\n"));
    }

    #[test]
    fn test_error_with_null_byte() {
        let err = VcBridgeError::Backend("before\0after".to_string());
        let msg = format!("{err}");
        assert!(msg.contains('\0'));
    }

    #[test]
    fn test_error_with_quotes() {
        let err = VcBridgeError::InvalidExprKind("\"quoted\"".to_string());
        let msg = format!("{err}");
        assert!(msg.contains("\"quoted\""));
    }

    #[test]
    fn test_error_with_backslashes() {
        let err = VcBridgeError::InvalidType("path\\to\\type".to_string());
        let msg = format!("{err}");
        assert!(msg.contains("path\\to\\type"));
    }

    #[test]
    fn test_error_with_emoji() {
        let err = VcBridgeError::Backend("failed 💥".to_string());
        let msg = format!("{err}");
        assert!(msg.contains("💥"));
    }

    #[test]
    fn test_error_with_control_characters() {
        let err = VcBridgeError::Conversion("bell\x07escape\x1b".to_string());
        let msg = format!("{err}");
        assert!(msg.contains('\x07'));
        assert!(msg.contains('\x1b'));
    }

    // ==========================================================================
    // Error message pattern tests
    // ==========================================================================

    #[test]
    fn test_all_error_messages_start_correctly() {
        // Verify each error variant produces the expected prefix
        let tests = vec![
            (
                VcBridgeError::InvalidExprKind("x".to_string()),
                "Invalid expression kind:",
            ),
            (
                VcBridgeError::MissingField("x".to_string()),
                "Missing required field:",
            ),
            (VcBridgeError::InvalidType("x".to_string()), "Invalid type:"),
            (
                VcBridgeError::InvalidAutoVcKind("x".to_string()),
                "Invalid auto-VC kind:",
            ),
            (
                VcBridgeError::Conversion("x".to_string()),
                "Conversion error:",
            ),
            (VcBridgeError::Backend("x".to_string()), "Backend error:"),
        ];

        for (err, expected_prefix) in tests {
            let msg = format!("{err}");
            assert!(
                msg.starts_with(expected_prefix),
                "Error '{msg}' should start with '{expected_prefix}'"
            );
        }
    }

    #[test]
    fn test_error_message_contains_value() {
        // Verify the error message contains the inner value
        let unique_marker = "UNIQUE_TEST_MARKER_12345";
        let tests = vec![
            VcBridgeError::InvalidExprKind(unique_marker.to_string()),
            VcBridgeError::MissingField(unique_marker.to_string()),
            VcBridgeError::InvalidType(unique_marker.to_string()),
            VcBridgeError::InvalidAutoVcKind(unique_marker.to_string()),
            VcBridgeError::Conversion(unique_marker.to_string()),
            VcBridgeError::Backend(unique_marker.to_string()),
        ];

        for err in tests {
            let msg = format!("{err}");
            assert!(
                msg.contains(unique_marker),
                "Error message '{msg}' should contain '{unique_marker}'"
            );
        }
    }

    // ==========================================================================
    // Debug format tests
    // ==========================================================================

    #[test]
    fn test_debug_format_all_variants() {
        let variants = vec![
            VcBridgeError::InvalidExprKind("test".to_string()),
            VcBridgeError::MissingField("test".to_string()),
            VcBridgeError::InvalidType("test".to_string()),
            VcBridgeError::InvalidAutoVcKind("test".to_string()),
            VcBridgeError::Conversion("test".to_string()),
            VcBridgeError::Backend("test".to_string()),
        ];

        for err in variants {
            let debug_str = format!("{err:?}");
            // Debug format should be non-empty and contain the variant name
            assert!(!debug_str.is_empty());
        }
    }

    #[test]
    fn test_debug_format_contains_inner_value() {
        let err = VcBridgeError::InvalidExprKind("inner_value_xyz".to_string());
        let debug_str = format!("{err:?}");
        assert!(debug_str.contains("inner_value_xyz"));
    }

    #[test]
    fn test_debug_alternate_format() {
        let err = VcBridgeError::Backend("test".to_string());
        let debug_str = format!("{err:#?}");
        assert!(!debug_str.is_empty());
    }

    // ==========================================================================
    // Error size tests
    // ==========================================================================

    #[test]
    fn test_error_size_is_reasonable() {
        // VcBridgeError should have a reasonable size (not too large)
        // String is 24 bytes on 64-bit, enum discriminant adds a few bytes
        let size = std::mem::size_of::<VcBridgeError>();
        assert!(
            size <= 64,
            "VcBridgeError size {size} is larger than expected"
        );
    }

    #[test]
    fn test_result_size() {
        // Result<T, VcBridgeError> size should be reasonable
        let size = std::mem::size_of::<VcBridgeResult<i32>>();
        assert!(
            size <= 72,
            "VcBridgeResult<i32> size {size} is larger than expected"
        );
    }

    // ==========================================================================
    // Error chaining tests
    // ==========================================================================

    #[test]
    fn test_error_chain_multiple_levels() {
        use std::error::Error;

        fn level3() -> VcBridgeResult<i32> {
            Err(VcBridgeError::Backend("level3 error".to_string()))
        }

        fn level2() -> VcBridgeResult<i32> {
            level3()
        }

        fn level1() -> VcBridgeResult<i32> {
            level2()
        }

        let result = level1();
        let err = result.unwrap_err();
        // The error should still have the original message
        assert!(err.to_string().contains("level3"));
        // Non-wrapped errors have no source
        assert!(err.source().is_none());
    }

    #[test]
    fn test_json_error_chain_has_source() {
        use std::error::Error;

        let invalid_json = r#"{"broken"#;
        let json_err = serde_json::from_str::<serde_json::Value>(invalid_json).unwrap_err();
        let vc_err: VcBridgeError = json_err.into();

        // The source should be the original serde_json error
        let source = vc_err.source();
        assert!(source.is_some());

        // Source description should contain something about JSON
        let source_desc = source.unwrap().to_string();
        assert!(!source_desc.is_empty());
    }

    // ==========================================================================
    // Pattern matching exhaustiveness tests
    // ==========================================================================

    #[test]
    fn test_pattern_match_all_variants() {
        let errors = vec![
            VcBridgeError::JsonParse(serde_json::from_str::<()>("invalid").unwrap_err()),
            VcBridgeError::InvalidExprKind("test".to_string()),
            VcBridgeError::MissingField("test".to_string()),
            VcBridgeError::InvalidType("test".to_string()),
            VcBridgeError::InvalidAutoVcKind("test".to_string()),
            VcBridgeError::Conversion("test".to_string()),
            VcBridgeError::Backend("test".to_string()),
        ];

        for err in errors {
            // This match must be exhaustive - compiler enforces coverage
            let _category = match &err {
                VcBridgeError::JsonParse(_) => "json",
                VcBridgeError::InvalidExprKind(_) => "expr",
                VcBridgeError::MissingField(_) => "field",
                VcBridgeError::InvalidType(_) => "type",
                VcBridgeError::InvalidAutoVcKind(_) => "autovc",
                VcBridgeError::Conversion(_) => "conversion",
                VcBridgeError::Backend(_) => "backend",
            };
        }
    }

    // ==========================================================================
    // Thread safety tests
    // ==========================================================================

    #[test]
    fn test_error_can_be_sent_across_threads() {
        use std::thread;

        let err = VcBridgeError::Backend("cross-thread error".to_string());
        let handle = thread::spawn(move || format!("{err}"));

        let result = handle.join().unwrap();
        assert!(result.contains("cross-thread"));
    }

    #[test]
    fn test_result_can_be_sent_across_threads() {
        use std::thread;

        let result: VcBridgeResult<i32> = Err(VcBridgeError::Backend("thread test".to_string()));
        let handle = thread::spawn(move || result.is_err());

        assert!(handle.join().unwrap());
    }

    // ==========================================================================
    // Comparison and equality tests (if applicable via Debug)
    // ==========================================================================

    #[test]
    fn test_same_error_same_debug() {
        let err1 = VcBridgeError::Backend("test".to_string());
        let err2 = VcBridgeError::Backend("test".to_string());

        let debug1 = format!("{err1:?}");
        let debug2 = format!("{err2:?}");

        assert_eq!(debug1, debug2);
    }

    #[test]
    fn test_different_errors_different_debug() {
        let err1 = VcBridgeError::Backend("test1".to_string());
        let err2 = VcBridgeError::Backend("test2".to_string());

        let debug1 = format!("{err1:?}");
        let debug2 = format!("{err2:?}");

        assert_ne!(debug1, debug2);
    }

    #[test]
    fn test_different_variants_different_debug() {
        let err1 = VcBridgeError::Backend("test".to_string());
        let err2 = VcBridgeError::Conversion("test".to_string());

        let debug1 = format!("{err1:?}");
        let debug2 = format!("{err2:?}");

        assert_ne!(debug1, debug2);
    }

    // ==========================================================================
    // Result method tests (ok, err, expect_err, as_ref)
    // ==========================================================================

    #[test]
    fn test_result_ok_method_on_success() {
        let result: VcBridgeResult<i32> = Ok(42);
        assert_eq!(result.ok(), Some(42));
    }

    #[test]
    fn test_result_ok_method_on_failure() {
        let result: VcBridgeResult<i32> = Err(VcBridgeError::Backend("err".to_string()));
        assert_eq!(result.ok(), None);
    }

    #[test]
    fn test_result_err_method_on_success() {
        let result: VcBridgeResult<i32> = Ok(42);
        assert!(result.err().is_none());
    }

    #[test]
    fn test_result_err_method_on_failure() {
        let result: VcBridgeResult<i32> = Err(VcBridgeError::Backend("test".to_string()));
        let err = result.err();
        assert!(err.is_some());
        assert!(matches!(err.unwrap(), VcBridgeError::Backend(_)));
    }

    #[test]
    #[should_panic(expected = "expected error")]
    #[allow(clippy::unnecessary_literal_unwrap)]
    fn test_result_expect_err_on_success_panics() {
        let result: VcBridgeResult<i32> = Ok(42);
        let _ = result.expect_err("expected error");
    }

    #[test]
    #[allow(clippy::unnecessary_literal_unwrap)]
    fn test_result_expect_err_on_failure() {
        let result: VcBridgeResult<i32> = Err(VcBridgeError::Backend("test".to_string()));
        let err = result.expect_err("should be error");
        assert!(matches!(err, VcBridgeError::Backend(_)));
    }

    #[test]
    fn test_result_as_ref_ok() {
        let result: VcBridgeResult<i32> = Ok(42);
        let ref_result = result.as_ref();
        assert_eq!(ref_result.unwrap(), &42);
    }

    #[test]
    fn test_result_as_ref_err() {
        let result: VcBridgeResult<i32> = Err(VcBridgeError::Backend("test".to_string()));
        let ref_result = result.as_ref();
        assert!(ref_result.is_err());
    }

    #[test]
    fn test_result_is_ok_and() {
        let result: VcBridgeResult<i32> = Ok(42);
        assert!(result.is_ok_and(|x| x > 0));

        let result2: VcBridgeResult<i32> = Ok(-1);
        assert!(!result2.is_ok_and(|x| x > 0));

        let result3: VcBridgeResult<i32> = Err(VcBridgeError::Backend("err".to_string()));
        assert!(!result3.is_ok_and(|x| x > 0));
    }

    #[test]
    fn test_result_is_err_and() {
        let result: VcBridgeResult<i32> = Err(VcBridgeError::Backend("test".to_string()));
        assert!(result.is_err_and(|e| matches!(e, VcBridgeError::Backend(_))));

        let result2: VcBridgeResult<i32> = Err(VcBridgeError::Conversion("conv".to_string()));
        assert!(!result2.is_err_and(|e| matches!(e, VcBridgeError::Backend(_))));

        let result3: VcBridgeResult<i32> = Ok(42);
        assert!(!result3.is_err_and(|e| matches!(e, VcBridgeError::Backend(_))));
    }

    // ==========================================================================
    // Collection tests (Vec, Box, Arc)
    // ==========================================================================

    #[test]
    fn test_vec_of_errors() {
        let errors: Vec<VcBridgeError> = vec![
            VcBridgeError::Backend("err1".to_string()),
            VcBridgeError::Conversion("err2".to_string()),
            VcBridgeError::InvalidType("err3".to_string()),
        ];

        assert_eq!(errors.len(), 3);
        assert!(matches!(&errors[0], VcBridgeError::Backend(_)));
        assert!(matches!(&errors[1], VcBridgeError::Conversion(_)));
        assert!(matches!(&errors[2], VcBridgeError::InvalidType(_)));
    }

    #[test]
    fn test_vec_of_errors_iteration() {
        let errors: Vec<VcBridgeError> = vec![
            VcBridgeError::Backend("1".to_string()),
            VcBridgeError::Backend("2".to_string()),
            VcBridgeError::Backend("3".to_string()),
        ];

        let messages: Vec<String> = errors.iter().map(ToString::to_string).collect();
        assert_eq!(messages.len(), 3);
        assert!(messages[0].contains('1'));
        assert!(messages[1].contains('2'));
        assert!(messages[2].contains('3'));
    }

    #[test]
    fn test_box_error() {
        let err = Box::new(VcBridgeError::Backend("boxed".to_string()));
        assert!(err.to_string().contains("boxed"));
    }

    #[test]
    fn test_box_dyn_error_downcast() {
        let err: Box<dyn std::error::Error> = Box::new(VcBridgeError::Backend("test".to_string()));
        // downcast_ref should work
        let downcast = err.downcast_ref::<VcBridgeError>();
        assert!(downcast.is_some());
        assert!(matches!(downcast.unwrap(), VcBridgeError::Backend(_)));
    }

    #[test]
    fn test_arc_error_shared() {
        use std::sync::Arc;

        let err = Arc::new(VcBridgeError::Backend("shared".to_string()));
        let err_clone = Arc::clone(&err);

        assert!(err.to_string().contains("shared"));
        assert!(err_clone.to_string().contains("shared"));
        assert_eq!(Arc::strong_count(&err), 2);
    }

    #[test]
    fn test_arc_error_across_threads() {
        use std::sync::Arc;
        use std::thread;

        let err = Arc::new(VcBridgeError::Backend("arc-thread".to_string()));
        let err_clone = Arc::clone(&err);

        let handle = thread::spawn(move || err_clone.to_string());

        let result = handle.join().unwrap();
        assert!(result.contains("arc-thread"));
    }

    #[test]
    #[allow(clippy::unnecessary_literal_unwrap)]
    fn test_option_error_some() {
        let maybe_err: Option<VcBridgeError> = Some(VcBridgeError::Backend("test".to_string()));
        assert!(maybe_err.is_some());
        assert!(matches!(maybe_err.unwrap(), VcBridgeError::Backend(_)));
    }

    #[test]
    fn test_option_error_none() {
        let maybe_err: Option<VcBridgeError> = None;
        assert!(maybe_err.is_none());
    }

    #[test]
    fn test_result_transpose() {
        // Ok(Some(v)) -> Some(Ok(v))
        let result: VcBridgeResult<Option<i32>> = Ok(Some(42));
        let transposed: Option<VcBridgeResult<i32>> = result.transpose();
        assert!(matches!(transposed, Some(Ok(42))));

        // Ok(None) -> None
        let result2: VcBridgeResult<Option<i32>> = Ok(None);
        let transposed2: Option<VcBridgeResult<i32>> = result2.transpose();
        assert!(transposed2.is_none());

        // Err(e) -> Some(Err(e))
        let result3: VcBridgeResult<Option<i32>> = Err(VcBridgeError::Backend("err".to_string()));
        let transposed3: Option<VcBridgeResult<i32>> = result3.transpose();
        assert!(matches!(transposed3, Some(Err(_))));
    }

    // ==========================================================================
    // More JSON error scenarios
    // ==========================================================================

    #[test]
    fn test_json_parse_deeply_nested() {
        // Create deeply nested JSON that fails
        let mut json = "{".repeat(100);
        json.push_str(&"}".repeat(99)); // Missing one closing brace
        let err: VcBridgeError = serde_json::from_str::<serde_json::Value>(&json)
            .unwrap_err()
            .into();
        assert!(matches!(err, VcBridgeError::JsonParse(_)));
    }

    #[test]
    fn test_json_parse_large_number() {
        // Number too large for JSON
        let json = "99999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999";
        let result: Result<u64, _> = serde_json::from_str(json);
        if let Err(e) = result {
            let err: VcBridgeError = e.into();
            assert!(matches!(err, VcBridgeError::JsonParse(_)));
        }
    }

    #[test]
    fn test_json_parse_unicode_escape_error() {
        let json = r#""\uXXXX""#; // Invalid unicode escape
        let err: VcBridgeError = serde_json::from_str::<String>(json).unwrap_err().into();
        assert!(matches!(err, VcBridgeError::JsonParse(_)));
    }

    #[test]
    fn test_json_parse_missing_comma() {
        let json = r#"{"a": 1 "b": 2}"#;
        let err: VcBridgeError = serde_json::from_str::<serde_json::Value>(json)
            .unwrap_err()
            .into();
        assert!(matches!(err, VcBridgeError::JsonParse(_)));
    }

    #[test]
    fn test_json_parse_duplicate_key() {
        // serde_json allows duplicate keys (last wins), so this should parse successfully
        let json = r#"{"a": 1, "a": 2}"#;
        let result: Result<serde_json::Value, _> = serde_json::from_str(json);
        // This should succeed, not fail
        assert!(result.is_ok());
    }

    #[test]
    fn test_json_parse_control_char_in_string() {
        // Unescaped control character in string
        let json = "\"hello\x01world\"";
        let err: VcBridgeError = serde_json::from_str::<String>(json).unwrap_err().into();
        assert!(matches!(err, VcBridgeError::JsonParse(_)));
    }

    // ==========================================================================
    // Unicode edge cases
    // ==========================================================================

    #[test]
    fn test_error_with_combining_characters() {
        // e + combining acute accent = é
        let err = VcBridgeError::Backend("cafe\u{0301}".to_string());
        let msg = format!("{err}");
        assert!(msg.contains("cafe\u{0301}"));
    }

    #[test]
    fn test_error_with_zero_width_chars() {
        // Zero-width space, zero-width joiner, zero-width non-joiner
        let err = VcBridgeError::Backend("a\u{200B}b\u{200C}c\u{200D}d".to_string());
        let msg = format!("{err}");
        assert!(msg.contains("a\u{200B}b\u{200C}c\u{200D}d"));
    }

    #[test]
    fn test_error_with_rtl_text() {
        // Right-to-left text (Hebrew)
        let err = VcBridgeError::Backend("שלום".to_string());
        let msg = format!("{err}");
        assert!(msg.contains("שלום"));
    }

    #[test]
    fn test_error_with_surrogate_pair_emoji() {
        // Emoji that requires surrogate pairs in UTF-16
        let err = VcBridgeError::Backend("👨‍👩‍👧‍👦".to_string());
        let msg = format!("{err}");
        assert!(msg.contains("👨‍👩‍👧‍👦"));
    }

    #[test]
    fn test_error_with_mathematical_symbols() {
        let err = VcBridgeError::InvalidType("∀x∈ℝ: x²≥0".to_string());
        let msg = format!("{err}");
        assert!(msg.contains("∀x∈ℝ"));
    }

    // ==========================================================================
    // Format specifier tests
    // ==========================================================================

    #[test]
    fn test_error_format_default() {
        let err = VcBridgeError::Backend("test".to_string());
        let msg = format!("{err}");
        // Default formatting should produce the error message
        assert_eq!(msg, "Backend error: test");
    }

    #[test]
    fn test_error_format_via_to_string() {
        let err = VcBridgeError::Backend("test".to_string());
        let msg = err.to_string();
        assert_eq!(msg, "Backend error: test");
    }

    #[test]
    fn test_error_format_in_string_interpolation() {
        let err = VcBridgeError::Backend("inner".to_string());
        let msg = format!("Outer: {err}");
        assert_eq!(msg, "Outer: Backend error: inner");
    }

    #[test]
    fn test_error_format_multiple_in_same_string() {
        let err1 = VcBridgeError::Backend("first".to_string());
        let err2 = VcBridgeError::Conversion("second".to_string());
        let msg = format!("{err1} and {err2}");
        assert!(msg.contains("Backend error: first"));
        assert!(msg.contains("Conversion error: second"));
    }

    #[test]
    fn test_debug_format_contains_variant_name() {
        let err = VcBridgeError::Backend("test".to_string());
        let debug = format!("{err:?}");
        assert!(debug.contains("Backend"));
        assert!(debug.contains("test"));
    }

    // ==========================================================================
    // Error creation from functions tests
    // ==========================================================================

    #[test]
    fn test_error_in_closure() {
        let make_error = |msg: &str| VcBridgeError::Backend(msg.to_string());
        let err = make_error("closure error");
        assert!(err.to_string().contains("closure error"));
    }

    #[test]
    fn test_error_from_format_macro() {
        let value = 42;
        let err = VcBridgeError::Conversion(format!("failed to convert value: {value}"));
        assert!(err.to_string().contains("42"));
    }

    #[test]
    fn test_error_from_concat() {
        let prefix = "prefix";
        let suffix = "suffix";
        let err = VcBridgeError::Backend([prefix, "_", suffix].concat());
        assert!(err.to_string().contains("prefix_suffix"));
    }

    // ==========================================================================
    // Memory and drop tests
    // ==========================================================================

    #[test]
    fn test_error_drop_no_panic() {
        // Creating and dropping errors should not panic
        {
            let _err = VcBridgeError::Backend("will be dropped".to_string());
        }
        // If we get here, drop didn't panic
    }

    #[test]
    fn test_error_replace_in_result() {
        let mut result: VcBridgeResult<i32> = Err(VcBridgeError::Backend("original".to_string()));
        // Verify original error exists
        assert!(result.is_err());
        result = Ok(42);
        assert_eq!(result.unwrap(), 42);
    }

    #[test]
    fn test_error_in_vec_clear() {
        let mut errors: Vec<VcBridgeError> = vec![
            VcBridgeError::Backend("1".to_string()),
            VcBridgeError::Backend("2".to_string()),
        ];
        errors.clear();
        assert!(errors.is_empty());
    }

    // ==========================================================================
    // Exhaustive variant message tests
    // ==========================================================================

    #[test]
    fn test_json_parse_message_format() {
        let json = "{invalid}";
        let err: VcBridgeError = serde_json::from_str::<serde_json::Value>(json)
            .unwrap_err()
            .into();
        let msg = err.to_string();
        assert!(msg.starts_with("JSON parse error:"));
    }

    #[test]
    fn test_all_variants_have_colon_separator() {
        // All non-JsonParse variants should have ": " after the error type
        let variants = vec![
            VcBridgeError::InvalidExprKind("x".to_string()),
            VcBridgeError::MissingField("x".to_string()),
            VcBridgeError::InvalidType("x".to_string()),
            VcBridgeError::InvalidAutoVcKind("x".to_string()),
            VcBridgeError::Conversion("x".to_string()),
            VcBridgeError::Backend("x".to_string()),
        ];

        for err in variants {
            let msg = err.to_string();
            assert!(msg.contains(": x"), "Error '{msg}' should contain ': x'");
        }
    }

    // ==========================================================================
    // Result flatten tests
    // ==========================================================================

    #[test]
    fn test_result_flatten_ok_ok() {
        let result: VcBridgeResult<VcBridgeResult<i32>> = Ok(Ok(42));
        let flattened: VcBridgeResult<i32> = result.flatten();
        assert_eq!(flattened.unwrap(), 42);
    }

    #[test]
    fn test_result_flatten_ok_err() {
        let result: VcBridgeResult<VcBridgeResult<i32>> =
            Ok(Err(VcBridgeError::Backend("inner".to_string())));
        let flattened: VcBridgeResult<i32> = result.flatten();
        assert!(flattened.is_err());
        assert!(flattened.unwrap_err().to_string().contains("inner"));
    }

    #[test]
    fn test_result_flatten_err() {
        let result: VcBridgeResult<VcBridgeResult<i32>> =
            Err(VcBridgeError::Backend("outer".to_string()));
        let flattened: VcBridgeResult<i32> = result.flatten();
        assert!(flattened.is_err());
        assert!(flattened.unwrap_err().to_string().contains("outer"));
    }

    // ==========================================================================
    // Result into_ok and into_err (where applicable)
    // ==========================================================================

    #[test]
    fn test_result_copied() {
        let value = 42i32;
        let result: VcBridgeResult<&i32> = Ok(&value);
        let copied: VcBridgeResult<i32> = result.copied();
        assert_eq!(copied.unwrap(), 42);
    }

    #[test]
    fn test_result_cloned() {
        let value = "test".to_string();
        let result: VcBridgeResult<&String> = Ok(&value);
        let cloned: VcBridgeResult<String> = result.cloned();
        assert_eq!(cloned.unwrap(), "test");
    }

    // ==========================================================================
    // Additional edge cases
    // ==========================================================================

    #[test]
    fn test_error_with_only_whitespace() {
        let err = VcBridgeError::Backend("   \t\n  ".to_string());
        let msg = format!("{err}");
        assert!(msg.contains("   \t\n  "));
    }

    #[test]
    fn test_error_with_repeated_pattern() {
        let pattern = "abc".repeat(1000);
        let err = VcBridgeError::Backend(pattern.clone());
        let msg = format!("{err}");
        assert!(msg.contains(&pattern));
    }

    #[test]
    fn test_error_message_ends_with_value() {
        // All string-based errors should end with the value
        let value = "END_MARKER";
        let err = VcBridgeError::Backend(value.to_string());
        let msg = err.to_string();
        assert!(msg.ends_with(value));
    }

    #[test]
    fn test_multiple_results_in_vec() {
        let results: Vec<VcBridgeResult<i32>> = vec![
            Ok(1),
            Err(VcBridgeError::Backend("err1".to_string())),
            Ok(2),
            Err(VcBridgeError::Conversion("err2".to_string())),
        ];

        let (oks, errs): (Vec<_>, Vec<_>) = results.into_iter().partition(Result::is_ok);
        assert_eq!(oks.len(), 2);
        assert_eq!(errs.len(), 2);
    }

    #[test]
    fn test_result_collect_vec() {
        let results: Vec<VcBridgeResult<i32>> = vec![Ok(1), Ok(2), Ok(3)];
        let collected: VcBridgeResult<Vec<i32>> = results.into_iter().collect();
        assert_eq!(collected.unwrap(), vec![1, 2, 3]);
    }

    #[test]
    fn test_result_collect_vec_with_error() {
        let results: Vec<VcBridgeResult<i32>> = vec![
            Ok(1),
            Err(VcBridgeError::Backend("fail".to_string())),
            Ok(3),
        ];
        let collected: VcBridgeResult<Vec<i32>> = results.into_iter().collect();
        assert!(collected.is_err());
    }

    #[test]
    fn test_error_with_path_separator() {
        let err = VcBridgeError::InvalidType("module::submodule::Type".to_string());
        let msg = format!("{err}");
        assert!(msg.contains("module::submodule::Type"));
    }

    #[test]
    fn test_error_with_angle_brackets() {
        let err = VcBridgeError::InvalidType("Vec<Option<String>>".to_string());
        let msg = format!("{err}");
        assert!(msg.contains("Vec<Option<String>>"));
    }
}
