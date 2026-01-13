//! Swift Name Demangling
//!
//! This module provides utilities for demangling Swift mangled names.
//! It uses `xcrun swift-demangle` when available, with a fallback
//! for common patterns.

use std::collections::HashMap;
use std::process::Command;

/// Cache for demangled names to avoid repeated process spawns
static DEMANGLE_CACHE: std::sync::LazyLock<std::sync::Mutex<HashMap<String, String>>> =
    std::sync::LazyLock::new(|| std::sync::Mutex::new(HashMap::new()));

/// Demangle a Swift mangled name.
///
/// Returns the demangled name if successful, or None if demangling fails.
/// Uses `xcrun swift-demangle` when available.
///
/// # Example
/// ```ignore
/// let mangled = "$s8test_sil3addyS2i_SitF";
/// let demangled = demangle(mangled);
/// assert_eq!(demangled, Some("test_sil.add(Swift.Int, Swift.Int) -> Swift.Int".to_string()));
/// ```
pub fn demangle(mangled: &str) -> Option<String> {
    // Check if already demangled (doesn't start with $ or _$)
    if !mangled.starts_with('$') && !mangled.starts_with("_$") {
        return Some(mangled.to_string());
    }

    // Check cache first
    {
        let cache = DEMANGLE_CACHE.lock().ok()?;
        if let Some(cached) = cache.get(mangled) {
            return Some(cached.clone());
        }
    }

    // Try xcrun swift-demangle
    let result = demangle_via_xcrun(mangled);

    // Cache the result
    if let Some(ref demangled) = result {
        if let Ok(mut cache) = DEMANGLE_CACHE.lock() {
            cache.insert(mangled.to_string(), demangled.clone());
        }
    }

    result
}

/// Parse a single line of `xcrun swift-demangle` output.
///
/// `swift-demangle` commonly emits `"<input> ---> <output>"`. This function
/// extracts `<output>` and trims surrounding whitespace. If the delimiter is
/// absent, it returns the trimmed input.
fn parse_xcrun_demangle_line(line: &str) -> &str {
    let trimmed = line.trim();
    trimmed
        .find(" ---> ")
        .map_or(trimmed, |arrow_pos| trimmed[arrow_pos + 6..].trim())
}

/// Demangle using xcrun swift-demangle
fn demangle_via_xcrun(mangled: &str) -> Option<String> {
    let output = Command::new("xcrun")
        .args(["swift-demangle", mangled])
        .output()
        .ok()?;

    if output.status.success() {
        let stdout = String::from_utf8_lossy(&output.stdout);
        let first_line = stdout.lines().next()?.trim();
        let demangled = parse_xcrun_demangle_line(first_line).to_string();

        // If demangling didn't change the name, return None
        // This happens when swift-demangle can't demangle (e.g., custom types)
        if demangled == mangled || demangled.is_empty() {
            return None;
        }

        Some(demangled)
    } else {
        None
    }
}

/// Demangle multiple names at once (more efficient for batch processing)
#[must_use]
pub fn demangle_batch(mangled_names: &[&str]) -> HashMap<String, String> {
    let mut results = HashMap::new();

    // Filter to only mangled names
    let to_demangle: Vec<&str> = mangled_names
        .iter()
        .filter(|n| n.starts_with('$') || n.starts_with("_$"))
        .copied()
        .collect();

    if to_demangle.is_empty() {
        return results;
    }

    // Try batch demangling via xcrun
    if let Ok(output) = Command::new("xcrun")
        .arg("swift-demangle")
        .args(&to_demangle)
        .output()
    {
        if output.status.success() {
            let stdout = String::from_utf8_lossy(&output.stdout);
            for (mangled, demangled) in to_demangle.iter().zip(stdout.lines()) {
                let parsed = parse_xcrun_demangle_line(demangled);
                if !parsed.is_empty() && parsed != *mangled {
                    results.insert((*mangled).to_string(), parsed.to_string());
                }
            }
        }
    }

    results
}

/// Try to extract function name from a mangled Swift name when demangling fails.
///
/// Swift 5+ mangled names have format: `$s<len><module><len><func>...`
/// Example: `$s16forced_cast_safe8safeCastAA3DogCAA6AnimalCF`
///   - Module: 16 chars "`forced_cast_safe`"
///   - Function: 8 chars "safeCast"
///
/// Returns None if the format doesn't match.
#[must_use]
pub fn extract_func_from_mangled(mangled: &str) -> Option<String> {
    // Must start with $s or _$s
    let rest = mangled
        .strip_prefix("$s")
        .or_else(|| mangled.strip_prefix("_$s"))?;

    // Parse module name: <length><name>
    let (module_len, after_module_len) = parse_length_prefix(rest)?;
    if after_module_len.len() < module_len {
        return None;
    }
    let after_module = &after_module_len[module_len..];

    // Parse function name: <length><name>
    let (func_len, after_func_len) = parse_length_prefix(after_module)?;
    if after_func_len.len() < func_len {
        return None;
    }
    let func_name = &after_func_len[..func_len];

    // Basic sanity check: function name should be alphabetic/underscore
    if !func_name.is_empty()
        && func_name
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || c == '_')
    {
        Some(func_name.to_string())
    } else {
        None
    }
}

/// Parse a length prefix (digits followed by the content).
fn parse_length_prefix(s: &str) -> Option<(usize, &str)> {
    let mut len_str = String::new();
    for c in s.chars() {
        if c.is_ascii_digit() {
            len_str.push(c);
        } else {
            break;
        }
    }
    if len_str.is_empty() {
        return None;
    }
    let len: usize = len_str.parse().ok()?;
    Some((len, &s[len_str.len()..]))
}

/// Extract a simplified function name from a demangled signature.
///
/// Converts "module.funcName(Type, Type) -> `ReturnType`" to "`funcName`"
/// or "module.funcName(label1:label2:)" to "funcName"
#[must_use]
pub fn simplify_function_name(demangled: &str) -> String {
    // Find the function name - it's between the last '.' before '(' and '('
    if let Some(paren_pos) = demangled.find('(') {
        let prefix = &demangled[..paren_pos];
        if let Some(dot_pos) = prefix.rfind('.') {
            return prefix[dot_pos + 1..].to_string();
        }
        return prefix.to_string();
    }

    // No parentheses - try to find last component after '.'
    if let Some(dot_pos) = demangled.rfind('.') {
        return demangled[dot_pos + 1..].to_string();
    }

    demangled.to_string()
}

/// Find the matching `)` for the `(` at `open_pos`.
fn find_matching_paren(s: &str, open_pos: usize) -> Option<usize> {
    if s.as_bytes().get(open_pos) != Some(&b'(') {
        return None;
    }

    let mut depth: i32 = 0;
    for (idx, ch) in s.char_indices().skip_while(|(idx, _)| *idx < open_pos) {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(idx);
                }
            }
            _ => {}
        }
    }
    None
}

/// Count top-level arguments in a Swift demangled argument list.
///
/// The input is the substring *inside* the outer `(...)` of the function
/// signature. Commas nested inside tuples, generics, arrays, or function types
/// do not separate arguments.
fn count_top_level_args(args_str: &str) -> usize {
    let args_str = args_str.trim();
    if args_str.is_empty() {
        return 0;
    }

    let mut paren_depth: i32 = 0;
    let mut angle_depth: i32 = 0;
    let mut bracket_depth: i32 = 0;
    let mut brace_depth: i32 = 0;
    let mut count: usize = 1;

    for ch in args_str.chars() {
        match ch {
            '(' => paren_depth += 1,
            ')' if paren_depth > 0 => paren_depth -= 1,
            '<' => angle_depth += 1,
            '>' if angle_depth > 0 => angle_depth -= 1,
            '[' => bracket_depth += 1,
            ']' if bracket_depth > 0 => bracket_depth -= 1,
            '{' => brace_depth += 1,
            '}' if brace_depth > 0 => brace_depth -= 1,
            ',' if paren_depth == 0
                && angle_depth == 0
                && bracket_depth == 0
                && brace_depth == 0 =>
            {
                count += 1;
            }
            _ => {}
        }
    }

    count
}

/// Extract the full qualified name without type signatures.
///
/// Converts "module.funcName(Swift.Int, Swift.Int) -> Swift.Int"
/// to "module.funcName(_:_:)"
#[must_use]
pub fn to_qualified_name(demangled: &str) -> String {
    if let Some(paren_pos) = demangled.find('(') {
        let prefix = &demangled[..paren_pos];

        // Find the matching closing paren for this argument list and extract it.
        if let Some(close_paren) = find_matching_paren(demangled, paren_pos) {
            let args_str = &demangled[paren_pos + 1..close_paren];
            let arg_count = count_top_level_args(args_str);

            // Build argument labels - without actual labels, use _:
            let labels: String = (0..arg_count).map(|_| "_:").collect();

            return format!("{prefix}({labels})");
        }

        return format!("{prefix}()");
    }

    demangled.to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_demangle_swift_name() {
        // This test requires xcrun swift-demangle to be available
        let mangled = "$s8test_sil3addyS2i_SitF";
        if let Some(demangled) = demangle(mangled) {
            assert!(demangled.contains("add"));
            assert!(demangled.contains("Int"));
        }
    }

    #[test]
    fn test_simplify_function_name() {
        let demangled = "test_sil.add(Swift.Int, Swift.Int) -> Swift.Int";
        let simple = simplify_function_name(demangled);
        assert_eq!(simple, "add");
    }

    #[test]
    fn test_to_qualified_name() {
        let demangled = "test_sil.add(Swift.Int, Swift.Int) -> Swift.Int";
        let qualified = to_qualified_name(demangled);
        assert_eq!(qualified, "test_sil.add(_:_:)");
    }

    #[test]
    fn test_already_demangled() {
        let name = "simple_function";
        let result = demangle(name);
        assert_eq!(result, Some("simple_function".to_string()));
    }

    #[test]
    fn test_simplify_no_args() {
        let demangled = "module.getter()";
        let simple = simplify_function_name(demangled);
        assert_eq!(simple, "getter");
    }

    #[test]
    fn test_simplify_no_module() {
        let demangled = "standalone";
        let simple = simplify_function_name(demangled);
        assert_eq!(simple, "standalone");
    }

    #[test]
    fn test_extract_func_from_mangled() {
        // Test with a custom type that swift-demangle can't handle
        let mangled = "$s16forced_cast_safe8safeCastAA3DogCAA6AnimalCF";
        let func = extract_func_from_mangled(mangled);
        assert_eq!(func, Some("safeCast".to_string()));
    }

    #[test]
    fn test_extract_func_from_mangled_with_underscore_prefix() {
        // Some names have _$s prefix
        let mangled = "_$s16forced_cast_safe8safeCastAA3DogCAA6AnimalCF";
        let func = extract_func_from_mangled(mangled);
        assert_eq!(func, Some("safeCast".to_string()));
    }

    #[test]
    fn test_extract_func_from_mangled_stdlib() {
        // Standard library function should also work
        let mangled = "$s17force_unwrap_safe10safeUnwrapySiSiSgF";
        let func = extract_func_from_mangled(mangled);
        assert_eq!(func, Some("safeUnwrap".to_string()));
    }

    #[test]
    fn test_extract_func_from_mangled_invalid() {
        // Non-mangled names should return None
        let func = extract_func_from_mangled("regularFunctionName");
        assert_eq!(func, None);
    }

    // ============================================================
    // Edge case tests for demangle_batch
    // ============================================================

    #[test]
    fn test_demangle_batch_empty_input() {
        let names: &[&str] = &[];
        let results = demangle_batch(names);
        assert!(results.is_empty());
    }

    #[test]
    fn test_demangle_batch_no_mangled_names() {
        // Names that don't start with $ or _$ should be filtered out
        let names = &["regularName", "another_func", "Module.func"];
        let results = demangle_batch(names);
        assert!(results.is_empty());
    }

    #[test]
    fn test_demangle_batch_mixed_names() {
        // Mix of mangled and non-mangled names
        let names = &["regularName", "$s8test_sil3addyS2i_SitF", "unmangled"];
        let results = demangle_batch(names);
        // Only the mangled name should have been processed
        // Result depends on xcrun availability, but count should be <= 1
        assert!(results.len() <= 1);
    }

    // ============================================================
    // Edge case tests for simplify_function_name
    // ============================================================

    #[test]
    fn test_simplify_nested_modules() {
        // Multiple dots - nested module path
        let demangled = "Swift.Array.Element.getter(Int) -> String";
        let simple = simplify_function_name(demangled);
        assert_eq!(simple, "getter");
    }

    #[test]
    fn test_simplify_deeply_nested_modules() {
        // Very deep nesting
        let demangled = "Foundation.URLSession.Configuration.default.makeURL(String) -> URL";
        let simple = simplify_function_name(demangled);
        assert_eq!(simple, "makeURL");
    }

    #[test]
    fn test_simplify_with_generic_types() {
        // Generic type parameters in signature
        let demangled = "Swift.Array<Int>.append(Swift.Array<Int>.Element) -> ()";
        let simple = simplify_function_name(demangled);
        assert_eq!(simple, "append");
    }

    #[test]
    fn test_simplify_empty_string() {
        let simple = simplify_function_name("");
        assert_eq!(simple, "");
    }

    #[test]
    fn test_simplify_just_dot() {
        let simple = simplify_function_name(".");
        assert_eq!(simple, "");
    }

    #[test]
    fn test_simplify_just_parens() {
        let simple = simplify_function_name("()");
        assert_eq!(simple, "");
    }

    #[test]
    fn test_simplify_only_dot_before_parens() {
        let simple = simplify_function_name(".(Int)");
        assert_eq!(simple, "");
    }

    // ============================================================
    // Edge case tests for to_qualified_name
    // ============================================================

    #[test]
    fn test_to_qualified_name_no_args() {
        let demangled = "module.getter()";
        let qualified = to_qualified_name(demangled);
        assert_eq!(qualified, "module.getter()");
    }

    #[test]
    fn test_to_qualified_name_single_arg() {
        let demangled = "module.process(Int) -> Void";
        let qualified = to_qualified_name(demangled);
        assert_eq!(qualified, "module.process(_:)");
    }

    #[test]
    fn test_to_qualified_name_three_args() {
        let demangled = "module.range(Int, Int, Int) -> Range";
        let qualified = to_qualified_name(demangled);
        assert_eq!(qualified, "module.range(_:_:_:)");
    }

    #[test]
    fn test_to_qualified_name_no_parens() {
        // Property or constant without parentheses
        let demangled = "module.constant";
        let qualified = to_qualified_name(demangled);
        assert_eq!(qualified, "module.constant");
    }

    #[test]
    fn test_to_qualified_name_unclosed_paren() {
        // Malformed - opening paren but no closing
        let demangled = "module.func(Int, String";
        let qualified = to_qualified_name(demangled);
        // Should return with empty parens since no closing paren found
        assert_eq!(qualified, "module.func()");
    }

    #[test]
    fn test_to_qualified_name_empty_string() {
        let qualified = to_qualified_name("");
        assert_eq!(qualified, "");
    }

    #[test]
    fn test_to_qualified_name_nested_types() {
        // Arguments containing commas within generic brackets
        let demangled = "module.transform(Dictionary<String, Int>) -> Array";
        let qualified = to_qualified_name(demangled);
        // The comma inside `Dictionary<_, _>` should not count as an argument separator.
        assert_eq!(qualified, "module.transform(_:)");
    }

    #[test]
    fn test_to_qualified_name_tuple_arg() {
        // A tuple type is a single argument, even though it contains a comma.
        let demangled = "module.f((Swift.Int, Swift.Int)) -> Void";
        let qualified = to_qualified_name(demangled);
        assert_eq!(qualified, "module.f(_:)");
    }

    #[test]
    fn test_to_qualified_name_function_type_arg() {
        // A function type argument can contain tuple commas, and the closing paren must match.
        let demangled = "module.apply((Swift.Int, Swift.Int) -> Swift.Int, Swift.Int) -> Void";
        let qualified = to_qualified_name(demangled);
        assert_eq!(qualified, "module.apply(_:_:)");
    }

    #[test]
    fn test_to_qualified_name_generic_type_and_two_args() {
        // Top-level comma still separates arguments even if one argument is generic.
        let demangled = "module.map(Dictionary<String, Int>, Int) -> Void";
        let qualified = to_qualified_name(demangled);
        assert_eq!(qualified, "module.map(_:_:)");
    }

    // ============================================================
    // Edge case tests for extract_func_from_mangled
    // ============================================================

    #[test]
    fn test_extract_func_empty_string() {
        let func = extract_func_from_mangled("");
        assert_eq!(func, None);
    }

    #[test]
    fn test_extract_func_just_prefix() {
        // Just the prefix with no content
        let func = extract_func_from_mangled("$s");
        assert_eq!(func, None);
    }

    #[test]
    fn test_extract_func_no_func_length() {
        // Module but no function length/name after it
        let func = extract_func_from_mangled("$s4test");
        assert_eq!(func, None);
    }

    #[test]
    fn test_extract_func_truncated_module() {
        // Module length says 10 but only 4 chars follow
        let func = extract_func_from_mangled("$s10test");
        assert_eq!(func, None);
    }

    #[test]
    fn test_extract_func_truncated_func_name() {
        // Module is complete but function name is truncated
        let func = extract_func_from_mangled("$s4test10funcXYZ");
        assert_eq!(func, None);
    }

    #[test]
    fn test_extract_func_short_names() {
        // Very short module and function names
        let mangled = "$s1a1bF";
        let func = extract_func_from_mangled(mangled);
        assert_eq!(func, Some("b".to_string()));
    }

    #[test]
    fn test_extract_func_with_numbers_in_name() {
        // Function name containing numbers
        let mangled = "$s5hello7func123XYZ";
        let func = extract_func_from_mangled(mangled);
        assert_eq!(func, Some("func123".to_string()));
    }

    #[test]
    fn test_extract_func_with_underscores() {
        // Function name containing underscores
        let mangled = "$s6module9my_func_1ABC";
        let func = extract_func_from_mangled(mangled);
        assert_eq!(func, Some("my_func_1".to_string()));
    }

    #[test]
    fn test_extract_func_special_chars_rejected() {
        // Function name with special characters (not alphanumeric/underscore)
        // The validation should reject names with characters like '-', '$', etc.
        // Using a valid length prefix but invalid function name chars
        let mangled = "$s4test4ab-cXYZ";
        let func = extract_func_from_mangled(mangled);
        // The '-' is not ASCII alphanumeric or underscore, so should fail validation
        assert_eq!(func, None);
    }

    // ============================================================
    // Edge case tests for demangle function
    // ============================================================

    #[test]
    fn test_demangle_underscore_dollar_prefix() {
        // Names starting with _$ should be recognized as mangled
        let mangled = "_$s8test_sil3addyS2i_SitF";
        let result = demangle(mangled);
        // If xcrun is available, this should demangle
        // If not, it returns None
        if let Some(demangled) = result {
            assert!(demangled.contains("add") || demangled.contains("test_sil"));
        }
    }

    #[test]
    fn test_demangle_caches_results() {
        // Call demangle twice on same input - second should use cache
        let mangled = "$s8test_sil3addyS2i_SitF";
        let result1 = demangle(mangled);
        let result2 = demangle(mangled);
        assert_eq!(result1, result2);
    }

    #[test]
    fn test_demangle_different_mangled_names() {
        // Different mangled names should produce different results (if demangled)
        let mangled1 = "$s8test_sil3addyS2i_SitF";
        let mangled2 = "$s8test_sil3subyS2i_SitF";
        let result1 = demangle(mangled1);
        let result2 = demangle(mangled2);
        // Results may both be None if xcrun unavailable, but if both succeed they differ
        if let (Some(r1), Some(r2)) = (result1, result2) {
            // Both should contain different function names
            assert!(r1 != r2 || r1.contains("add") != r2.contains("add"));
        }
    }

    // ============================================================
    // Additional parse_length_prefix tests (via extract_func_from_mangled)
    // ============================================================

    #[test]
    fn test_extract_func_zero_length_module() {
        // Zero-length module name: $s0<func_len><func_name>
        // Note: "04" parses as 4, not 0. To get zero-length, need "0" followed by non-digit.
        // In practice, zero-length module names are unusual.
        // With "$s04test..." the parser sees module length=4, name="test"
        // Let's test a case with 0-length module using $s0X... pattern
        // Since 0 parses as 0, then next char is non-digit for func length
        // Actually parse_length_prefix("0X4func") returns (0, "X4func")
        // Then we try to take 0 chars from "X4func" leaving "X4func"
        // Then parse_length_prefix("X4func") fails because X is not a digit
        // So zero-length module can't work with our parser - returns None
        let mangled = "$s04testXXXX"; // "04" parses as 4
        let func = extract_func_from_mangled(mangled);
        // Module="test", then "XXXX" - no digit prefix for func length
        assert_eq!(func, None);
    }

    #[test]
    fn test_extract_func_zero_length_function() {
        // Zero-length function name should be rejected
        let mangled = "$s4test0F"; // 4-char module "test", 0-char func
        let func = extract_func_from_mangled(mangled);
        assert_eq!(func, None);
    }

    // ============================================================
    // parse_xcrun_demangle_line tests
    // ============================================================

    #[test]
    fn test_parse_xcrun_demangle_line_without_arrow() {
        assert_eq!(parse_xcrun_demangle_line("PlainOutput"), "PlainOutput");
    }

    #[test]
    fn test_parse_xcrun_demangle_line_with_arrow() {
        let line = "$s8test_sil3addyS2i_SitF ---> test_sil.add(Swift.Int, Swift.Int) -> Swift.Int";
        assert_eq!(
            parse_xcrun_demangle_line(line),
            "test_sil.add(Swift.Int, Swift.Int) -> Swift.Int"
        );
    }

    #[test]
    fn test_parse_xcrun_demangle_line_trims_whitespace() {
        let line = "  $sFoo --->  Module.func()  ";
        assert_eq!(parse_xcrun_demangle_line(line), "Module.func()");
    }

    #[test]
    fn test_extract_func_large_length_prefix() {
        // Large multi-digit length prefix
        let mangled = "$s100aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa5funcXXYZ";
        let func = extract_func_from_mangled(mangled);
        assert_eq!(func, Some("funcX".to_string()));
    }

    #[test]
    fn test_extract_func_only_length_no_content() {
        // Length prefix says 5 but no characters follow
        let func = extract_func_from_mangled("$s5");
        assert_eq!(func, None);
    }

    #[test]
    fn test_extract_func_double_digit_lengths() {
        // Both module and function have double-digit lengths
        // "helloworld" = 10 chars, "veryLongFuncName" = 16 chars
        let mangled = "$s10helloworld16veryLongFuncNameXXX";
        let func = extract_func_from_mangled(mangled);
        assert_eq!(func, Some("veryLongFuncName".to_string()));
    }

    #[test]
    fn test_extract_func_leading_zero_in_length() {
        // Leading zeros in length: "08" should parse as 8, not octal
        let mangled = "$s08testmodl04testXYZ"; // module "testmodl" (8 chars), func "test" (4 chars)
        let func = extract_func_from_mangled(mangled);
        assert_eq!(func, Some("test".to_string()));
    }

    #[test]
    fn test_extract_func_max_length_edge() {
        // Length exactly matches remaining string
        let mangled = "$s3abc3xyz"; // module "abc", func "xyz", nothing after
        let func = extract_func_from_mangled(mangled);
        assert_eq!(func, Some("xyz".to_string()));
    }

    // ============================================================
    // Additional demangle_batch tests
    // ============================================================

    #[test]
    fn test_demangle_batch_only_underscore_dollar_prefix() {
        // Names starting with _$ should be recognized
        let names = &["_$s8test_sil3addyS2i_SitF"];
        let results = demangle_batch(names);
        // Might succeed or fail depending on xcrun
        assert!(results.len() <= 1);
    }

    #[test]
    fn test_demangle_batch_many_mangled() {
        // Multiple mangled names
        let names = &[
            "$s8test_sil3addyS2i_SitF",
            "$s8test_sil3subyS2i_SitF",
            "$s8test_sil3mulyS2i_SitF",
        ];
        let results = demangle_batch(names);
        // Result count depends on xcrun availability
        assert!(results.len() <= 3);
    }

    #[test]
    fn test_demangle_batch_duplicate_names() {
        // Same mangled name multiple times
        let names = &["$s8test_sil3addyS2i_SitF", "$s8test_sil3addyS2i_SitF"];
        let results = demangle_batch(names);
        // Should only produce one entry (HashMap deduplicates)
        assert!(results.len() <= 1);
    }

    // ============================================================
    // Additional simplify_function_name tests
    // ============================================================

    #[test]
    fn test_simplify_operator_name() {
        // Operators might have special formats
        let demangled = "Swift.Int.==(_:_:)";
        let simple = simplify_function_name(demangled);
        // The '(' appears after ==, so == should be extracted
        assert_eq!(simple, "==");
    }

    #[test]
    fn test_simplify_subscript() {
        let demangled = "Module.Type.subscript(Int) -> Element";
        let simple = simplify_function_name(demangled);
        assert_eq!(simple, "subscript");
    }

    #[test]
    fn test_simplify_init() {
        let demangled = "Module.Type.init(String) -> Type";
        let simple = simplify_function_name(demangled);
        assert_eq!(simple, "init");
    }

    #[test]
    fn test_simplify_deinit() {
        let demangled = "Module.Type.deinit";
        let simple = simplify_function_name(demangled);
        assert_eq!(simple, "deinit");
    }

    #[test]
    fn test_simplify_computed_property_getter() {
        let demangled = "Module.Type.property.getter";
        let simple = simplify_function_name(demangled);
        assert_eq!(simple, "getter");
    }

    #[test]
    fn test_simplify_with_closure_number() {
        // Closures may have special names
        let demangled = "Module.func(Int).closure#1";
        let simple = simplify_function_name(demangled);
        // Everything before '(' is taken, then last dot
        assert_eq!(simple, "func");
    }

    #[test]
    fn test_simplify_only_module() {
        // Just a module name with no function
        let demangled = "MyModule";
        let simple = simplify_function_name(demangled);
        assert_eq!(simple, "MyModule");
    }

    #[test]
    fn test_simplify_trailing_dots() {
        let demangled = "Module.func.";
        let simple = simplify_function_name(demangled);
        // Last component after final dot is empty
        assert_eq!(simple, "");
    }

    // ============================================================
    // Additional to_qualified_name tests
    // ============================================================

    #[test]
    fn test_to_qualified_name_many_args() {
        let demangled = "module.func(A, B, C, D, E) -> F";
        let qualified = to_qualified_name(demangled);
        assert_eq!(qualified, "module.func(_:_:_:_:_:)");
    }

    #[test]
    fn test_to_qualified_name_whitespace_in_args() {
        // Arguments with spaces (like "Array<Int, Int>")
        let demangled = "module.func(Array<Int, Int>) -> Void";
        let qualified = to_qualified_name(demangled);
        // The comma inside `Array<_, _>` should not count as an argument separator.
        assert_eq!(qualified, "module.func(_:)");
    }

    #[test]
    fn test_to_qualified_name_multiple_parens() {
        // Function returning function type
        let demangled = "module.curry(Int) -> (Int) -> Int";
        let qualified = to_qualified_name(demangled);
        // First () pair is used
        assert_eq!(qualified, "module.curry(_:)");
    }

    #[test]
    fn test_to_qualified_name_closure_arg() {
        // Closure as argument: (Int) -> Int counts as 2 with naive parsing
        let demangled = "module.map((Int) -> String) -> [String]";
        let qualified = to_qualified_name(demangled);
        // The first paren starts a "closure type" - naive parsing sees empty before inner (
        assert_eq!(qualified, "module.map(_:)");
    }

    #[test]
    fn test_to_qualified_name_just_parens_no_module() {
        let demangled = "standalone()";
        let qualified = to_qualified_name(demangled);
        assert_eq!(qualified, "standalone()");
    }

    #[test]
    fn test_to_qualified_name_args_only_spaces() {
        // Edge case: args section is just whitespace
        let demangled = "module.func(   ) -> Void";
        let qualified = to_qualified_name(demangled);
        // Treat whitespace-only argument lists as empty.
        assert_eq!(qualified, "module.func()");
    }

    // ============================================================
    // Additional extract_func_from_mangled tests
    // ============================================================

    #[test]
    fn test_extract_func_all_digits_in_name() {
        // Function name that's all digits (valid alphanumeric)
        let mangled = "$s4test312345678901234567890WXYZ";
        let func = extract_func_from_mangled(mangled);
        // 31 chars: "12345678901234567890WXYZ" but wait, that's 24 chars
        // Let me recalculate: module="test"(4), func length=31 but not enough chars
        // Actually 31 > "2345678901234567890WXYZ".len() which is 22
        // This should return None
        assert_eq!(func, None);
    }

    #[test]
    fn test_extract_func_valid_all_digits_name() {
        // Function name that's all digits (valid) with correct length
        // Challenge: If func name is "123", the length would be "3" but then "123"
        // gets parsed as length 123. To have an all-digit func name, the parser
        // needs a clear boundary. In practice, Swift mangled names don't have
        // all-digit function names. Let's test that attempting it fails.
        let mangled = "$s4test3123F"; // module="test", then "3123F" - parses as len=3123
        let func = extract_func_from_mangled(mangled);
        // 3123 > "F".len(), so returns None
        assert_eq!(func, None);
    }

    #[test]
    fn test_extract_func_mixed_case_module() {
        let mangled = "$s12MyModuleName8funcNameABC";
        let func = extract_func_from_mangled(mangled);
        assert_eq!(func, Some("funcName".to_string()));
    }

    #[test]
    fn test_extract_func_dollar_only() {
        // Just "$" without "s"
        let func = extract_func_from_mangled("$");
        assert_eq!(func, None);
    }

    #[test]
    fn test_extract_func_underscore_dollar_only() {
        // Just "_$" without "s"
        let func = extract_func_from_mangled("_$");
        assert_eq!(func, None);
    }

    #[test]
    fn test_extract_func_underscore_dollar_s_only() {
        // Just "_$s" with nothing after
        let func = extract_func_from_mangled("_$s");
        assert_eq!(func, None);
    }

    #[test]
    fn test_extract_func_single_char_module_and_func() {
        // Minimal valid: 1-char module, 1-char func
        let mangled = "$s1X1Y";
        let func = extract_func_from_mangled(mangled);
        assert_eq!(func, Some("Y".to_string()));
    }

    #[test]
    fn test_extract_func_with_trailing_suffix() {
        // Real mangled names have suffixes after the func name
        // "MyModule" = 8 chars, "myFunction" = 10 chars
        let mangled = "$s8MyModule10myFunctionyyF"; // suffix "yyF"
        let func = extract_func_from_mangled(mangled);
        assert_eq!(func, Some("myFunction".to_string()));
    }

    // ============================================================
    // Additional demangle tests
    // ============================================================

    #[test]
    fn test_demangle_plain_name_no_prefix() {
        // Names without $ or _$ should return as-is
        let name = "myFunction";
        let result = demangle(name);
        assert_eq!(result, Some("myFunction".to_string()));
    }

    #[test]
    fn test_demangle_empty_string() {
        // Empty string is not mangled
        let result = demangle("");
        assert_eq!(result, Some(String::new()));
    }

    #[test]
    fn test_demangle_just_dollar() {
        // Just "$" is not a valid mangled name but doesn't start with "$s"
        // Our check is starts_with('$'), so this goes to xcrun
        let result = demangle("$");
        // xcrun will likely fail, so None or the original
        // The function tries xcrun and returns None if it fails
        assert!(result.is_none() || result == Some("$".to_string()));
    }

    #[test]
    fn test_demangle_underscore_alone() {
        // "_" doesn't start with $ or _$, so returns as-is
        let result = demangle("_");
        assert_eq!(result, Some("_".to_string()));
    }

    #[test]
    fn test_demangle_underscore_dollar_not_s() {
        // "_$x" starts with _$ but isn't "_$s", still mangled
        let result = demangle("_$x");
        // Goes to xcrun, likely fails
        assert!(result.is_none() || result == Some("_$x".to_string()));
    }

    #[test]
    fn test_demangle_whitespace_name() {
        // Whitespace doesn't start with $ or _$
        let result = demangle("  ");
        assert_eq!(result, Some("  ".to_string()));
    }

    #[test]
    fn test_demangle_unicode_name() {
        // Unicode name without mangling prefix
        let result = demangle("関数");
        assert_eq!(result, Some("関数".to_string()));
    }

    // ============================================================
    // Cache behavior tests
    // ============================================================

    #[test]
    fn test_demangle_cache_hit_for_unmangled() {
        // Unmangled names aren't cached (early return)
        // Call twice to ensure no issues
        let name = "simpleName";
        let r1 = demangle(name);
        let r2 = demangle(name);
        assert_eq!(r1, r2);
        assert_eq!(r1, Some("simpleName".to_string()));
    }

    #[test]
    fn test_demangle_cache_consistency() {
        // Multiple calls to same mangled name should return consistent results
        let mangled = "$s4test4funcF";
        let r1 = demangle(mangled);
        let r2 = demangle(mangled);
        let r3 = demangle(mangled);
        assert_eq!(r1, r2);
        assert_eq!(r2, r3);
    }

    // ============================================================
    // Complex name tests
    // ============================================================

    #[test]
    fn test_simplify_nested_generic_type_param() {
        let demangled =
            "Swift.Array<Swift.Dictionary<Swift.String, Swift.Int>>.append(Element) -> ()";
        let simple = simplify_function_name(demangled);
        assert_eq!(simple, "append");
    }

    #[test]
    fn test_to_qualified_name_extension_method() {
        // Extension methods have format like "Module.Type.method"
        let demangled = "Swift.String.hasPrefix(String) -> Bool";
        let qualified = to_qualified_name(demangled);
        assert_eq!(qualified, "Swift.String.hasPrefix(_:)");
    }

    #[test]
    fn test_simplify_protocol_witness() {
        // Protocol witness tables have special names
        let demangled = "protocol witness for Module.Protocol.method() in conformance Module.Type : Module.Protocol";
        let simple = simplify_function_name(demangled);
        // "method" comes before the first (
        assert_eq!(simple, "method");
    }

    #[test]
    fn test_to_qualified_name_labeled_args() {
        // Swift functions can have labeled arguments
        // This tests the generic handling (our impl doesn't track labels)
        let demangled = "Module.func(with: Int, and: String) -> Void";
        let qualified = to_qualified_name(demangled);
        // Naive comma split sees "with: Int" and "and: String" as 2 args
        assert_eq!(qualified, "Module.func(_:_:)");
    }
}
