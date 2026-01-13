/*===--- vc_bridge.h - C FFI for tSwift VC IR Bridge ---*- C -*-============*\
|*                                                                            *|
|* This source file is part of the tSwift project                              *|
|*                                                                            *|
|* Copyright (c) 2026 Dropbox, Inc. All rights reserved.                       *|
|* Licensed under Apache License v2.0                                          *|
|*                                                                            *|
\*============================================================================*/

/**
 * @file vc_bridge.h
 * @brief C FFI for the tSwift VC IR Bridge library.
 *
 * This header provides the C API for bridging tSwift verification conditions
 * (in JSON format) to the tRust VC IR format for verification.
 *
 * ## Usage
 *
 * 1. Build your verification bundle as JSON
 * 2. Call `vc_bridge_verify_json()` with the JSON string
 * 3. Parse the JSON response for results
 * 4. Free the response string with `vc_bridge_free_string()`
 *
 * ## Example
 *
 * ```c
 * const char* json = "{\"function_name\":\"test\",\"requires\":[],\"ensures\":[]}";
 * char* result = vc_bridge_verify_json(json);
 * // Parse result JSON...
 * vc_bridge_free_string(result);
 * ```
 */

#ifndef VC_BRIDGE_H
#define VC_BRIDGE_H

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Opaque type for a parsed Swift VC bundle.
 *
 * This is used with the low-level parse/convert/free API.
 * For most use cases, prefer the high-level `vc_bridge_verify_json()` API.
 */
typedef struct SwiftVcBundle SwiftVcBundle;

/**
 * Parse a JSON string into a SwiftVcBundle.
 *
 * @param json A null-terminated JSON string containing a SwiftVcBundle.
 * @return A pointer to the parsed bundle, or NULL on error.
 *         Must be freed with `vc_bridge_free_bundle()`.
 */
SwiftVcBundle* vc_bridge_parse_bundle(const char* json);

/**
 * Free a SwiftVcBundle allocated by `vc_bridge_parse_bundle()`.
 *
 * @param bundle The bundle to free. If NULL, this function does nothing.
 */
void vc_bridge_free_bundle(SwiftVcBundle* bundle);

/**
 * Convert a SwiftVcBundle to VC IR and return summary as JSON.
 *
 * @param bundle A pointer to a parsed SwiftVcBundle.
 * @return A JSON string summarizing the conversion, or an error JSON object.
 *         Must be freed with `vc_bridge_free_string()`.
 */
char* vc_bridge_convert_to_vcir(const SwiftVcBundle* bundle);

/**
 * Verify a SwiftVcBundle and return results as JSON.
 *
 * This is the main entry point for verification. It:
 * 1. Parses the JSON into a SwiftVcBundle
 * 2. Converts to VC IR
 * 3. Runs verification using the configured backend
 * 4. Returns results as JSON
 *
 * @param json A null-terminated JSON string containing a SwiftVcBundle.
 * @return A JSON string containing the verification results,
 *         or an error JSON object if verification fails.
 *         Must be freed with `vc_bridge_free_string()`.
 *
 * ## Response Format
 *
 * On success:
 * ```json
 * {
 *   "function_name": "test",
 *   "spec_result": {"result": "Verified", "time_seconds": 0.05},
 *   "auto_vc_results": [],
 *   "summary": {"total_vcs": 1, "verified": 1, "failed": 0, ...}
 * }
 * ```
 *
 * On error:
 * ```json
 * {"error": "error message"}
 * ```
 */
char* vc_bridge_verify_json(const char* json);

/**
 * Free a string allocated by the bridge library.
 *
 * @param s The string to free. If NULL, this function does nothing.
 */
void vc_bridge_free_string(char* s);

/**
 * Get the version of the bridge library.
 *
 * @return A statically allocated version string (do not free).
 */
const char* vc_bridge_version(void);

#ifdef __cplusplus
}
#endif

#endif /* VC_BRIDGE_H */
