/**
 * TypeScript contract checker
 *
 * Parses TypeScript files and checks fetch/API calls against Rust contracts
 */

import * as fs from "fs";
import {
  ContractExport,
  ExportedContract,
  CheckResult,
  ContractViolation,
  ContractWarning,
} from "./types";
import { buildApiContractMap, buildFunctionContractMap } from "./loader";

/** Parsed fetch call from TypeScript */
interface ParsedFetchCall {
  url: string;
  method: string;
  body?: string;
  line: number;
  column: number;
}

/**
 * Extract constant definitions from TypeScript source
 * Looks for patterns like: const API_BASE = "/api"
 */
function extractConstants(content: string): Map<string, string> {
  const constants = new Map<string, string>();
  const constRegex = /const\s+(\w+)\s*=\s*["'`]([^"'`]+)["'`]/g;
  let match;
  while ((match = constRegex.exec(content)) !== null) {
    constants.set(match[1], match[2]);
  }
  return constants;
}

/**
 * Resolve template literal with known constants
 * Handles patterns like: ${API_BASE}/users
 */
function resolveTemplateUrl(template: string, constants: Map<string, string>): string {
  return template.replace(/\$\{(\w+)\}/g, (_, name) => {
    return constants.get(name) || `\${${name}}`;
  });
}

/** Parsed API call pattern */
interface ApiCallPattern {
  pattern: string;
  method: string;
  validation?: string;
  line: number;
  column: number;
}

/**
 * Check a TypeScript file against contracts
 */
export function checkTypeScriptFile(
  filePath: string,
  contracts: ContractExport
): CheckResult {
  const content = fs.readFileSync(filePath, "utf-8");
  const lines = content.split("\n");

  const violations: ContractViolation[] = [];
  const warnings: ContractWarning[] = [];

  const apiMap = buildApiContractMap(contracts);
  const fnMap = buildFunctionContractMap(contracts);

  // Extract constants for template resolution
  const constants = extractConstants(content);

  // Parse fetch calls
  const fetchCalls = parseFetchCalls(content, constants);

  for (const call of fetchCalls) {
    checkFetchCall(call, apiMap, fnMap, contracts, violations, warnings);
  }

  // Parse general API patterns (axios, etc.)
  const apiPatterns = parseApiPatterns(content);

  for (const pattern of apiPatterns) {
    checkApiPattern(pattern, apiMap, contracts, violations, warnings);
  }

  // Check for missing error handling on API calls
  checkErrorHandling(content, lines, warnings);

  return {
    file: filePath,
    violations,
    warnings,
  };
}

/**
 * Parse fetch() calls from TypeScript source
 * Handles both single-line and multi-line fetch calls with template literals
 */
function parseFetchCalls(content: string, constants: Map<string, string>): ParsedFetchCall[] {
  const calls: ParsedFetchCall[] = [];
  const lines = content.split("\n");

  // First pass: find fetch calls and extract URLs (handles template literals)
  // Pattern matches: fetch(`url`, or fetch("url", or fetch('url',
  const fetchStartRegex = /fetch\s*\(\s*["'`]([^"'`]*(?:\$\{[^}]+\}[^"'`]*)*)["'`]\s*,?\s*\{?/g;

  let lineNum = 0;
  for (const line of lines) {
    lineNum++;
    let match;
    while ((match = fetchStartRegex.exec(line)) !== null) {
      // Resolve template literals like ${API_BASE}/users
      const rawUrl = match[1];
      const url = resolveTemplateUrl(rawUrl, constants);

      // Look ahead for method in the next few lines
      const contextLines = lines.slice(lineNum - 1, lineNum + 5).join("\n");
      const methodMatch = contextLines.match(/method\s*:\s*["'`]([^"'`]+)["'`]/);
      const method = methodMatch ? methodMatch[1].toUpperCase() : "GET";

      // Look for body reference - handle JSON.stringify() and similar nested calls
      const bodyMatch = contextLines.match(/body\s*:\s*(JSON\.stringify\s*\([^)]+\)|[^,\n}]+)/);
      const body = bodyMatch ? bodyMatch[1].trim() : undefined;

      calls.push({
        url,
        method,
        body,
        line: lineNum,
        column: match.index + 1,
      });
    }
  }

  return calls;
}

/**
 * Parse general API call patterns (axios, custom clients)
 */
function parseApiPatterns(content: string): ApiCallPattern[] {
  const patterns: ApiCallPattern[] = [];
  const lines = content.split("\n");

  // axios.post("/api/users", data)
  const axiosRegex =
    /axios\.(get|post|put|delete|patch)\s*\(\s*["'`]([^"'`]+)["'`]/gi;

  let lineNum = 0;
  for (const line of lines) {
    lineNum++;
    let match;
    while ((match = axiosRegex.exec(line)) !== null) {
      patterns.push({
        pattern: match[2],
        method: match[1].toUpperCase(),
        line: lineNum,
        column: match.index + 1,
      });
    }
  }

  // api.call("functionName", args) - for RPC-style APIs
  const rpcRegex = /api\.call\s*\(\s*["'`]([^"'`]+)["'`]/gi;
  lineNum = 0;
  for (const line of lines) {
    lineNum++;
    let match;
    while ((match = rpcRegex.exec(line)) !== null) {
      patterns.push({
        pattern: match[1],
        method: "RPC",
        line: lineNum,
        column: match.index + 1,
      });
    }
  }

  return patterns;
}

/**
 * Normalize URL for matching: convert ${var} to {var} for path parameters
 */
function normalizeUrl(url: string): string {
  return url.replace(/\$\{([^}]+)\}/g, "{$1}");
}

/**
 * Check if two URLs match, handling path parameters
 * /api/users/{id} should match /api/users/123 or /api/users/${id}
 */
function urlMatchesPattern(url: string, pattern: string): boolean {
  // Exact match after normalization
  const normalizedUrl = normalizeUrl(url);
  if (normalizedUrl === pattern) return true;

  // Convert pattern to regex for path parameter matching
  const regexPattern = pattern.replace(/\{[^}]+\}/g, "[^/]+");
  const regex = new RegExp(`^${regexPattern}$`);
  return regex.test(url) || regex.test(normalizedUrl);
}

/**
 * Find contracts matching a URL (with path parameter support)
 */
function findMatchingContracts(
  method: string,
  url: string,
  contracts: ContractExport
): ExportedContract[] {
  const matches: ExportedContract[] = [];
  for (const contract of contracts.contracts) {
    if (
      contract.api_metadata &&
      contract.api_metadata.method === method &&
      urlMatchesPattern(url, contract.api_metadata.path)
    ) {
      matches.push(contract);
    }
  }
  return matches;
}

/**
 * Check a fetch call against contracts
 */
function checkFetchCall(
  call: ParsedFetchCall,
  apiMap: Map<string, ExportedContract[]>,
  fnMap: Map<string, ExportedContract>,
  contracts: ContractExport,
  violations: ContractViolation[],
  warnings: ContractWarning[]
): void {
  // Try exact match first
  const key = `${call.method}:${call.url}`;
  let matchingContracts = apiMap.get(key);

  // If no exact match, try pattern matching
  if (!matchingContracts || matchingContracts.length === 0) {
    matchingContracts = findMatchingContracts(call.method, call.url, contracts);
  }

  if (!matchingContracts || matchingContracts.length === 0) {
    // No contract found - check if there's a contract for same URL but different method
    // This helps detect wrong HTTP method errors
    const normalizedUrl = normalizeUrl(call.url);
    const wrongMethodContracts = contracts.contracts.filter(
      (c) =>
        c.api_metadata &&
        c.api_metadata.method !== call.method &&
        urlMatchesPattern(normalizedUrl, c.api_metadata.path)
    );

    if (wrongMethodContracts.length > 0) {
      // List all available methods for this endpoint
      const availableMethods = wrongMethodContracts
        .map((c) => c.api_metadata?.method)
        .filter((m): m is string => !!m);
      const methodList = availableMethods.join(" or ");

      violations.push({
        type: "wrong_endpoint",
        contract: wrongMethodContracts[0],
        location: { line: call.line, column: call.column },
        message: `Wrong HTTP method: expected ${methodList}, got ${call.method}`,
        suggestion: `Use ${methodList} instead of ${call.method}`,
      });
    } else if (call.url.startsWith("/api/")) {
      warnings.push({
        type: "unverified_precondition",
        location: { line: call.line, column: call.column },
        message: `No contract found for ${call.method} ${call.url}`,
      });
    }
    return;
  }

  for (const contract of matchingContracts) {
    // Check preconditions
    for (const req of contract.requires) {
      // Simple heuristic: check if the precondition references a parameter
      // that should be validated before the API call
      const paramCheck = checkPreconditionCoverage(call, req.expr, contract);
      if (!paramCheck.covered) {
        warnings.push({
          type: "unverified_precondition",
          contract,
          location: { line: call.line, column: call.column },
          message: `Precondition "${req.expr}" may not be validated before call`,
        });
      }
    }
  }
}

/**
 * Check an API pattern against contracts
 */
function checkApiPattern(
  pattern: ApiCallPattern,
  apiMap: Map<string, ExportedContract[]>,
  contracts: ContractExport,
  violations: ContractViolation[],
  warnings: ContractWarning[]
): void {
  // For RPC-style calls, look up by function name
  if (pattern.method === "RPC") {
    // Find contract by pattern matching
    const matching = contracts.contracts.filter(
      (c) =>
        c.function.endsWith(pattern.pattern) ||
        c.function.includes(pattern.pattern)
    );

    if (matching.length === 0) {
      warnings.push({
        type: "unverified_precondition",
        location: { line: pattern.line, column: pattern.column },
        message: `No contract found for RPC call to "${pattern.pattern}"`,
      });
    }
    return;
  }

  // For REST-style calls
  const key = `${pattern.method}:${pattern.pattern}`;
  const matchingContracts = apiMap.get(key);

  if (!matchingContracts || matchingContracts.length === 0) {
    if (pattern.pattern.startsWith("/api/")) {
      warnings.push({
        type: "unverified_precondition",
        location: { line: pattern.line, column: pattern.column },
        message: `No contract found for ${pattern.method} ${pattern.pattern}`,
      });
    }
  }
}

/**
 * Check if a precondition is covered by the calling code
 *
 * This is a simplified heuristic - a production implementation would
 * use proper TypeScript AST analysis.
 *
 * Conservative approach: only mark as covered if we see actual validation.
 * Just having a parameter in the body is NOT sufficient - that's just usage.
 */
function checkPreconditionCoverage(
  _call: ParsedFetchCall,
  _precondition: string,
  _contract: ExportedContract
): { covered: boolean; reason?: string } {
  // Conservative: always report as not covered
  // A proper implementation would analyze the function body for validation patterns like:
  // - if (param >= 18) or if (param > 0)
  // - throw new Error() for invalid values
  // - validation library calls
  //
  // For this prototype, we over-report to avoid missing real violations.
  // False positives can be suppressed with inline comments or config.
  return { covered: false, reason: "no validation analysis (prototype)" };
}

/**
 * Check for missing error handling on API calls
 */
function checkErrorHandling(
  content: string,
  lines: string[],
  warnings: ContractWarning[]
): void {
  let lineNum = 0;

  for (const line of lines) {
    lineNum++;

    // Check for fetch without catch/then error handling
    if (
      line.includes("fetch(") &&
      !line.includes(".catch") &&
      !line.includes("try")
    ) {
      // Look ahead a few lines for error handling
      const context = lines.slice(lineNum - 1, lineNum + 3).join("\n");
      if (!context.includes(".catch") && !context.includes("try {")) {
        warnings.push({
          type: "missing_error_handling",
          location: { line: lineNum, column: 1 },
          message: "fetch() call without error handling",
        });
      }
    }

    // Check for axios without catch
    if (
      line.includes("axios.") &&
      !line.includes(".catch") &&
      !line.includes("try")
    ) {
      const context = lines.slice(lineNum - 1, lineNum + 3).join("\n");
      if (!context.includes(".catch") && !context.includes("try {")) {
        warnings.push({
          type: "missing_error_handling",
          location: { line: lineNum, column: 1 },
          message: "axios call without error handling",
        });
      }
    }
  }
}

/**
 * Format check results for display
 */
export function formatResults(results: CheckResult[]): string {
  const lines: string[] = [];

  let totalViolations = 0;
  let totalWarnings = 0;

  for (const result of results) {
    totalViolations += result.violations.length;
    totalWarnings += result.warnings.length;

    if (result.violations.length > 0 || result.warnings.length > 0) {
      lines.push(`\n${result.file}:`);

      for (const v of result.violations) {
        lines.push(
          `  ERROR [${v.location.line}:${v.location.column}] ${v.type}: ${v.message}`
        );
        if (v.suggestion) {
          lines.push(`    Suggestion: ${v.suggestion}`);
        }
      }

      for (const w of result.warnings) {
        lines.push(
          `  WARN [${w.location.line}:${w.location.column}] ${w.type}: ${w.message}`
        );
      }
    }
  }

  lines.push("\n---");
  lines.push(
    `Total: ${totalViolations} error(s), ${totalWarnings} warning(s)`
  );

  return lines.join("\n");
}
