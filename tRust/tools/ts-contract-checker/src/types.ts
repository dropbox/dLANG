/**
 * TypeScript types for tRust contract export format (Phase 6.5.6)
 *
 * These types correspond to the JSON format exported by rustc_verify/src/contract_export.rs
 */

/** Root structure for exported contracts */
export interface ContractExport {
  version: string;
  crate_name: string;
  timestamp: string;
  contracts: ExportedContract[];
  types: Record<string, ExportedType>;
}

/** A single exported function contract */
export interface ExportedContract {
  function: string;
  module: string;
  visibility: "public" | "crate" | "private";
  api_metadata?: ApiMetadata;
  requires: ExportedClause[];
  ensures: ExportedClause[];
  params: ExportedParam[];
  return_type: string;
  pure: boolean;
  effects: string[];
  location?: ExportedLocation;
}

/** API metadata for HTTP endpoints */
export interface ApiMetadata {
  path: string;
  method: string;
}

/** A single contract clause (requires or ensures) */
export interface ExportedClause {
  expr: string;
  label?: string;
}

/** A function parameter */
export interface ExportedParam {
  name: string;
  type: string;
  refined?: string;
}

/** A type definition */
export interface ExportedType {
  kind: "struct" | "enum" | "alias";
  fields: ExportedField[];
  underlying?: string;
  refined?: string;
}

/** A struct field or enum variant */
export interface ExportedField {
  name: string;
  type?: string;
}

/** Source location for error reporting */
export interface ExportedLocation {
  file: string;
  line: number;
  column: number;
}

/** Result of checking a TypeScript file against contracts */
export interface CheckResult {
  file: string;
  violations: ContractViolation[];
  warnings: ContractWarning[];
}

/** A contract violation found in TypeScript code */
export interface ContractViolation {
  type: "missing_precondition" | "type_mismatch" | "wrong_endpoint";
  contract: ExportedContract;
  location: { line: number; column: number };
  message: string;
  suggestion?: string;
}

/** A warning about potential contract issues */
export interface ContractWarning {
  type: "unverified_precondition" | "missing_error_handling" | "deprecated_api";
  contract?: ExportedContract;
  location: { line: number; column: number };
  message: string;
}
