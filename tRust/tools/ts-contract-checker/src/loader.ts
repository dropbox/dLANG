/**
 * Contract loader for tRust exported contracts
 */

import * as fs from "fs";
import * as path from "path";
import { ContractExport, ExportedContract } from "./types";

/**
 * Load contracts from a JSON file
 */
export function loadContracts(contractPath: string): ContractExport {
  const absolutePath = path.resolve(contractPath);

  if (!fs.existsSync(absolutePath)) {
    throw new Error(`Contract file not found: ${absolutePath}`);
  }

  const content = fs.readFileSync(absolutePath, "utf-8");
  const contracts = JSON.parse(content) as ContractExport;

  // Validate version
  if (!contracts.version) {
    throw new Error("Invalid contract file: missing version");
  }

  if (contracts.version !== "1.0") {
    console.warn(
      `Warning: Contract version ${contracts.version} may not be fully compatible`
    );
  }

  return contracts;
}

/**
 * Build a lookup map from API path to contracts
 */
export function buildApiContractMap(
  contracts: ContractExport
): Map<string, ExportedContract[]> {
  const map = new Map<string, ExportedContract[]>();

  for (const contract of contracts.contracts) {
    if (contract.api_metadata?.path) {
      const key = `${contract.api_metadata.method}:${contract.api_metadata.path}`;
      const existing = map.get(key) || [];
      existing.push(contract);
      map.set(key, existing);
    }
  }

  return map;
}

/**
 * Build a lookup map from function name to contract
 */
export function buildFunctionContractMap(
  contracts: ContractExport
): Map<string, ExportedContract> {
  const map = new Map<string, ExportedContract>();

  for (const contract of contracts.contracts) {
    map.set(contract.function, contract);

    // Also add short name (without module prefix)
    const shortName = contract.function.split("::").pop();
    if (shortName && !map.has(shortName)) {
      map.set(shortName, contract);
    }
  }

  return map;
}

/**
 * Find contracts that match a given pattern (supports wildcards)
 */
export function findMatchingContracts(
  contracts: ContractExport,
  pattern: string
): ExportedContract[] {
  const regex = new RegExp(
    "^" + pattern.replace(/\*/g, ".*").replace(/\?/g, ".") + "$"
  );

  return contracts.contracts.filter(
    (c) => regex.test(c.function) || regex.test(c.module)
  );
}
