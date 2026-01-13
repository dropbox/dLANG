#!/usr/bin/env node
/**
 * CLI for ts-contract-checker
 *
 * Usage:
 *   ts-contract-checker --contracts contracts.json file1.ts file2.ts
 *   ts-contract-checker -c contracts.json src/[glob].ts
 */

import * as fs from "fs";
import * as path from "path";
import { loadContracts } from "./loader";
import { checkTypeScriptFile, formatResults } from "./checker";
import { CheckResult } from "./types";

interface CliOptions {
  contracts: string;
  files: string[];
  verbose: boolean;
  json: boolean;
  help: boolean;
}

function parseArgs(): CliOptions {
  const args = process.argv.slice(2);
  const options: CliOptions = {
    contracts: "",
    files: [],
    verbose: false,
    json: false,
    help: false,
  };

  let i = 0;
  while (i < args.length) {
    const arg = args[i];

    if (arg === "-h" || arg === "--help") {
      options.help = true;
      i++;
    } else if (arg === "-v" || arg === "--verbose") {
      options.verbose = true;
      i++;
    } else if (arg === "--json") {
      options.json = true;
      i++;
    } else if (arg === "-c" || arg === "--contracts") {
      options.contracts = args[i + 1] || "";
      i += 2;
    } else if (arg.startsWith("-")) {
      console.error(`Unknown option: ${arg}`);
      process.exit(1);
    } else {
      options.files.push(arg);
      i++;
    }
  }

  return options;
}

function printHelp(): void {
  console.log(`
ts-contract-checker - Cross-language contract verification for tRust (Phase 6.5.6)

USAGE:
  ts-contract-checker --contracts <path> [options] <files...>

OPTIONS:
  -c, --contracts <path>   Path to contracts.json exported from Rust
  -v, --verbose            Show verbose output
  --json                   Output results as JSON
  -h, --help               Show this help message

EXAMPLES:
  # Check a single file
  ts-contract-checker -c contracts.json src/api.ts

  # Check multiple files
  ts-contract-checker -c contracts.json src/*.ts

  # Output as JSON for CI integration
  ts-contract-checker -c contracts.json --json src/api.ts

DESCRIPTION:
  This tool reads function contracts exported from a Rust codebase (using
  rustc -Zverify -Zexport-contracts=contracts.json) and checks TypeScript
  source files for:

  1. API calls that may violate preconditions
  2. Type mismatches between Rust and TypeScript
  3. Missing error handling for API calls
  4. Unvalidated data sent to Rust backend

  The goal is to catch cross-language contract violations at development time,
  before they become runtime errors.

See also:
  - tRust documentation: https://github.com/ayates_dbx/tRust
  - Contract export: rustc -Zverify -Zexport-contracts=contracts.json
`);
}

function expandGlobs(patterns: string[]): string[] {
  const files: string[] = [];

  for (const pattern of patterns) {
    if (pattern.includes("*")) {
      // Simple glob expansion (would use glob package in production)
      const dir = path.dirname(pattern);
      const ext = path.extname(pattern);

      if (fs.existsSync(dir)) {
        const entries = fs.readdirSync(dir);
        for (const entry of entries) {
          if (entry.endsWith(ext)) {
            files.push(path.join(dir, entry));
          }
        }
      }
    } else if (fs.existsSync(pattern)) {
      files.push(pattern);
    } else {
      console.error(`File not found: ${pattern}`);
    }
  }

  return files;
}

function main(): void {
  const options = parseArgs();

  if (options.help) {
    printHelp();
    process.exit(0);
  }

  if (!options.contracts) {
    console.error("Error: --contracts option is required");
    console.error("Use --help for usage information");
    process.exit(1);
  }

  if (options.files.length === 0) {
    console.error("Error: No input files specified");
    console.error("Use --help for usage information");
    process.exit(1);
  }

  // Load contracts
  let contracts;
  try {
    contracts = loadContracts(options.contracts);
    if (options.verbose) {
      console.log(
        `Loaded ${contracts.contracts.length} contracts from ${options.contracts}`
      );
    }
  } catch (error) {
    console.error(`Error loading contracts: ${error}`);
    process.exit(1);
  }

  // Expand file patterns
  const files = expandGlobs(options.files);

  if (files.length === 0) {
    console.error("Error: No matching files found");
    process.exit(1);
  }

  // Check each file
  const results: CheckResult[] = [];

  for (const file of files) {
    if (options.verbose) {
      console.log(`Checking ${file}...`);
    }

    try {
      const result = checkTypeScriptFile(file, contracts);
      results.push(result);
    } catch (error) {
      console.error(`Error checking ${file}: ${error}`);
    }
  }

  // Output results
  if (options.json) {
    console.log(JSON.stringify(results, null, 2));
  } else {
    console.log(formatResults(results));
  }

  // Exit with error code if violations found
  const totalViolations = results.reduce(
    (sum, r) => sum + r.violations.length,
    0
  );

  if (totalViolations > 0) {
    process.exit(1);
  }
}

main();
