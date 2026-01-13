# Upstream Contracts Integration Examples

This directory contains tests for tRust's integration with upstream Rust's `#![feature(contracts)]`.

## Background

As of tRust iteration #942-#947, both contract systems work together:
- **tRust's `trust_macros`**: Compile-time verification via SMT solver
- **Upstream `#![feature(contracts)]`**: Runtime contracts (now integrated)

When tRust can prove a contract at compile time, the runtime check is elided (zero overhead).
When it can't prove, the upstream runtime check remains as a fallback.

## Test Files

- `upstream_contracts_test.rs`: Basic integration test showing both contract systems
- `elide_mir_test.rs`: Regression test for runtime check elision (ContractsElide MIR pass)

## Usage

These tests are run by `./run_tests.sh` with special flags:
- `TRUST_CONTRACTS_VERIFY=1` - Enable contracts verification
- `-Zcontract-checks` - Enable upstream contract checking
- `-Zdump-mir=ContractsElide` - Dump MIR for elision verification (elide_mir_test only)

## See Also

- `docs/CONTRACTS_COMPATIBILITY.md` - Full documentation of contracts integration
- `docs/CONTRACTS_MERGER_DESIGN.md` - Design document for the merger
