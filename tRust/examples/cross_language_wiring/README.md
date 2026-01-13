# Cross-Language Wiring Test

Phase 6.5.6: Cross-Language Contract Verification Example

## Overview

This example demonstrates tRust's cross-language contract verification:
1. Rust backend with contracts (`backend.rs`)
2. TypeScript frontend with intentional violations (`frontend.ts`)
3. Pre-generated contracts file (`contracts.json`)

## Files

- `backend.rs` - Rust backend with `#[requires]` and `#[ensures]` contracts
- `frontend.ts` - TypeScript frontend with API calls (some violating contracts)
- `contracts.json` - Exported contracts (pre-generated for demo)

## Expected Violations

The frontend.ts intentionally contains these issues:

| Function | Issue | Contract Violated |
|----------|-------|-------------------|
| `createUser` | No age validation | `age >= 18` |
| `createUser` | No email validation | `email.len() > 0` |
| `deleteUser` | No admin check | `is_admin` |
| `processPayment` | Weak card validation | `card_number >= 1000000000000000` |
| `searchProducts` | No limit upper bound | `limit <= 100` |

## Running the Test

### Option 1: Use pre-generated contracts

```bash
# Build the TypeScript checker
cd tools/ts-contract-checker
npm install
npm run build

# Check the frontend
npx ts-contract-checker -c ../../examples/cross_language_wiring/contracts.json \
    ../../examples/cross_language_wiring/frontend.ts
```

### Option 2: Generate contracts from Rust (requires tRust compiler)

```bash
# Build and verify the backend, exporting contracts
./run_tests.sh examples/cross_language_wiring/backend.rs -Zexport-contracts=contracts.json

# Then check the frontend
cd tools/ts-contract-checker
npm run build
npx ts-contract-checker -c ../../examples/cross_language_wiring/contracts.json \
    ../../examples/cross_language_wiring/frontend.ts
```

## Expected Output

```
examples/cross_language_wiring/frontend.ts:
  WARN [24:3] unverified_precondition: Precondition "email.len() > 0" may not be validated
  WARN [25:3] unverified_precondition: Precondition "age >= 18" may not be validated
  WARN [64:3] unverified_precondition: Precondition "is_admin" may not be validated
  WARN [97:3] unverified_precondition: Precondition "card_number >= 1000000000000000" may not be validated
  WARN [124:3] unverified_precondition: Precondition "limit <= 100" may not be validated

---
Total: 0 error(s), 5 warning(s)
```

## Integration Points

1. **Contract Export**: `rustc -Zverify -Zexport-contracts=contracts.json`
2. **TypeScript Checking**: `ts-contract-checker --contracts contracts.json frontend.ts`
3. **CI Integration**: Both tools exit with code 1 on errors for CI failure

## Architecture

```
┌─────────────────┐     ┌──────────────────┐     ┌─────────────────┐
│   backend.rs    │     │  contracts.json  │     │  frontend.ts    │
│  (Rust + specs) │────▶│  (exported)      │◀────│  (API calls)    │
└─────────────────┘     └──────────────────┘     └─────────────────┘
        │                        │                        │
        ▼                        ▼                        ▼
┌─────────────────┐     ┌──────────────────┐     ┌─────────────────┐
│  trustc -Zverify │     │  JSON contract   │     │ ts-contract-    │
│  (Rust verify)   │     │  schema v1.0     │     │ checker (TS)    │
└─────────────────┘     └──────────────────┘     └─────────────────┘
```

## Next Steps

- Add API metadata (`#[api("/path", "METHOD")]`) to Rust contracts
- Extend TypeScript checker to do deeper AST analysis
- Add type compatibility checking between Rust and TypeScript
- Integrate with IDE/LSP for real-time feedback
