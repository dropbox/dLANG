# ts-contract-checker

Cross-language contract verification for tRust (Phase 6.5.6)

## Overview

This tool enables verification of TypeScript frontend code against Rust backend
contracts. It reads contracts exported from `rustc -Zverify -Zexport-contracts`
and checks TypeScript source files for potential violations.

## Installation

```bash
cd tools/ts-contract-checker
npm install
npm run build
```

## Usage

### 1. Export contracts from Rust

```bash
# Compile Rust with contract export
rustc -Zverify -Zexport-contracts=contracts.json src/lib.rs
```

### 2. Check TypeScript files

```bash
# Check a single file
npx ts-contract-checker -c contracts.json src/api.ts

# Check multiple files
npx ts-contract-checker -c contracts.json src/*.ts

# Output as JSON (for CI)
npx ts-contract-checker -c contracts.json --json src/api.ts
```

## What it checks

1. **API calls vs contracts**: Warns when TypeScript fetch/axios calls don't
   have corresponding contracts or when preconditions might not be validated.

2. **Error handling**: Warns about API calls without proper error handling.

3. **Type compatibility**: (Future) Check TypeScript types against Rust types
   for structural compatibility.

## Example

Given this Rust contract:

```rust
#[requires("body.email.len() > 0")]
#[requires("body.age >= 18")]
#[ensures("result.id > 0")]
pub fn create_user(body: CreateUserRequest) -> CreateUserResponse {
    // ...
}
```

And this TypeScript code:

```typescript
// Warning: Precondition "body.age >= 18" may not be validated
const response = await fetch("/api/users", {
  method: "POST",
  body: JSON.stringify({ email, age }),
});
```

The checker will warn that the age validation might be missing.

## JSON Output Format

```json
[
  {
    "file": "src/api.ts",
    "violations": [],
    "warnings": [
      {
        "type": "unverified_precondition",
        "location": { "line": 10, "column": 5 },
        "message": "Precondition \"body.age >= 18\" may not be validated before call"
      }
    ]
  }
]
```

## Contract JSON Format

The input `contracts.json` follows this schema:

```json
{
  "version": "1.0",
  "crate_name": "my_api",
  "timestamp": "2026-01-03T12:00:00Z",
  "contracts": [
    {
      "function": "api::create_user",
      "module": "api",
      "visibility": "public",
      "api_metadata": {
        "path": "/api/users",
        "method": "POST"
      },
      "requires": [
        { "expr": "body.email.len() > 0", "label": "email must not be empty" }
      ],
      "ensures": [
        { "expr": "result.id > 0" }
      ],
      "params": [
        { "name": "body", "type": "CreateUserRequest" }
      ],
      "return_type": "CreateUserResponse",
      "pure": false,
      "effects": ["IO", "Database"]
    }
  ],
  "types": {}
}
```

## Development

```bash
# Build
npm run build

# Run tests
npm test
```

## License

MIT
