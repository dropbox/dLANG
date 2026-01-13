# tRust Architecture Intent

## THIS IS A FULL RUSTC FORK

**We are modifying rustc directly. Not building a separate tool. Not just macros.**

## Current State (Scaffolding)

```
┌─────────────────────────────────────────────────────────────┐
│ TEMPORARY SCAFFOLDING (will be replaced)                    │
├─────────────────────────────────────────────────────────────┤
│  trust_macros (proc_macro)  →  VC IR  →  Z3               │
│  #[requires], #[ensures]       translation    verification  │
│                                                             │
│  This lets us TEST the spec syntax while we build the real  │
│  compiler integration. IT WILL BE THROWN AWAY.              │
└─────────────────────────────────────────────────────────────┘
```

## Target State (The Real tRust)

```
┌─────────────────────────────────────────────────────────────┐
│ RUSTC FORK (the goal)                                       │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  rustc_parse     → Parse #[requires], #[ensures] natively   │
│       ↓                                                     │
│  rustc_ast       → AST includes spec expressions            │
│       ↓                                                     │
│  rustc_hir       → HIR carries specifications               │
│       ↓                                                     │
│  rustc_mir_build → MIR preserves spec info                  │
│       ↓                                                     │
│  rustc_verify    → NEW PASS: MIR → VC → Z3 → prove/disprove │
│       ↓                                                     │
│  LLVM codegen    → Only if verified                         │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

## Key Rustc Files to Modify

```
upstream/rustc/compiler/
├── rustc_ast/src/
│   └── attr/           ← Add #[requires], #[ensures] as built-in attributes
├── rustc_parse/src/
│   └── parser/         ← Parse spec expressions
├── rustc_hir/src/
│   └── hir.rs          ← HIR nodes carry specs
├── rustc_mir_build/src/
│   └── build/          ← Preserve specs through lowering
└── rustc_verify/       ← NEW CRATE: verification pass
    ├── src/
    │   ├── lib.rs      ← Main verification pass
    │   ├── vc_gen.rs   ← MIR → Verification Conditions
    │   └── z3.rs       ← Z3 integration
    └── Cargo.toml
```

## The Plan

1. **NOW**: Use proc_macros to test spec syntax, build VC IR, integrate Z3
2. **SOON**: Start modifying `upstream/rustc/` to parse specs natively
3. **GOAL**: Verification is a rustc pass, not a separate tool

## Non-Negotiable

- This is NOT another Kani/Creusot/Prusti
- This IS a rustc fork with native verification
- Specs are FIRST-CLASS in the compiler
- Verification errors are COMPILER ERRORS

## Why Scaffolding First

1. Faster iteration on spec syntax
2. Test VC → Z3 pipeline without touching rustc
3. Build confidence before major surgery
4. Working prototype to guide rustc changes

**The scaffolding is a means to an end. The end is a modified rustc.**
