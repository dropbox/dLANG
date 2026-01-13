# Real-World Validation

This directory contains dependency-free re-creations of core logic from small real-world crates,
intended to validate tRust on realistic Rust code (beyond toy examples).

## subtle (subset)

Files:
- `subtle.rs`: Minimal `Choice` type plus `ct_eq_u8` and `conditional_select_u8`.
- `../real_validation_subtle_test.rs`: Integration test that verifies contracts with `-Zverify`.

Verified functions (contracted + used by the test):
- `Choice::from_u8`
- `Choice::unwrap_bool`
- `Choice::not`
- `Choice::and`
- `Choice::or`
- `Choice::xor` - logical XOR
- `ct_eq_u8` - constant-time equality
- `ct_ne_u8` - constant-time not-equal
- `conditional_select_u8`
- `conditional_swap_u8` - conditional swap (returns `SwapResult` struct)
- `ct_lt_u8` - constant-time less-than
- `ct_gt_u8` - constant-time greater-than
- `ct_le_u8` - constant-time less-than-or-equal
- `ct_ge_u8` - constant-time greater-than-or-equal

**u16 variants:**
- `ct_eq_u16` - constant-time equality for u16
- `ct_ne_u16` - constant-time not-equal for u16
- `ct_lt_u16` - constant-time less-than for u16
- `ct_gt_u16` - constant-time greater-than for u16
- `ct_le_u16` - constant-time less-than-or-equal for u16
- `ct_ge_u16` - constant-time greater-than-or-equal for u16
- `conditional_select_u16` - conditional selection for u16
- `conditional_swap_u16` - conditional swap for u16 (returns `SwapResult16` struct)

**u32 variants:**
- `ct_eq_u32` - constant-time equality for u32
- `ct_ne_u32` - constant-time not-equal for u32
- `ct_lt_u32` - constant-time less-than for u32
- `ct_gt_u32` - constant-time greater-than for u32
- `ct_le_u32` - constant-time less-than-or-equal for u32
- `ct_ge_u32` - constant-time greater-than-or-equal for u32
- `conditional_select_u32` - conditional selection for u32
- `conditional_swap_u32` - conditional swap for u32 (returns `SwapResult32` struct)

**u64 variants:**
- `ct_eq_u64` - constant-time equality for u64
- `ct_ne_u64` - constant-time not-equal for u64
- `ct_lt_u64` - constant-time less-than for u64
- `ct_gt_u64` - constant-time greater-than for u64
- `ct_le_u64` - constant-time less-than-or-equal for u64
- `ct_ge_u64` - constant-time greater-than-or-equal for u64
- `conditional_select_u64` - conditional selection for u64
- `conditional_swap_u64` - conditional swap for u64 (returns `SwapResult64` struct)

**i8 signed variants:**
- `ct_eq_i8` - constant-time equality for i8 (signed)
- `ct_ne_i8` - constant-time not-equal for i8 (signed)
- `ct_lt_i8` - constant-time less-than for i8 (signed comparison)
- `ct_gt_i8` - constant-time greater-than for i8 (signed comparison)
- `ct_le_i8` - constant-time less-than-or-equal for i8 (signed comparison)
- `ct_ge_i8` - constant-time greater-than-or-equal for i8 (signed comparison)
- `conditional_select_i8` - conditional selection for i8
- `conditional_swap_i8` - conditional swap for i8 (returns `SwapResultI8` struct)

**i16 signed variants:**
- `ct_eq_i16` - constant-time equality for i16 (signed)
- `ct_ne_i16` - constant-time not-equal for i16 (signed)
- `ct_lt_i16` - constant-time less-than for i16 (signed comparison)
- `ct_gt_i16` - constant-time greater-than for i16 (signed comparison)
- `ct_le_i16` - constant-time less-than-or-equal for i16 (signed comparison)
- `ct_ge_i16` - constant-time greater-than-or-equal for i16 (signed comparison)
- `conditional_select_i16` - conditional selection for i16
- `conditional_swap_i16` - conditional swap for i16 (returns `SwapResultI16` struct)

**i32 signed variants:**
- `ct_eq_i32` - constant-time equality for i32 (signed)
- `ct_ne_i32` - constant-time not-equal for i32 (signed)
- `ct_lt_i32` - constant-time less-than for i32 (signed comparison)
- `ct_gt_i32` - constant-time greater-than for i32 (signed comparison)
- `ct_le_i32` - constant-time less-than-or-equal for i32 (signed comparison)
- `ct_ge_i32` - constant-time greater-than-or-equal for i32 (signed comparison)
- `conditional_select_i32` - conditional selection for i32
- `conditional_swap_i32` - conditional swap for i32 (returns `SwapResultI32` struct)

**i64 signed variants:**
- `ct_eq_i64` - constant-time equality for i64 (signed)
- `ct_ne_i64` - constant-time not-equal for i64 (signed)
- `ct_lt_i64` - constant-time less-than for i64 (signed comparison)
- `ct_gt_i64` - constant-time greater-than for i64 (signed comparison)
- `ct_le_i64` - constant-time less-than-or-equal for i64 (signed comparison)
- `ct_ge_i64` - constant-time greater-than-or-equal for i64 (signed comparison)
- `conditional_select_i64` - conditional selection for i64
- `conditional_swap_i64` - conditional swap for i64 (returns `SwapResultI64` struct)

**Conditional negation (ConditionallyNegatable trait):**
Used in cryptographic operations like elliptic curve point negation.
Returns value unchanged if choice is 0, wrapping-negated if choice is 1.
- `conditional_negate_i8` - conditionally negate i8
- `conditional_negate_i16` - conditionally negate i16
- `conditional_negate_i32` - conditionally negate i32
- `conditional_negate_i64` - conditionally negate i64
- `conditional_negate_isize` - conditionally negate isize (pointer-sized)

**usize variants (pointer-sized unsigned):**
Used for array indexing operations in cryptographic code.
- `ct_eq_usize` - constant-time equality for usize
- `ct_ne_usize` - constant-time not-equal for usize
- `ct_lt_usize` - constant-time less-than for usize
- `ct_gt_usize` - constant-time greater-than for usize
- `ct_le_usize` - constant-time less-than-or-equal for usize
- `ct_ge_usize` - constant-time greater-than-or-equal for usize
- `conditional_select_usize` - conditional selection for usize
- `conditional_swap_usize` - conditional swap for usize (returns `SwapResultUsize` struct)

**isize variants (pointer-sized signed):**
Used for signed offset calculations in cryptographic code.
- `ct_eq_isize` - constant-time equality for isize
- `ct_ne_isize` - constant-time not-equal for isize (signed)
- `ct_lt_isize` - constant-time less-than for isize (signed comparison)
- `ct_gt_isize` - constant-time greater-than for isize (signed comparison)
- `ct_le_isize` - constant-time less-than-or-equal for isize (signed comparison)
- `ct_ge_isize` - constant-time greater-than-or-equal for isize (signed comparison)
- `conditional_select_isize` - conditional selection for isize
- `conditional_swap_isize` - conditional swap for isize (returns `SwapResultIsize` struct)

**CtOption (constant-time optional value handling):**
Provides constant-time optional semantics where the presence or absence of a value
doesn't leak through timing side-channels. Critical for cryptographic operations
where branching on `Option::is_some()` would create observable timing differences.

Type-specific implementations (verifier doesn't handle generics):

*Unsigned types:*
- `CtOptionU8` - constant-time optional u8 value
- `CtOptionU32` - constant-time optional u32 value
- `CtOptionU64` - constant-time optional u64 value

*Signed types:*
- `CtOptionI8` - constant-time optional i8 value
- `CtOptionI16` - constant-time optional i16 value
- `CtOptionI32` - constant-time optional i32 value
- `CtOptionI64` - constant-time optional i64 value

*Pointer-sized types:*
- `CtOptionUsize` - constant-time optional usize value
- `CtOptionIsize` - constant-time optional isize value

Each CtOption provides:
- `new(value, is_some)` - create with explicit presence flag
- `none()` - create "None" variant (is_some=0)
- `some(value)` - create "Some" variant (is_some=1)
- `ct_is_some()` - returns Choice(1) if Some, Choice(0) if None
- `ct_is_none()` - returns Choice(1) if None, Choice(0) if Some
- `unwrap_or(default)` - returns value if Some, default if None (constant-time)
- `unwrap_or_default()` - returns value if Some, 0 if None (constant-time)

**Constant-time byte array comparison (ConstantTimeEq for fixed-size arrays):**
Used for comparing cryptographic hashes, keys, and signatures in constant time.
Fixed sizes avoid generics which the verifier doesn't support.

- `ct_eq_bytes_16(a, b)` - constant-time equality for [u8; 16] (AES block, UUID, MD5)
- `ct_eq_bytes_32(a, b)` - constant-time equality for [u8; 32] (SHA-256, ChaCha20 key, X25519 key)
- `ct_eq_bytes_64(a, b)` - constant-time equality for [u8; 64] (SHA-512, Ed25519 signature)

Note: These functions use runtime testing only - the verifier has trouble with
array reference parameters. The constant-time property is ensured by the
XOR-accumulate-then-compare implementation pattern.

Update: `ct_eq_bytes_*` now uses a verified, branch-free `ct_is_zero_u8()` helper to
avoid incorrect results for high-bit XOR differences (e.g., 0xFF vs 0x00). Runtime
assertions in `examples/real_validation_subtle_test.rs` cover these edge cases, but
`./run_tests.sh` does not execute binaries (it only verifies/compiles).

**Constant-time zero checking (ConstantTimeZero):**
Used for cryptographic operations like scalar validation, field element validation,
and checking if a key is the identity element.

- `ct_is_zero_u8_pub(x)` - constant-time check if u8 is zero (returns Choice)
- `ct_is_zero_u16(x)` - constant-time check if u16 is zero
- `ct_is_zero_u32(x)` - constant-time check if u32 is zero
- `ct_is_zero_u64(x)` - constant-time check if u64 is zero
- `ct_is_zero_i8(x)` - constant-time check if i8 is zero
- `ct_is_zero_i16(x)` - constant-time check if i16 is zero
- `ct_is_zero_i32(x)` - constant-time check if i32 is zero
- `ct_is_zero_i64(x)` - constant-time check if i64 is zero
- `ct_is_zero_usize(x)` - constant-time check if usize is zero
- `ct_is_zero_isize(x)` - constant-time check if isize is zero

Note: Returns Choice(1) if x == 0, Choice(0) otherwise. Contracts verify
normalization only (result is 0 or 1); exact values are tested at runtime.

## hex (subset)

Files:
- `hex.rs`: Hex encoding/decoding with verified contracts.
- `../real_validation_hex_test.rs`: Integration test that verifies contracts with `-Zverify`.

Verified functions (contracted + used by the test):
- `encode_nibble` - encode 4-bit value to lowercase hex char [precondition: nibble <= 15]
- `decode_nibble` - decode hex char to 4-bit value (case-insensitive)
- `encode_byte` - encode byte to two lowercase hex chars
- `decode_byte` - decode two hex chars to byte (uses wrapping arithmetic for verifier compatibility)
- `is_hex_digit` - check if char is valid hex digit
- `encode_nibble_upper` - encode 4-bit value to uppercase hex char [precondition: nibble <= 15]
- `encode_byte_upper` - encode byte to two uppercase hex chars

Note: Round-trip functions were removed because they require complex contract
propagation that the SMT solver cannot handle. The individual encode/decode
functions are verified, and roundtrip behavior is tested at runtime.

## base64 (subset)

Files:
- `base64.rs`: Base64 encoding/decoding with verified contracts (RFC 4648 alphabet).
- `../real_validation_base64_test.rs`: Integration test that verifies contracts with `-Zverify`.

Verified functions (contracted + used by the test):
- `encode_char` - encode 6-bit value (0-63) to base64 character [precondition: value < 64]
- `decode_char` - decode base64 character to 6-bit value (returns DecodeResult with validity flag)
- `is_base64_char` - check if byte is valid base64 character (excludes padding '=')
- `is_padding_char` - check if byte is base64 padding '=' (ASCII 61)
- `encode_group` - encode 3 bytes to 4 base64 characters (core encoding operation)
- `decode_group` - decode 4 base64 characters to 3 bytes (core decoding operation)
- `encode_one_byte` - encode 1 byte to 2 base64 chars + 2 padding
- `encode_two_bytes` - encode 2 bytes to 3 base64 chars + 1 padding

Note: Uses wrapping arithmetic in encode functions because the overflow checker
cannot prove bounds from bit operations. The bit operations guarantee values < 64
at runtime, but this requires symbolic reasoning the verifier doesn't perform.
Closures are not used because the SMT solver doesn't track closure return values.

## Testing

Two complementary test scripts are available:

### Contract Verification (compile-time)
```bash
./run_tests.sh
```
Compiles tests with `-Zverify` to check contracts at compile-time via SMT solver.
Does NOT execute binaries - only verifies contracts are satisfiable.

### Runtime Testing (execution)
```bash
./run_runtime_tests.sh
```
Compiles tests WITHOUT `-Zverify` and EXECUTES the binaries.
Exercises `assert_eq!` and other runtime checks that can't be SMT-verified.

**Use both**: Run `./run_tests.sh` for verification coverage, then `./run_runtime_tests.sh`
to ensure runtime behavior is correct (especially for functions like `ct_eq_bytes_*`
where the verifier can't reason about array reference parameters).
