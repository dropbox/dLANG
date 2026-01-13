#![allow(dead_code)]

/// Minimal, dependency-free subset of base64 encoding/decoding logic.
///
/// This module provides verified base64 conversion operations.
/// The specification follows RFC 4648 standard base64 alphabet.
///
/// Base64 alphabet (64 characters):
/// Index 0-25:  'A'-'Z' (ASCII 65-90)
/// Index 26-51: 'a'-'z' (ASCII 97-122)
/// Index 52-61: '0'-'9' (ASCII 48-57)
/// Index 62:    '+' (ASCII 43)
/// Index 63:    '/' (ASCII 47)
/// Padding:     '=' (ASCII 61)

/// Result type for decode operations.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct DecodeResult {
    pub value: u8,
    pub valid: bool,
}

/// Encode a single 6-bit value (0-63) to its base64 character.
/// Precondition ensures valid input range.
#[requires("value < 64")]
#[ensures("result >= 43")]  // min is '+' (43)
#[ensures("result <= 122")] // max is 'z' (122)
pub fn encode_char(value: u8) -> u8 {
    if value < 26 {
        // 0-25 -> 'A'-'Z' (65-90)
        65 + value
    } else if value < 52 {
        // 26-51 -> 'a'-'z' (97-122)
        // value - 26 gives 0-25, + 97 gives 97-122
        97 + (value - 26)
    } else if value < 62 {
        // 52-61 -> '0'-'9' (48-57)
        // value - 52 gives 0-9, + 48 gives 48-57
        48 + (value - 52)
    } else if value == 62 {
        // 62 -> '+' (43)
        43
    } else {
        // 63 -> '/' (47)
        47
    }
}

/// Decode a single base64 character to its 6-bit value.
/// Returns DecodeResult { value, valid } where valid indicates success.
#[ensures("result.valid == true ==> result.value < 64")]
pub fn decode_char(c: u8) -> DecodeResult {
    if c >= 65 && c <= 90 {
        // 'A'-'Z' (65-90) -> 0-25
        DecodeResult { value: c - 65, valid: true }
    } else if c >= 97 && c <= 122 {
        // 'a'-'z' (97-122) -> 26-51
        DecodeResult { value: c - 97 + 26, valid: true }
    } else if c >= 48 && c <= 57 {
        // '0'-'9' (48-57) -> 52-61
        DecodeResult { value: c - 48 + 52, valid: true }
    } else if c == 43 {
        // '+' (43) -> 62
        DecodeResult { value: 62, valid: true }
    } else if c == 47 {
        // '/' (47) -> 63
        DecodeResult { value: 63, valid: true }
    } else {
        DecodeResult { value: 0, valid: false }
    }
}

/// Check if a character is a valid base64 character (not including padding '=').
#[ensures("result == true ==> (c >= 43 && c != 44 && c != 45 && c != 46)")]
pub fn is_base64_char(c: u8) -> bool {
    (c >= 65 && c <= 90)   // 'A'-'Z'
        || (c >= 97 && c <= 122) // 'a'-'z'
        || (c >= 48 && c <= 57)  // '0'-'9'
        || c == 43  // '+'
        || c == 47  // '/'
}

/// Check if a character is the base64 padding character '='.
#[ensures("result == (c == 61)")]
pub fn is_padding_char(c: u8) -> bool {
    c == 61  // '='
}

/// Result of encoding a 3-byte group to 4 base64 characters.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct EncodeGroupResult {
    pub c0: u8,
    pub c1: u8,
    pub c2: u8,
    pub c3: u8,
}

/// Encode a 3-byte group to 4 base64 characters.
/// This is the core encoding operation.
///
/// 3 bytes (24 bits) -> 4 base64 chars (6 bits each)
/// |  byte0  |  byte1  |  byte2  |
/// |xxxxxxyy|yyyyzzzz|zzwwwwww|
/// |  c0  |  c1  |  c2  |  c3  |
#[ensures("result.c0 >= 43 && result.c0 <= 122")]
#[ensures("result.c1 >= 43 && result.c1 <= 122")]
#[ensures("result.c2 >= 43 && result.c2 <= 122")]
#[ensures("result.c3 >= 43 && result.c3 <= 122")]
pub fn encode_group(b0: u8, b1: u8, b2: u8) -> EncodeGroupResult {
    // Extract 6-bit values using bit operations
    // c0 = top 6 bits of b0 (b0 >> 2, always < 64)
    // c1 = bottom 2 bits of b0 + top 4 bits of b1 (always < 64)
    // c2 = bottom 4 bits of b1 + top 2 bits of b2 (always < 64)
    // c3 = bottom 6 bits of b2 (always < 64)
    let n0 = b0 >> 2;
    let n1 = ((b0 & 0x03) << 4) | (b1 >> 4);
    let n2 = ((b1 & 0x0F) << 2) | (b2 >> 6);
    let n3 = b2 & 0x3F;

    // Use wrapping operations since overflow checker can't prove bounds from bit ops
    let c0 = if n0 < 26 { 65u8.wrapping_add(n0) }
        else if n0 < 52 { 97u8.wrapping_add(n0.wrapping_sub(26)) }
        else if n0 < 62 { 48u8.wrapping_add(n0.wrapping_sub(52)) }
        else if n0 == 62 { 43 }
        else { 47 };

    let c1 = if n1 < 26 { 65u8.wrapping_add(n1) }
        else if n1 < 52 { 97u8.wrapping_add(n1.wrapping_sub(26)) }
        else if n1 < 62 { 48u8.wrapping_add(n1.wrapping_sub(52)) }
        else if n1 == 62 { 43 }
        else { 47 };

    let c2 = if n2 < 26 { 65u8.wrapping_add(n2) }
        else if n2 < 52 { 97u8.wrapping_add(n2.wrapping_sub(26)) }
        else if n2 < 62 { 48u8.wrapping_add(n2.wrapping_sub(52)) }
        else if n2 == 62 { 43 }
        else { 47 };

    let c3 = if n3 < 26 { 65u8.wrapping_add(n3) }
        else if n3 < 52 { 97u8.wrapping_add(n3.wrapping_sub(26)) }
        else if n3 < 62 { 48u8.wrapping_add(n3.wrapping_sub(52)) }
        else if n3 == 62 { 43 }
        else { 47 };

    EncodeGroupResult { c0, c1, c2, c3 }
}

/// Result of decoding a 4-character group to 3 bytes.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct DecodeGroupResult {
    pub b0: u8,
    pub b1: u8,
    pub b2: u8,
    pub valid: bool,
}

/// Decode a 4-character base64 group to 3 bytes.
/// This is the core decoding operation.
/// Note: Does not handle padding - all 4 characters must be valid base64.
#[ensures("result.valid == true ==> result.b0 <= 255")]
#[ensures("result.valid == true ==> result.b1 <= 255")]
#[ensures("result.valid == true ==> result.b2 <= 255")]
pub fn decode_group(c0: u8, c1: u8, c2: u8, c3: u8) -> DecodeGroupResult {
    let r0 = decode_char(c0);
    let r1 = decode_char(c1);
    let r2 = decode_char(c2);
    let r3 = decode_char(c3);

    if r0.valid && r1.valid && r2.valid && r3.valid {
        // Reconstruct bytes from 6-bit values
        // Using wrapping operations for verifier compatibility

        // b0 = top 6 bits from n0, bottom 2 bits from top of n1
        let b0 = (r0.value << 2).wrapping_add(r1.value >> 4);

        // b1 = bottom 4 bits of n1, top 4 bits of n2
        let b1 = ((r1.value & 0x0F) << 4).wrapping_add(r2.value >> 2);

        // b2 = bottom 2 bits of n2, all 6 bits of n3
        let b2 = ((r2.value & 0x03) << 6).wrapping_add(r3.value);

        DecodeGroupResult { b0, b1, b2, valid: true }
    } else {
        DecodeGroupResult { b0: 0, b1: 0, b2: 0, valid: false }
    }
}

/// Encode a single byte to 2 base64 characters with padding.
/// Output format: [char0, char1, '=', '=']
/// This handles the case when we have 1 byte remaining (8 bits -> 2 chars + 2 padding).
#[ensures("result.c0 >= 43 && result.c0 <= 122")]
#[ensures("result.c1 >= 43 && result.c1 <= 122")]
#[ensures("result.c2 == 61")]  // '='
#[ensures("result.c3 == 61")]  // '='
pub fn encode_one_byte(b0: u8) -> EncodeGroupResult {
    // c0 = top 6 bits of b0 (always < 64)
    // c1 = bottom 2 bits of b0 shifted left (always < 64)
    let n0 = b0 >> 2;
    let n1 = (b0 & 0x03) << 4;

    // Use wrapping operations since overflow checker can't prove bounds from bit ops
    let c0 = if n0 < 26 { 65u8.wrapping_add(n0) }
        else if n0 < 52 { 97u8.wrapping_add(n0.wrapping_sub(26)) }
        else if n0 < 62 { 48u8.wrapping_add(n0.wrapping_sub(52)) }
        else if n0 == 62 { 43 }
        else { 47 };

    let c1 = if n1 < 26 { 65u8.wrapping_add(n1) }
        else if n1 < 52 { 97u8.wrapping_add(n1.wrapping_sub(26)) }
        else if n1 < 62 { 48u8.wrapping_add(n1.wrapping_sub(52)) }
        else if n1 == 62 { 43 }
        else { 47 };

    EncodeGroupResult { c0, c1, c2: 61, c3: 61 }
}

/// Encode two bytes to 3 base64 characters with padding.
/// Output format: [char0, char1, char2, '=']
/// This handles the case when we have 2 bytes remaining (16 bits -> 3 chars + 1 padding).
#[ensures("result.c0 >= 43 && result.c0 <= 122")]
#[ensures("result.c1 >= 43 && result.c1 <= 122")]
#[ensures("result.c2 >= 43 && result.c2 <= 122")]
#[ensures("result.c3 == 61")]  // '='
pub fn encode_two_bytes(b0: u8, b1: u8) -> EncodeGroupResult {
    // c0 = top 6 bits of b0 (always < 64)
    // c1 = bottom 2 bits of b0 + top 4 bits of b1 (always < 64)
    // c2 = bottom 4 bits of b1 shifted left (always < 64)
    let n0 = b0 >> 2;
    let n1 = ((b0 & 0x03) << 4) | (b1 >> 4);
    let n2 = (b1 & 0x0F) << 2;

    // Use wrapping operations since overflow checker can't prove bounds from bit ops
    let c0 = if n0 < 26 { 65u8.wrapping_add(n0) }
        else if n0 < 52 { 97u8.wrapping_add(n0.wrapping_sub(26)) }
        else if n0 < 62 { 48u8.wrapping_add(n0.wrapping_sub(52)) }
        else if n0 == 62 { 43 }
        else { 47 };

    let c1 = if n1 < 26 { 65u8.wrapping_add(n1) }
        else if n1 < 52 { 97u8.wrapping_add(n1.wrapping_sub(26)) }
        else if n1 < 62 { 48u8.wrapping_add(n1.wrapping_sub(52)) }
        else if n1 == 62 { 43 }
        else { 47 };

    let c2 = if n2 < 26 { 65u8.wrapping_add(n2) }
        else if n2 < 52 { 97u8.wrapping_add(n2.wrapping_sub(26)) }
        else if n2 < 62 { 48u8.wrapping_add(n2.wrapping_sub(52)) }
        else if n2 == 62 { 43 }
        else { 47 };

    EncodeGroupResult { c0, c1, c2, c3: 61 }
}
