//! FFI annotation macros for tSwift verification.
//!
//! These macros annotate Rust functions for FFI boundary verification with Swift.
//! They are parsed by `tswift-ffi-verify` but have no runtime effect.
//!
//! # Usage
//!
//! ```rust,ignore
//! use tswift_ffi_macros::{ffi_export, ffi_requires, ffi_ensures, ffi_trusted};
//!
//! #[ffi_export]
//! #[ffi_requires("x > 0")]
//! #[ffi_ensures("result >= x")]
//! #[no_mangle]
//! pub extern "C" fn increment(x: i64) -> i64 {
//!     x + 1
//! }
//! ```
//!
//! # Attributes
//!
//! - `#[ffi_export]` or `#[ffi_export("custom_name")]` - Mark function as FFI export
//! - `#[ffi_requires("condition")]` - Precondition (caller must ensure)
//! - `#[ffi_ensures("condition")]` - Postcondition (callee must ensure)
//! - `#[ffi_trusted]` - Skip verification for this function

use proc_macro::TokenStream;
use syn::{LitStr, parse_macro_input};

/// Mark a function as an FFI export.
///
/// The optional argument specifies a custom export name (defaults to function name).
///
/// # Example
///
/// ```rust,ignore
/// #[ffi_export]
/// pub extern "C" fn my_func() {}
///
/// #[ffi_export("custom_name")]
/// pub extern "C" fn internal_name() {}
/// ```
#[proc_macro_attribute]
pub fn ffi_export(_attr: TokenStream, item: TokenStream) -> TokenStream {
    // No-op: pass through the function unchanged
    item
}

/// Specify a precondition for an FFI function.
///
/// The condition is a string that will be parsed by tswift-ffi-verify.
///
/// # Example
///
/// ```rust,ignore
/// #[ffi_requires("x > 0 && y != 0")]
/// pub extern "C" fn divide(x: i64, y: i64) -> i64 { x / y }
/// ```
#[proc_macro_attribute]
pub fn ffi_requires(attr: TokenStream, item: TokenStream) -> TokenStream {
    // Parse to validate the attribute is a string literal
    let _ = parse_macro_input!(attr as LitStr);
    item
}

/// Specify a postcondition for an FFI function.
///
/// The condition is a string that will be parsed by tswift-ffi-verify.
///
/// # Example
///
/// ```rust,ignore
/// #[ffi_ensures("result >= 0")]
/// pub extern "C" fn abs(x: i64) -> i64 { if x < 0 { -x } else { x } }
/// ```
#[proc_macro_attribute]
pub fn ffi_ensures(attr: TokenStream, item: TokenStream) -> TokenStream {
    // Parse to validate the attribute is a string literal
    let _ = parse_macro_input!(attr as LitStr);
    item
}

/// Mark a function as trusted (skip FFI verification).
///
/// Use this for functions that are unsafe or cannot be verified.
///
/// # Example
///
/// ```rust,ignore
/// #[ffi_trusted]
/// pub unsafe extern "C" fn raw_ptr_op(ptr: *mut u8) {}
/// ```
#[proc_macro_attribute]
pub fn ffi_trusted(_attr: TokenStream, item: TokenStream) -> TokenStream {
    // No-op: pass through the function unchanged
    item
}

#[cfg(test)]
mod tests {
    // Note: proc-macro tests are limited; integration tests are in the parent crate
}
