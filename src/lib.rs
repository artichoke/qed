#![warn(clippy::all)]
#![warn(clippy::pedantic)]
#![warn(clippy::cargo)]
#![cfg_attr(test, allow(clippy::non_ascii_literal))]
#![cfg_attr(test, allow(clippy::shadow_unrelated))]
#![allow(unknown_lints)]
#![warn(missing_copy_implementations)]
#![warn(missing_debug_implementations)]
#![warn(missing_docs)]
#![warn(rust_2018_idioms)]
#![warn(trivial_casts, trivial_numeric_casts)]
#![warn(unused_qualifications)]
#![warn(variant_size_differences)]
// Enable feature callouts in generated documentation:
// https://doc.rust-lang.org/beta/unstable-book/language-features/doc-cfg.html
//
// This approach is borrowed from tokio.
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, feature(doc_alias))]

//! Compile time assertions.
//!
//! This crate contains compile time assertion macros used for maintaining safety
//! invariants or limiting platform support. If the assertion is false, a compiler
//! error is emitted.
//!
//! # Examples
//!
//! ```
//! # use core::num::NonZeroU8;
//! # #[cfg(any(target_pointer_width = "32", target_pointer_width = "64"))]
//! qed::const_assert!(usize::BITS >= u32::BITS);
//! qed::const_assert_eq!("Veni, vidi, vici".len(), "Cogito, ergo sum".len());
//! qed::const_assert_ne!('∎'.len_utf8(), 0);
//! qed::const_assert_matches!(NonZeroU8::new(42), Some(_));
//! ```
//!
//!
//! Assertion failures will result in a compile error:
//!
//! ```compile_fail
//! qed::const_assert!("non-empty string".is_empty());
//! ```

#![no_std]
#![doc(html_root_url = "https://docs.rs/qed/1.3.0")]

#[cfg(any(test, doc))]
extern crate std;

// Ensure code blocks in README.md compile
#[cfg(all(doctest, any(target_pointer_width = "32", target_pointer_width = "64")))]
#[doc = include_str!("../README.md")]
mod readme {}

/// Asserts that a boolean expression is true at compile time.
///
/// This will result in a compile time type error if the boolean expression does
/// not evaluate to true.
///
/// # Uses
///
/// Assertions are always checked in both debug and release builds and cannot be
/// disabled.
///
/// Unsafe code and [`as` casts][casts] may rely on `const_assert!` to enforce
/// runtime invariants that, if violated, could lead to unsafety.
///
/// [casts]: https://doc.rust-lang.org/nomicon/casts.html
///
/// Other use-cases of `const_assert!` include limiting supported platforms and
/// architectures.
///
/// # Examples
///
/// ```
/// // Assert at compile time that the target platform has at least 32-bit
/// // `usize`.
/// # #[cfg(any(target_pointer_width = "32", target_pointer_width = "64"))]
/// qed::const_assert!(usize::BITS >= u32::BITS);
/// ```
///
/// Assertion failures will result in a compile error:
///
/// ```compile_fail
/// qed::const_assert!("non-empty string".is_empty());
/// ```
#[macro_export]
macro_rules! const_assert {
    ($x:expr $(,)?) => {
        #[allow(unknown_lints, clippy::eq_op)]
        const _: [(); 0 - !{
            const ASSERT: bool = $x;
            ASSERT
        } as usize] = [];
    };
}

/// Asserts that two expressions are equal to each other (using [`PartialEq`])
/// at compile time.
///
/// See also [`const_assert!`].
///
/// # Examples
///
/// ```
/// qed::const_assert_eq!("Veni, vidi, vici".len(), "Cogito, ergo sum".len());
/// ```
///
/// The following fails to compile because the expressions are not equal:
///
/// ```compile_fail
/// qed::const_assert_eq!("Carpe diem".len(), "Et tu, Brute?".len());
/// ```
#[macro_export]
macro_rules! const_assert_eq {
    ($x:expr, $y:expr $(,)?) => {
        $crate::const_assert!($x == $y);
    };
}

/// Asserts that two expressions are not equal to each other (using
/// [`PartialEq`]) at compile time.
///
/// See also [`const_assert!`].
///
/// # Examples
///
/// ```
/// const END_OF_PROOF: char = '∎';
/// qed::const_assert_ne!(END_OF_PROOF.len_utf8(), 0);
/// ```
///
/// The following fails to compile because the expressions are equal:
///
/// ```compile_fail
/// const END_OF_PROOF: char = '∎';
/// qed::const_assert_ne!(END_OF_PROOF.len_utf8(), 3);
/// ```
#[macro_export]
macro_rules! const_assert_ne {
    ($x:expr, $y:expr $(,)?) => {
        $crate::const_assert!($x != $y);
    };
}

/// Asserts that an expression matches any of the given patterns at compile
/// time.
///
/// Like in a `match` expression, the pattern can be optionally followed by `if`
/// and a guard expression that has access to names bound by the pattern.
///
/// See also [`const_assert!`].
///
/// # Examples
///
/// ```
/// # use core::num::NonZeroU8;
/// qed::const_assert_matches!(NonZeroU8::new(0), None);
/// qed::const_assert_matches!(NonZeroU8::new(42), Some(_));
/// ```
///
/// Assertion failures will result in a compile error:
///
/// ```compile_fail
/// qed::const_assert_matches!(b"maybe c string".last(), Some(&0));
/// ```
#[macro_export]
macro_rules! const_assert_matches {
    ($left:expr, $(|)? $( $pattern:pat_param )|+ $( if $guard: expr )? $(,)?) => {
        $crate::const_assert!(match $left {
            $( $pattern )|+ $( if $guard )? => true,
            _ => false,
        });
    };
}

/// Cast a [`u32`] to [`usize`] at runtime with a compile time assert that the
/// cast is lossless and will not overflow.
///
/// This macro emits a compile time assertion that `usize` has at least as many
/// bits as `u32`.
///
/// # Examples
///
/// ```
/// # #![cfg(any(target_pointer_width = "32", target_pointer_width = "64"))]
/// #[derive(Default)]
/// struct SymbolTable {
///     next: u32,
///     table: [&'static str; 32],
/// }
///
/// impl SymbolTable {
///     pub fn intern(&mut self, symbol: &'static str) -> u32 {
///         let id = self.next;
///         let idx = qed::lossless_cast_u32_to_usize!(id);
///         self.table[idx] = symbol;
///         self.next += 1;
///         id
///     }
/// }
///
/// let mut table = SymbolTable::default();
/// assert_eq!(table.intern("end of proof"), 0);
/// assert_eq!(table.intern("∎"), 1);
/// ```
///
/// This macro requires a `u32` as its argument:
///
/// ```compile_fail
/// qed::lossless_cast_u32_to_usize!(0_i32);
/// ```
#[macro_export]
macro_rules! lossless_cast_u32_to_usize {
    ($num:expr) => {{
        $crate::const_assert!(usize::BITS >= u32::BITS);
        let num: u32 = $num;
        num as usize
    }};
}

/// Asserts that two types have the same size at compile time.
///
/// See also [`const_assert!`].
///
/// # Examples
///
/// ```
/// qed::const_assert_size_eq!(u8, i8);
/// qed::const_assert_size_eq!([u32; 4], i128);
/// qed::const_assert_size_eq!(&[u8], &str);
/// ```
///
/// The following fails to compile because the types have different sizes:
///
/// ```compile_fail
/// qed::const_assert_size_eq!(u8, u64);
/// ```
#[macro_export]
macro_rules! const_assert_size_eq {
    ($left:ty, $right:ty $(,)?) => {
        const _: () = {
            let _ = ::core::mem::transmute::<$left, $right>;
        };
    };
}

/// Asserts that a byte slice does not contain any NUL (`\0`) bytes.
///
/// This macro emits a compile error if the given slice contains any NUL bytes,
/// including a NUL terminator.
///
/// # Examples
///
/// ```
/// const ARRAY_CLASS: &[u8] = b"Array";
/// qed::const_assert_bytes_has_no_nul!(ARRAY_CLASS);
/// ```
///
/// The following fails to compile because the byte slice contains a NUL byte:
///
/// ```compile_fail
/// const BYTES: &[u8] = b"abc\0xyz";
/// qed::const_assert_bytes_has_no_nul!(BYTES);
/// ```
///
/// The following fails to compile because the byte slice contains a NUL
/// terminator:
///
/// ```compile_fail
/// const CSTR: &[u8] = b"Q.E.D.\x00";
/// qed::const_assert_bytes_has_no_nul!(CSTR);
/// ```
#[macro_export]
macro_rules! const_assert_bytes_has_no_nul {
    ($bytes:expr $(,)?) => {
        $crate::const_assert!({
            const fn byte_slice_contains(slice: &[u8], elem: u8) -> bool {
                let mut idx = 0;
                loop {
                    if idx >= slice.len() {
                        return false;
                    }
                    if slice[idx] == elem {
                        return true;
                    }
                    idx += 1;
                }
            }

            const BYTES: &[u8] = $bytes;
            !byte_slice_contains(BYTES, 0_u8)
        });
    };
}

/// Construct a const [`CStr`] from the given bytes at compile time and assert
/// that the given bytes are a valid `CStr` (NUL terminated with no interior NUL
/// bytes).
///
/// [`CStr`]: std::ffi::CStr
///
/// This macro emits a compile error if the given slice contains any interior
/// NUL bytes or does not have a NUL terminator.
///
/// # Examples
///
/// ```
/// use std::ffi::CStr;
///
/// const ARRAY_CLASS: &[u8] = b"Array\0";
/// const ARRAY_CLASS_CSTR: &CStr = qed::const_cstr_from_bytes!(ARRAY_CLASS);
/// ```
///
/// The following fails to compile because the byte slice contains an interior
/// NUL byte:
///
/// ```compile_fail
/// use std::ffi::CStr;
///
/// const BYTES: &[u8] = b"abc\0xyz";
/// const BYTES_CSTR: &CStr = qed::const_cstr_from_bytes!(BYTES);
/// ```
///
/// The following fails to compile because the byte slice does not contain a NUL
/// terminator:
///
/// ```compile_fail
/// use std::ffi::CStr;
///
/// const BYTES: &[u8] = b"Q.E.D.";
/// const BYTES_CSTR: &CStr = qed::const_cstr_from_bytes!(BYTES);
/// ```
///
/// The following fails to compile because the empty byte slice is not a valid
/// `CStr`:
///
/// ```compile_fail
/// use std::ffi::CStr;
///
/// const EMPTY: &[u8] = b"";
/// const CSTR: &CStr = qed::const_cstr_from_bytes!(BYTES);
/// ```
#[macro_export]
macro_rules! const_cstr_from_bytes {
    ($bytes:expr $(,)?) => {{
        const BYTES: &[u8] = $bytes;

        $crate::const_assert!({
            const fn byte_slice_is_cstr(slice: &[u8]) -> bool {
                let mut idx = slice.len() - 1;
                if slice[idx] != 0 {
                    return false;
                }
                loop {
                    if idx == 0 {
                        return true;
                    }
                    idx -= 1;
                    if slice[idx] == 0 {
                        return false;
                    }
                }
            }

            byte_slice_is_cstr(BYTES)
        });
        // SAFETY
        //
        // The compile time assert above ensures the given bytes:
        //
        // - Are NUL terminated
        // - Do not have any interior bytes
        //
        // which meets the safety criteria for `CStr::from_bytes_with_nul_unchecked`.
        //
        // https://doc.rust-lang.org/stable/std/ffi/struct.CStr.html#method.from_bytes_with_nul_unchecked
        unsafe { ::std::ffi::CStr::from_bytes_with_nul_unchecked(BYTES) }
    }};
}

/// Construct a const [`CStr`] from the given `str` at compile time and assert
/// that the given `str` bytes are a valid `CStr` (NUL terminated with no
/// interior NUL bytes).
///
/// [`CStr`]: std::ffi::CStr
///
/// This macro emits a compile error if the given slice contains any interior
/// NUL bytes or does not have a NUL terminator.
///
/// # Examples
///
/// ```
/// use std::ffi::CStr;
///
/// const ARRAY_CLASS_CSTR: &CStr = qed::const_cstr_from_str!("Array\0");
/// ```
///
/// The following fails to compile because the `str` slice contains an interior
/// NUL byte:
///
/// ```compile_fail
/// use std::ffi::CStr;
///
/// const CSTR: &CStr = qed::const_cstr_from_str!("abc\0xyz");
/// ```
///
/// The following fails to compile because the `str` slice does not contain a NUL
/// terminator:
///
/// ```compile_fail
/// use std::ffi::CStr;
///
/// const CSTR: &CStr = qed::const_cstr_from_str!("Q.E.D.");
/// ```
///
/// The following fails to compile because the empty string is not a valid
/// `CStr`:
///
/// ```compile_fail
/// use std::ffi::CStr;
///
/// const CSTR: &CStr = qed::const_cstr_from_str!("");
/// ```
#[macro_export]
macro_rules! const_cstr_from_str {
    ($str:expr $(,)?) => {{
        const STRING: &str = $str;
        $crate::const_cstr_from_bytes!(STRING.as_bytes())
    }};
}

#[cfg(test)]
mod tests {
    use core::num::NonZeroU8;
    use std::ffi::CStr;

    #[test]
    fn const_assert_no_warnings() {
        crate::const_assert!(true);
        crate::const_assert!(NonZeroU8::new(0).is_none());
        crate::const_assert!(NonZeroU8::new(29).is_some());
    }

    #[test]
    fn const_assert_eq_no_warnings() {
        crate::const_assert_eq!(i8::BITS, u8::BITS);
        crate::const_assert_eq!(u8::BITS, u8::BITS);
    }

    #[test]
    fn const_assert_eq_no_warnings_literals() {
        crate::const_assert_eq!(0, 0);
        crate::const_assert_eq!(29_i32, 29_i32);
    }

    #[test]
    fn const_assert_ne_no_warnings() {
        crate::const_assert_ne!(u32::BITS, u8::BITS);
    }

    #[test]
    fn const_assert_ne_no_warings_literals() {
        crate::const_assert_ne!(9, 99);
        crate::const_assert_ne!(0_i32, 29_i32);
    }

    #[test]
    fn const_assert_matches_no_warnings() {
        crate::const_assert_matches!(NonZeroU8::new(0), None);
        crate::const_assert_matches!(NonZeroU8::new(29), Some(x) if x.get() == 29);
    }

    #[test]
    fn const_assert_matches_no_warnings_literals() {
        crate::const_assert_matches!(None::<i8>, None);
        crate::const_assert_matches!(Some(0_i8), Some(_));

        crate::const_assert_matches!(None::<i8>, None::<i8>);
        crate::const_assert_matches!(Some(0_i8), Some(0_i8));
    }

    #[test]
    fn lossless_cast_u32_usize_no_warnings() {
        let n = crate::lossless_cast_u32_to_usize!(29_u32);
        assert_eq!(n, 29_usize);
    }

    #[test]
    fn lossless_cast_u32_usize_no_warnings_const() {
        const N: usize = crate::lossless_cast_u32_to_usize!(29_u32);
        assert_eq!(N, 29_usize);
    }

    #[test]
    fn size_eq_reference_transmute_no_warnings() {
        crate::const_assert_size_eq!(&[u8], &str);
    }

    #[test]
    fn size_eq_pointer_transmute_no_warnings() {
        crate::const_assert_size_eq!(*mut u8, *const u8);
    }

    #[test]
    fn const_assert_bytes_has_no_nul_no_warnings() {
        crate::const_assert_bytes_has_no_nul!("abcdefg".as_bytes());
        crate::const_assert_bytes_has_no_nul!("".as_bytes());
    }

    #[test]
    fn const_cstr_from_bytes_no_warnings() {
        const CSTR: &CStr = crate::const_cstr_from_bytes!("Array\0".as_bytes());
        const EMPTY: &CStr = crate::const_cstr_from_bytes!("\0".as_bytes());
        assert_eq!(CSTR.to_bytes(), b"Array");
        assert!(EMPTY.to_bytes().is_empty());
    }

    #[test]
    fn const_cstr_from_str_no_warnings() {
        const CSTR: &CStr = crate::const_cstr_from_str!("Array\0");
        const EMPTY: &CStr = crate::const_cstr_from_str!("\0");
        assert_eq!(CSTR.to_bytes(), b"Array");
        assert!(EMPTY.to_bytes().is_empty());
    }
}
