// Return the first index, if any, where the given byte occurs.
#[must_use]
pub const fn find(slice: &[u8], elem: u8) -> Option<usize> {
    let mut idx = 0;
    loop {
        if idx == slice.len() {
            return None;
        }
        if slice[idx] == elem {
            return Some(idx);
        }
        idx += 1;
    }
}

// Return true if the slice contains a single NUL byte in the last position of
// the slice.
#[must_use]
pub const fn is_cstr(slice: &[u8]) -> bool {
    matches!(find(slice, 0), Some(nul_pos) if nul_pos + 1 == slice.len())
}

// Returns true if the slice contains any NUL bytes.
#[must_use]
pub const fn contains_nul(slice: &[u8]) -> bool {
    matches!(find(slice, 0), Some(_))
}

#[cfg(test)]
mod tests {
    use super::{contains_nul, find, is_cstr};

    #[test]
    fn find_nul_byte() {
        assert_eq!(find(b"", 0), None);
        assert_eq!(find(b"abc", 0), None);
        assert_eq!(find(b"abc\xFFxyz", 0), None);

        assert_eq!(find(b"abc\0xyz", 0), Some(3));
        assert_eq!(find(b"abc\0xyz\0", 0), Some(3));
        assert_eq!(find(b"abc\xFF\0xyz", 0), Some(4));
        assert_eq!(find(b"abc\xFF\0xyz\0", 0), Some(4));

        assert_eq!(find(b"\0", 0), Some(0));
        assert_eq!(find(b"abc\0", 0), Some(3));
        assert_eq!(find(b"abc\xFFxyz\0", 0), Some(7));
    }

    #[test]
    fn check_is_cstr() {
        assert!(!is_cstr(b""));
        assert!(!is_cstr(b"abc"));
        assert!(!is_cstr(b"abc\xFFxyz"));

        assert!(!is_cstr(b"abc\0xyz"));
        assert!(!is_cstr(b"abc\0xyz\0"));
        assert!(!is_cstr(b"abc\xFF\0xyz"));
        assert!(!is_cstr(b"abc\xFF\0xyz\0"));

        assert!(is_cstr(b"\0"));
        assert!(is_cstr(b"abc\0"));
        assert!(is_cstr(b"abc\xFFxyz\0"));
    }

    #[test]
    fn check_contains_nul_byte() {
        assert!(!contains_nul(b""));
        assert!(!contains_nul(b"abc"));
        assert!(!contains_nul(b"abc\xFFxyz"));

        assert!(contains_nul(b"abc\0xyz"));
        assert!(contains_nul(b"abc\0xyz\0"));
        assert!(contains_nul(b"abc\xFF\0xyz"));
        assert!(contains_nul(b"abc\xFF\0xyz\0"));

        assert!(contains_nul(b"\0"));
        assert!(contains_nul(b"abc\0"));
        assert!(contains_nul(b"abc\xFFxyz\0"));
    }
}
