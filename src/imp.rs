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

#[must_use]
pub const fn is_cstr(slice: &[u8]) -> bool {
    matches!(find(slice, 0), Some(nul_pos) if nul_pos + 1 == slice.len())
}

// Enforce that the given argument is a `bool`. Returns the given argument.
pub const fn assert_bool(b: bool) -> bool {
    b
}

// Return the given `bool` cast to `usize`.
pub const fn bool_as_idx(b: bool) -> usize {
    b as usize
}

// Enforce that the given argument is a `&[u8]`. Returns the given argument.
pub const fn assert_is_byte_slice(bytes: &[u8]) -> &[u8] {
    bytes
}

// Enforce that the given argument is a `&str`. Returns the given argument.
pub const fn assert_is_str(s: &str) -> &str {
    s
}

#[cfg(test)]
mod tests {
    use super::{find, is_cstr};

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
}
