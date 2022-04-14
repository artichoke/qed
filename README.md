# qed

[![GitHub Actions](https://github.com/artichoke/qed/workflows/CI/badge.svg)](https://github.com/artichoke/qed/actions)
[![Discord](https://img.shields.io/discord/607683947496734760)](https://discord.gg/QCe2tp2)
[![Twitter](https://img.shields.io/twitter/follow/artichokeruby?label=Follow&style=social)](https://twitter.com/artichokeruby)
<br>
[![Crate](https://img.shields.io/crates/v/qed.svg)](https://crates.io/crates/qed)
[![API](https://docs.rs/qed/badge.svg)](https://docs.rs/qed)
[![API trunk](https://img.shields.io/badge/docs-trunk-blue.svg)](https://artichoke.github.io/qed/qed/)

Compile time assertions.

> **_QED_** is an initialism of the Latin phrase **_quod erat demonstrandum_**,
> meaning "which was to be demonstrated".

This crate contains compile time assertion macros used for maintaining safety
invariants or limiting platform support. If the assertion is false, a compiler
error is emitted.

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
qed = "1.1.0"
```

Then make compile time assertions like:

```rust
use core::num::NonZeroU8;

qed::const_assert!(usize::BITS >= u32::BITS);
qed::const_assert_eq!("Veni, vidi, vici".len(), "Cogito, ergo sum".len());
qed::const_assert_ne!('∎'.len_utf8(), 0);
qed::const_assert_matches!(NonZeroU8::new(42), Some(_));
```

## `no_std`

qed is `no_std` compatible.

### Minimum Supported Rust Version

This crate requires at least Rust 1.56.0. This version can be bumped in minor
releases.

## License

`qed` is licensed under the [MIT License](LICENSE) (c) Ryan Lopopolo.
