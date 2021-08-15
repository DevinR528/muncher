# Muncher

[![Rust Stable](https://github.com/DevinR528/muncher/actions/workflows/stable.yml/badge.svg)](https://github.com/DevinR528/muncher/actions/workflows/stable.yml)
[![Latest Version](https://img.shields.io/crates/v/muncher.svg)](https://crates.io/crates/muncher)

## About
An easy to use string muncher that allows easy tokenization when writing a parser. Muncher has peek
and fork capabilities so you can look ahead and behind when needed. If lexing braces Muncher
has a built in brace matching stack accessed from `Muncher::brace_stack()`.

## Use
```toml
[dependencies]
muncher = "0.6"
```

## Examples
```rust
use muncher::Muncher;

let input = "hello\nworld";
let mut m = Muncher::new(input);

let hello = m.eat_until(|c| c == &'\n').collect::<String>();
assert_eq!(m.peek(), Some(&'\n'));
assert!(m.eat_eol());
```


#### License
<sup>
Licensed under either of <a href="LICENSE-APACHE">Apache License, Version
2.0</a> or <a href="LICENSE-MIT">MIT license</a> at your option.
</sup>

<br>

<sub>
Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in this project by you, as defined in the Apache-2.0 license,
shall be dual licensed as above, without any additional terms or conditions.
</sub>
