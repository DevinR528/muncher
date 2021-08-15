//! `muncher` is a library for lexing a string of text input. The main struct
//! `Muncher` can be crated from any `&str` and forks or peeking and seeking without
//! moving the cursor forward can be accomplished via [`fork`](Muncher::fork),
//! [`peek`](Muncher::peek) and [`seek`](Muncher::seek).
//!
//! # Creation and Peeking
//! ```
//! use muncher::Muncher;
//!
//! let input = "hello world";
//! let m = Muncher::new(input);
//!
//! assert_eq!(m.seek(5), Some("hello".to_string()));
//! assert_eq!(m.peek(), Some(&' '));
//! assert_eq!(m.seek(5), Some("world".to_string()));
//! assert!(m.peek().is_none());
//! ```
//! ```
//! # use muncher::Muncher;
//! let input = "abcde";
//! let mut munch = Muncher::new(input);
//! assert_eq!(munch.eat(), Some('a'));
//!
//! let fork = munch.fork();
//! assert_eq!(fork.peek(), Some(&'b'));
//! assert_eq!(munch.eat(), Some('b'));
//! ```
//!
//! `Muncher` has many `eat_*` methods as well as [`eat`](Muncher::eat) that are used to
//! advance the cursor. `eat` returns an `Option<char>` if you want to use the returned
//! char. Another way of advancing the cursor is the [`eat_until`](Muncher::eat_until),
//! [`eat_until_count`](Muncher::eat_until_count) and
//! [`eat_range_of`](Muncher::eat_range_of) methods.
//!
//! ## eat_until
//! ```
//! use muncher::Muncher;
//!
//! let input = "abcde";
//! let mut munch = Muncher::new(input);
//!
//! let text = munch.eat_until(|ch| ch == &'d').collect::<String>();
//! assert_eq!(text, "abc");
//! assert_eq!(munch.eat(), Some('d'));
//! ```
//!
//! `eat_until_count` works the same but returns (usize, usize) as (start, end).
//!
//! ## eat_range_of
//! ```
//! use muncher::Muncher;
//!
//! let input = "abcde";
//! let mut munch = Muncher::new(input);
//!
//! let (start, end) = munch.eat_range_of("d");
//! assert_eq!(&munch.text()[start..end], "abc");
//! assert_eq!(munch.eat(), Some('d'));
//! ```
mod muncher;

pub use crate::muncher::{Fork, Muncher, Stack, StackResult};
