# specx — minimal Specification utilities for Rust [![Latest Version]][crates.io] [![Docs]][docs.rs]

[Latest Version]: https://img.shields.io/crates/v/specx.svg
[crates.io]: https://crates.io/crates/specx
[Docs]: https://docs.rs/specx/badge.svg
[docs.rs]: https://docs.rs/specx/0.1.0/specx/

`specx` is a tiny, zero-dependency crate implementing the [Specification pattern](https://en.wikipedia.org/wiki/Specification_pattern) with ergonomic boolean combinators and a lightweight macro DSL.

## Goals

* Zero dependencies and minimal overhead.
* Generic, zero-cost combinators with full static typing.
* Compact DSL for building expressions: `spec!(A & (B | !C))`.
* Helpers for predicate-based specifications: `spec_fn(|x| ...)`.

## Example

```rust
use specx::{Specification, spec};

struct IsAdult;
struct IsAdmin;

struct User {
    age: u8,
    is_admin: bool,
}

impl Specification<User> for IsAdult {
    fn is_satisfied_by(&self, u: &User) -> bool { u.age >= 18 }
}

impl Specification<User> for IsAdmin {
    fn is_satisfied_by(&self, u: &User) -> bool { u.is_admin }
}

let combined = spec!(IsAdult & !IsAdmin);

let u = User { age: 20, is_admin: false };
assert!(combined.is_satisfied_by(&u));
```
