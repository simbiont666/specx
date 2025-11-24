//! # specx
//!
//! A lightweight, zero-allocation implementation of the *Specification Pattern*
//! for Rust. This crate provides:
//!
//! * predicate-based specifications via [`spec_fn`],
//! * boolean combinators (`and`, `or`, `not`),
//! * an expression-style DSL through the [`spec!`] macro,
//! * fully static typing with no dynamic dispatch.
//!
//!
//! ## Quick example
//!
//! ```rust
//! use specx::{Specification, spec_fn, spec};
//!
//! #[derive(Debug)]
//! struct User {
//!     age: u8,
//!     is_admin: bool,
//! }
//!
//! let adult = spec_fn(|u: &User| u.age >= 18);
//! let admin = spec_fn(|u: &User| u.is_admin);
//!
//! // Expression-style DSL: a user is valid if they are an adult OR an admin.
//! let rule = spec!(adult | admin);
//!
//! let u1 = User { age: 17, is_admin: true };
//! let u2 = User { age: 17, is_admin: false };
//!
//! assert!(rule.is_satisfied_by(&u1));
//! assert!(!rule.is_satisfied_by(&u2));
//! ```
//!
//! ## Key components
//!
//! - [`Specification`] — the core trait.
//! - [`spec_fn`] — build specifications from predicates.
//! - [`AndSpecification`], [`OrSpecification`], [`NotSpecification`] — boolean combinators.
//! - [`spec!`] — a small DSL with `!`, `&`, `|`, and parentheses.

/// Represents a predicate over a candidate value.
///
/// A `Specification<Candidate>` answers the question:
/// “Does this value satisfy the rule?”
///
/// Specifications can be composed using the built-in boolean combinators
/// provided by this trait: [`and`](Specification::and),
/// [`or`](Specification::or), and [`not`](Specification::not).
///
/// # Example
/// ```rust
/// use specx::Specification;
///
/// struct User { age: u8, is_admin: bool }
///
/// struct IsAdult;
///
/// impl Specification<User> for IsAdult {
///     fn is_satisfied_by(&self, u: &User) -> bool {
///         u.age >= 18
///     }
/// }
///
/// let user = User { age: 20, is_admin: false };
/// assert!(IsAdult.is_satisfied_by(&user));
/// ```
pub trait Specification<Candidate: ?Sized> {
    /// Returns `true` if the candidate satisfies this specification.
    ///
    /// # Example
    /// ```rust
    /// use specx::Specification;
    ///
    /// struct IsEven;
    /// impl Specification<u32> for IsEven {
    ///     fn is_satisfied_by(&self, x: &u32) -> bool { x % 2 == 0 }
    /// }
    ///
    /// assert!(IsEven.is_satisfied_by(&4));
    /// assert!(!IsEven.is_satisfied_by(&3));
    /// ```
    fn is_satisfied_by(&self, candidate: &Candidate) -> bool;

    /// Logical AND of two specifications.
    ///
    /// The resulting specification is satisfied only if **both**
    /// operands are satisfied.
    ///
    /// # Example
    /// ```rust
    /// use specx::Specification;
    ///
    /// struct Positive;
    /// struct Even;
    ///
    /// impl Specification<i32> for Positive {
    ///     fn is_satisfied_by(&self, x: &i32) -> bool { *x > 0 }
    /// }
    /// impl Specification<i32> for Even {
    ///     fn is_satisfied_by(&self, x: &i32) -> bool { x % 2 == 0 }
    /// }
    ///
    /// let s = Positive.and(Even);
    /// assert!(s.is_satisfied_by(&4));
    /// assert!(!s.is_satisfied_by(&3));
    /// assert!(!s.is_satisfied_by(&-2));
    /// ```
    fn and<S>(self, other: S) -> AndSpecification<Self, S>
    where
        S: Specification<Candidate>,
        Self: Sized,
    {
        AndSpecification {
            left: self,
            right: other,
        }
    }

    /// Logical OR of two specifications.
    ///
    /// The resulting specification is satisfied if **either**
    /// operand is satisfied.
    ///
    /// # Example
    /// ```rust
    /// use specx::Specification;
    ///
    /// struct IsZero;
    /// struct IsOne;
    ///
    /// impl Specification<u8> for IsZero {
    ///     fn is_satisfied_by(&self, x: &u8) -> bool { *x == 0 }
    /// }
    /// impl Specification<u8> for IsOne {
    ///     fn is_satisfied_by(&self, x: &u8) -> bool { *x == 1 }
    /// }
    ///
    /// let s = IsZero.or(IsOne);
    ///
    /// assert!(s.is_satisfied_by(&0));
    /// assert!(s.is_satisfied_by(&1));
    /// assert!(!s.is_satisfied_by(&2));
    /// ```
    fn or<S>(self, other: S) -> OrSpecification<Self, S>
    where
        S: Specification<Candidate>,
        Self: Sized,
    {
        OrSpecification {
            left: self,
            right: other,
        }
    }

    /// Logical negation of a specification.
    ///
    /// # Example
    /// ```rust
    /// use specx::Specification;
    ///
    /// struct IsEven;
    /// impl Specification<u32> for IsEven {
    ///     fn is_satisfied_by(&self, x: &u32) -> bool { x % 2 == 0 }
    /// }
    ///
    /// let s = IsEven.not();
    ///
    /// assert!(s.is_satisfied_by(&3));
    /// assert!(!s.is_satisfied_by(&4));
    /// ```
    fn not(self) -> NotSpecification<Self>
    where
        Self: Sized,
    {
        NotSpecification { inner: self }
    }
}

/// Specification representing logical AND (`left AND right`).
///
/// Usually created via [`Specification::and`].
///
/// # Example
/// ```rust
/// use specx::{Specification, spec_fn};
///
/// let even = spec_fn(|x: &i32| x % 2 == 0);
/// let positive = spec_fn(|x: &i32| *x > 0);
///
/// let s = even.and(positive);
/// assert!(s.is_satisfied_by(&6));
/// assert!(!s.is_satisfied_by(&-4));
/// assert!(!s.is_satisfied_by(&3));
/// ```
pub struct AndSpecification<Left, Right> {
    left: Left,
    right: Right,
}

/// Specification representing logical OR (`left OR right`).
///
/// # Example
/// ```rust
/// use specx::{Specification, spec_fn};
///
/// let is_0 = spec_fn(|x: &u8| *x == 0);
/// let is_1 = spec_fn(|x: &u8| *x == 1);
///
/// let s = is_0.or(is_1);
/// assert!(s.is_satisfied_by(&0));
/// assert!(s.is_satisfied_by(&1));
/// assert!(!s.is_satisfied_by(&2));
/// ```
pub struct OrSpecification<Left, Right> {
    left: Left,
    right: Right,
}

/// Specification representing logical NOT (`!inner`).
///
/// # Example
/// ```rust
/// use specx::{Specification, spec_fn};
///
/// let positive = spec_fn(|x: &i32| *x > 0);
/// let not_positive = positive.not();
///
/// assert!(not_positive.is_satisfied_by(&-1));
/// assert!(!not_positive.is_satisfied_by(&5));
/// ```
pub struct NotSpecification<S> {
    inner: S,
}

impl<S, Candidate> Specification<Candidate> for NotSpecification<S>
where
    S: Specification<Candidate>,
{
    fn is_satisfied_by(&self, candidate: &Candidate) -> bool {
        !self.inner.is_satisfied_by(candidate)
    }
}

impl<Candidate, Left, Right> Specification<Candidate> for AndSpecification<Left, Right>
where
    Left: Specification<Candidate>,
    Right: Specification<Candidate>,
{
    fn is_satisfied_by(&self, candidate: &Candidate) -> bool {
        self.left.is_satisfied_by(candidate) && self.right.is_satisfied_by(candidate)
    }
}

impl<Candidate, Left, Right> Specification<Candidate> for OrSpecification<Left, Right>
where
    Left: Specification<Candidate>,
    Right: Specification<Candidate>,
{
    fn is_satisfied_by(&self, candidate: &Candidate) -> bool {
        self.left.is_satisfied_by(candidate) || self.right.is_satisfied_by(candidate)
    }
}

/// Specification defined by a predicate function or closure.
///
/// Wraps any `Fn(&Candidate) -> bool`.
///
/// Created via [`spec_fn`].
///
/// # Example
/// ```rust
/// use specx::{Specification, spec_fn};
///
/// let is_even = spec_fn(|x: &i32| x % 2 == 0);
///
/// assert!(is_even.is_satisfied_by(&4));
/// assert!(!is_even.is_satisfied_by(&3));
/// ```
pub struct PredicateSpec<F>(F);

impl<Candidate, F> Specification<Candidate> for PredicateSpec<F>
where
    F: Fn(&Candidate) -> bool,
{
    fn is_satisfied_by(&self, candidate: &Candidate) -> bool {
        (self.0)(candidate)
    }
}

/// Constructs a specification from a closure or function.
///
///
/// # Example
/// ```rust
/// use specx::{Specification, spec_fn};
///
/// #[derive(Debug)]
/// struct User { age: u8 }
///
/// let adult = spec_fn(|u: &User| u.age >= 18);
///
/// let u1 = User { age: 20 };
/// let u2 = User { age: 15 };
///
/// assert!(adult.is_satisfied_by(&u1));
/// assert!(!adult.is_satisfied_by(&u2));
/// ```
pub fn spec_fn<Candidate, F>(f: F) -> PredicateSpec<F>
where
    F: Fn(&Candidate) -> bool,
{
    PredicateSpec(f)
}

/// A small expression-style DSL for composing specifications.
///
/// Supported operators (by precedence):
///
/// * `!spec` — negation  
/// * `&` — logical AND  
/// * `|` — logical OR  
///
/// Parentheses `(...)` control grouping.
/// All leaf expressions must evaluate to something implementing
/// [`Specification`].
///
/// # Examples
///
/// Basic usage:
/// ```rust
/// use specx::{Specification, spec_fn, spec};
///
/// let even = spec_fn(|x: &i32| x % 2 == 0);
/// let positive = spec_fn(|x: &i32| *x > 0);
///
/// let s = spec!(even & positive);
///
/// assert!(s.is_satisfied_by(&4));
/// assert!(!s.is_satisfied_by(&-2));
/// ```
///
/// Operator precedence (AND binds tighter than OR):
/// ```rust
/// use specx::{Specification, spec_fn, spec};
///
/// let a = spec_fn(|_: &i32| false);
/// let b = spec_fn(|_: &i32| false);
/// let c = spec_fn(|_: &i32| true);
///
/// // Parsed as: (a & b) | c
/// let s = spec!(a & b | c);
///
/// assert!(s.is_satisfied_by(&0));
/// ```
///
/// Parentheses:
/// ```rust
/// use specx::{Specification, spec_fn, spec};
///
/// let a = spec_fn(|x: &i32| *x > 0);
/// let b = spec_fn(|x: &i32| *x == 10);
/// let c = spec_fn(|x: &i32| *x == 20);
///
/// let s = spec!(a & (b | c));
///
/// assert!(s.is_satisfied_by(&10));
/// assert!(s.is_satisfied_by(&20));
/// assert!(!s.is_satisfied_by(&-5));
/// ```
///
/// Using negation:
/// ```rust
/// use specx::{Specification, spec_fn, spec};
///
/// let zero = spec_fn(|x: &i32| *x == 0);
/// let positive = spec_fn(|x: &i32| *x > 0);
///
/// let s = spec!(!zero & positive);
///
/// assert!(s.is_satisfied_by(&5));
/// assert!(!s.is_satisfied_by(&0));
/// ```
#[macro_export]
macro_rules! spec {
    (@or [$($lhs:tt)*] | $($rest:tt)+) => {
        spec!(@and [] $($lhs)*).or(spec!(@or [] $($rest)+))
    };

    (@or [$($lhs:tt)*] $tok:tt $($rest:tt)*) => {
        spec!(@or [$($lhs)* $tok] $($rest)*)
    };

    (@or [$($lhs:tt)*]) => {
        spec!(@and [] $($lhs)*)
    };

    (@and [$($lhs:tt)*] & $($rest:tt)+) => {
        spec!(@not $($lhs)*).and(spec!(@and [] $($rest)+))
    };

    (@and [$($lhs:tt)*] $tok:tt $($rest:tt)*) => {
        spec!(@and [$($lhs)* $tok] $($rest)*)
    };

    (@and [$($lhs:tt)*]) => {
        spec!(@not $($lhs)*)
    };

    (@not ! $($rest:tt)+) => {
        spec!(@not $($rest)+).not()
    };

    (@not ($($inner:tt)+)) => {
        spec!(@or [] $($inner)+)
    };

    (@not $leaf:expr) => {
        $leaf
    };

    ($($tokens:tt)+) => {
        spec!(@or [] $($tokens)+)
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Debug)]
    struct Cand {
        a: bool,
        b: bool,
        c: bool,
        d: bool,
    }

    struct A;
    struct B;
    struct C;
    struct D;

    impl Specification<Cand> for A {
        fn is_satisfied_by(&self, c: &Cand) -> bool {
            c.a
        }
    }
    impl Specification<Cand> for B {
        fn is_satisfied_by(&self, c: &Cand) -> bool {
            c.b
        }
    }
    impl Specification<Cand> for C {
        fn is_satisfied_by(&self, c: &Cand) -> bool {
            c.c
        }
    }
    impl Specification<Cand> for D {
        fn is_satisfied_by(&self, c: &Cand) -> bool {
            c.d
        }
    }

    #[test]
    fn spec_and_or_precedence_matches_manual() {
        let macro_spec = spec!(A & B | C);

        let manual: OrSpecification<AndSpecification<A, _>, _> = A.and(B).or(C);

        let manual_alt = A.and(B.or(C));

        let cand = Cand {
            a: false,
            b: false,
            c: true,
            d: false,
        };

        assert_eq!(
            macro_spec.is_satisfied_by(&cand),
            manual.is_satisfied_by(&cand),
            "macro_spec must behave like (A & B) | C",
        );

        assert_ne!(
            macro_spec.is_satisfied_by(&cand),
            manual_alt.is_satisfied_by(&cand),
            "macro_spec must NOT behave like A & (B | C)",
        );
    }

    #[test]
    fn spec_respects_parentheses() {
        let macro_spec = spec!(A & (B | C));
        let manual = A.and(B.or(C));

        let cand = Cand {
            a: true,
            b: false,
            c: true,
            d: false,
        };

        assert_eq!(
            macro_spec.is_satisfied_by(&cand),
            manual.is_satisfied_by(&cand),
        );
    }

    #[test]
    fn spec_not_and_or() {
        let macro_spec = spec!(!A & B | C);
        let manual = A.not().and(B).or(C);

        let cand = Cand {
            a: true,
            b: true,
            c: false,
            d: false,
        };

        assert_eq!(
            macro_spec.is_satisfied_by(&cand),
            manual.is_satisfied_by(&cand),
        );
    }

    #[test]
    fn spec_multiple_and_with_parens() {
        let macro_spec = spec!(A & B & (C | D));
        let manual = A.and(B).and(C.or(D));

        let cand = Cand {
            a: true,
            b: true,
            c: false,
            d: true,
        };

        assert_eq!(
            macro_spec.is_satisfied_by(&cand),
            manual.is_satisfied_by(&cand),
        );
    }
}
