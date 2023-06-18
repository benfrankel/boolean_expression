// boolean_expression: a Rust crate for Boolean expressions and BDDs.
//
// Copyright (c) 2016 Chris Fallin <cfallin@c1f.net>. Released under the MIT
// License.
//

use std::cmp::Ord;
use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;
use std::ops::BitAnd;
use std::ops::BitAndAssign;
use std::ops::BitOr;
use std::ops::BitOrAssign;
use std::ops::BitXor;
use std::ops::BitXorAssign;
use std::ops::Not;

#[cfg(feature = "bevy_reflect")]
use bevy_reflect_derive::{FromReflect, Reflect};

use crate::simplify;

/// An `Expr` is a simple Boolean logic expression. It may contain terminals
/// (i.e., free variables), constants, and the following fundamental operations:
/// AND, OR, NOT.
///
/// ```
/// use std::collections::HashMap;
/// use boolean_expression::Expr;
///
/// #[derive(Clone, Hash, Eq, PartialEq, Debug)]
/// enum RiverCrossing { Chicken, Fox, Grain }
///
/// let chicken = Expr::Terminal(RiverCrossing::Chicken);
/// let fox_and_grain = Expr::Terminal(RiverCrossing::Fox) & Expr::Terminal(RiverCrossing::Grain);
///
/// let allowed = (!chicken.clone() & fox_and_grain.clone()) | (chicken & !fox_and_grain);
/// let items = [
///    (RiverCrossing::Grain, true),
///    (RiverCrossing::Fox, true),
/// ].iter().cloned().collect();
///
/// // nobody gets eaten!
/// assert!(allowed.evaluate(&items));
/// ```
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "bevy_reflect", derive(Reflect, FromReflect))]
pub enum Expr<T> {
    /// A terminal (free variable). This expression node represents a value that
    /// is not known until evaluation time.
    Terminal(T),
    /// A boolean constant: true or false.
    Const(bool),

    /// The logical complement of the contained expression argument.
    Not(Box<Expr<T>>),

    /// The logical AND of the two expression arguments.
    And(Box<Expr<T>>, Box<Expr<T>>),

    /// The logical OR of the two expression arguments.
    Or(Box<Expr<T>>, Box<Expr<T>>),
}

impl<T> Expr<T> {
    /// Returns `true` if this `Expr` is a terminal.
    pub fn is_terminal(&self) -> bool {
        matches!(self, Self::Terminal(..))
    }

    /// Returns `true` if this `Expr` is a constant.
    pub fn is_const(&self) -> bool {
        matches!(self, Self::Const(..))
    }

    /// Returns `true` if this `Expr` is a NOT node.
    pub fn is_not(&self) -> bool {
        matches!(self, Self::Not(..))
    }

    /// Returns `true` if this `Expr` is an AND node.
    pub fn is_and(&self) -> bool {
        matches!(self, Self::And(..))
    }

    /// Returns `true` if this `Expr` is an OR node.
    pub fn is_or(&self) -> bool {
        matches!(self, Self::Or(..))
    }

    /// Builds an AND node around two arguments, consuming the argument
    /// expressions.
    pub fn and(self, rhs: Self) -> Self {
        Self::And(Box::new(self), Box::new(rhs))
    }

    /// Builds an OR node around two arguments, consuming the argument
    /// expressions.
    pub fn or(self, rhs: Self) -> Self {
        Self::Or(Box::new(self), Box::new(rhs))
    }

    /// Evaluates the expression using the provided function to map terminals
    /// (variables) to boolean values. This is a generalization of
    /// [`Expr::evaluate`], where the variable lookup in a hashmap is replaced
    /// with an arbitrary computation.
    ///
    ///```
    /// use boolean_expression::Expr;
    ///
    /// let expression = Expr::Terminal(10) | Expr::Terminal(3);
    ///
    /// // check if the expression satisfies a predicate
    /// assert!(expression.evaluate_with(|&x| x > 5));
    /// ```
    pub fn evaluate_with<F>(&self, f: F) -> bool
    where
        F: Fn(&T) -> bool,
    {
        self.evaluate_with_helper(&f)
    }

    fn evaluate_with_helper<F>(&self, f: F) -> bool
    where
        F: Copy + Fn(&T) -> bool,
    {
        match self {
            Self::Terminal(t) => f(t),
            &Self::Const(val) => val,
            Self::Not(x) => !x.evaluate_with_helper(f),
            Self::And(a, b) => a.evaluate_with_helper(f) && b.evaluate_with_helper(f),
            Self::Or(a, b) => a.evaluate_with_helper(f) || b.evaluate_with_helper(f),
        }
    }

    /// Map terminal values using the specified mapping function.
    pub fn map<F, R>(&self, f: F) -> Expr<R>
    where
        F: Fn(&T) -> R,
    {
        self.map_helper(&f)
    }

    fn map_helper<F, R>(&self, f: F) -> Expr<R>
    where
        F: Copy + Fn(&T) -> R,
    {
        match self {
            Self::Terminal(t) => Expr::Terminal(f(t)),
            &Self::Const(val) => Expr::Const(val),
            Self::Not(n) => !n.map_helper(f),
            Self::And(a, b) => Expr::and(a.map_helper(f), b.map_helper(f)),
            Self::Or(a, b) => Expr::or(a.map_helper(f), b.map_helper(f)),
        }
    }
}

impl<T: Clone> Expr<T> {
    pub fn xor(self, rhs: Self) -> Self {
        let nand = !(self.clone() & rhs.clone());
        let or = self | rhs;
        nand & or
    }
}

impl<T: PartialEq + Clone> Expr<T> {
    /// Simplify an expression in a relatively cheap way using well-known logic
    /// identities.
    ///
    /// This function performs certain reductions using DeMorgan's Law,
    /// distribution of ANDs over ORs, and certain identities involving
    /// constants, to simplify an expression. The result will always be in
    /// sum-of-products form: nodes will always appear in order (from
    /// expression tree root to leaves) `OR -> AND -> NOT`. In other words,
    /// `AND` nodes may only have `NOT` nodes (or terminals or constants) as
    /// children, and `NOT` nodes may only have terminals or constants as
    /// children.
    ///
    /// This function explicitly does *not* perform any sort of minterm reduction.
    /// The terms may thus be redundant (i.e., `And(a, b)` may appear twice), and
    /// combinable terms may exist (i.e., `And(a, b)` and `And(a, Not(b))` may
    /// appear in the `OR`'d list of terms, where these could be combined to
    /// simply `a` but are not). For example:
    ///
    /// ```
    /// use boolean_expression::Expr;
    ///
    /// // This simplifies using DeMorgan's Law:
    /// let expr = !Expr::or(Expr::Terminal(0), Expr::Terminal(1));
    /// let simplified = expr.simplify_via_laws();
    /// assert_eq!(
    ///     simplified,
    ///     Expr::and(!Expr::Terminal(0), !Expr::Terminal(1)),
    /// );
    ///
    /// // This doesn't simplify, though:
    /// let expr = Expr::or(
    ///     Expr::and(Expr::Terminal(0), Expr::Terminal(1)),
    ///     Expr::and(Expr::Terminal(0), !Expr::Terminal(1)),
    /// );
    /// let simplified = expr.clone().simplify_via_laws();
    /// assert_eq!(simplified, expr);
    /// ```
    ///
    /// For better (but more expensive) simplification, see `simplify_via_bdd()`.
    pub fn simplify_via_laws(self) -> Self {
        simplify::simplify_via_laws(self)
    }
}

impl<T: Eq + Hash> Expr<T> {
    /// Evaluates the expression with a particular set of terminal assignments.
    /// If any terminals are not assigned, they default to `false`.
    pub fn evaluate(&self, vals: &HashMap<T, bool>) -> bool {
        match self {
            Self::Terminal(t) => *vals.get(t).unwrap_or(&false),
            &Self::Const(val) => val,
            Self::Not(x) => !x.evaluate(vals),
            Self::And(a, b) => a.evaluate(vals) && b.evaluate(vals),
            Self::Or(a, b) => a.evaluate(vals) || b.evaluate(vals),
        }
    }
}

impl<T: Eq + Hash + Clone> Expr<T> {
    /// Simplify an expression via a roundtrip through a `Bdd`. This procedure
    /// is more effective than `Expr::simplify_via_laws()`, but more expensive.
    /// This roundtrip will implicitly simplify an arbitrarily complicated
    /// function (by construction, as the BDD is built), and then find a
    /// quasi-minimal set of terms using cubelist-based reduction. For example:
    ///
    /// ```
    /// use boolean_expression::Expr;
    ///
    /// // `simplify_via_laws()` cannot combine these terms, but
    /// // `simplify_via_bdd()` will:
    /// let expr = Expr::or(
    ///     Expr::and(Expr::Terminal(0), Expr::Terminal(1)),
    ///     Expr::and(Expr::Terminal(0), !Expr::Terminal(1)),
    /// );
    /// let simplified = expr.simplify_via_bdd();
    /// assert_eq!(simplified, Expr::Terminal(0));
    /// ```
    pub fn simplify_via_bdd(self) -> Self {
        simplify::simplify_via_bdd(self)
    }
}

impl<T> Not for Expr<T> {
    type Output = Self;

    /// Builds a NOT node around an argument, consuming the argument
    /// expression.
    fn not(self) -> Self::Output {
        Self::Not(Box::new(self))
    }
}

impl<T> BitAnd for Expr<T> {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        self.and(rhs)
    }
}

impl<T: Clone> BitAndAssign for Expr<T> {
    fn bitand_assign(&mut self, rhs: Self) {
        *self = self.clone().and(rhs);
    }
}

impl<T> BitOr for Expr<T> {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        self.or(rhs)
    }
}

impl<T: Clone> BitOrAssign for Expr<T> {
    fn bitor_assign(&mut self, rhs: Self) {
        *self = self.clone().or(rhs)
    }
}

impl<T: Clone> BitXor for Expr<T> {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        self.xor(rhs)
    }
}

impl<T: Clone> BitXorAssign for Expr<T> {
    fn bitxor_assign(&mut self, rhs: Self) {
        *self = self.clone().xor(rhs);
    }
}
