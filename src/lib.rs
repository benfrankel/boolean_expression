// boolean_expression: a Rust crate for Boolean expressions and BDDs.
//
// Copyright (c) 2016 Chris Fallin <cfallin@c1f.net>. Released under the MIT
// License.
//

#![allow(unused_imports)]
#![allow(dead_code)]

//! # boolean\_expression expression manipulation / BDD library
//!
//! This crate provides for the manipulation and evaluation of Boolean expressions
//! and Binary Decision Diagrams (BDDs), and the construction of BDDs from Boolean
//! expressions. It can also simplify Boolean expressions via either a set of rules
//! such as DeMorgan's Law (see `Expr::simplify_via_laws()`), or via a
//! roundtrip through a `Bdd` and a cubelist-based term reduction (see
//! `Expr::simplify_via_bdd()`). The latter is more powerful, but also more
//! expensive.
//!
//! The main pieces of interest are:
//!
//! * `Expr`, an AST enum for simple `AND` / `OR` / `NOT`-based expressions.
//! * `Bdd`, a Binary Decision Diagram implementation.
//! * `CubeList`, a low-level datatype with support for cubelist manipulation
//!   (used when converting `Bdd` functions to expressions).

mod bdd;
mod cubes;
mod expr;
mod idd;
mod simplify;

pub use bdd::*;
pub use cubes::*;
pub use expr::*;
pub(crate) use idd::*;
