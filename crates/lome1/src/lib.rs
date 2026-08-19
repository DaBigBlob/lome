#![no_std]
#![deny(
    clippy::panic,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::todo,
    clippy::unimplemented,
    clippy::unreachable,
    clippy::arithmetic_side_effects,
)]

extern crate alloc;
use alloc::{boxed::Box, string::String, vec::Vec};
use lome0 as modus;

type App<T> = modus::Tree<T>;

// in PTS outside, types, kinda, ... (axioms) will be constructors

/// Abstraction
#[derive(PartialEq, Eq)]
pub enum Expr{
    App(Box<App<Expr>>),
    Con{face:String, args:Vec<Expr>}, // constructor
    Err(Box<(Expr, Expr)>) // failed application
}
