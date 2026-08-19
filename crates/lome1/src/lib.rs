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
use alloc::boxed::Box;
use lome0 as modus;

type App<M> = modus::Tree<M>;

// in PTS outside, types, kinda, ... (axioms) will be constructors

/// Expression: Abstraction + Application
#[derive(PartialEq, Eq)]
pub enum Tree<Leaf>{
    Abs(Box<(Tree<Leaf>, Tree<Leaf>)>),
    App(Box<App<Tree<Leaf>>>),
    Lea(Leaf),
}
