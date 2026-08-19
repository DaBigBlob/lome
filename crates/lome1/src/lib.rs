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
use lome0;

// constructors do:
// constructors(constructors) -> constructors
pub trait ConApplicator<Con> {
    type ConAppTask;
    fn task(&mut self, operator:Con, operand:Con) -> Self::ConAppTask;
    fn completed(&mut self, task:Self::ConAppTask) -> Con;
}

// we must recognize that we are the Leaf implementors
#[derive(PartialEq, Eq)]
pub enum Leaf<Con>{
    Abs(Box<(Leaf<Con>, Leaf<Con>)>),
    App(lome0::Tree<Box<Leaf<Con>>>), // we impl apply for this
    ConTree(Con)
}
// norm:
// keep normalizing Leaf::App(lome0::Tree<Box<Leaf<Con>>>) to Leaf
// till we reach Leaf::ConTree - which is pure lome0::Tree<Con>
// then we call normalize with applicator from above

// we also do norm (to ConTree) during task() an
