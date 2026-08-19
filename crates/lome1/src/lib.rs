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
    Con(Con)
}



// struct LeafApplicator<Con, CA: ConApplicator<Con>>(CA);
// impl <Con, CA: ConApplicator<Con>> LeafApplicator<Con, CA> {
//     new
// }
// impl <Con, CA: ConApplicator<Con>> lome0::LeafApplicator<Leaf<Con>> for LeafApplicator {
//     type ApplicatorTask = CA::ConAppTask;

//     fn task(&mut self, operator:Leaf<Con>, operand:Leaf<Con>) -> Self::ApplicatorTask {
//         todo!()
//     }

//     fn completed(&mut self, task:Self::ApplicatorTask) -> lome0::Tree<Leaf<Con>> {
//         todo!()
//     }
// }
