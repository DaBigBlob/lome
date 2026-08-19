#![no_std]
#![deny(
    clippy::panic,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::todo,
    clippy::unimplemented,
    clippy::arithmetic_side_effects,
)]
#![allow(
    clippy::unreachable,
    clippy::single_match,
    clippy::explicit_auto_deref
)]

extern crate alloc;
use alloc::boxed::Box;
use lome0;

pub trait ConApplicator<Con> {
    type ConTask;
    fn task(&mut self, operator:Con, operand:Con) -> Self::ConTask;
    fn completed(&mut self, task:Self::ConTask) -> Con;
}

// type App<Con> = AppTree<Box<Leaf<Con>>>;

// we must recognize that we are the Leaf implementors
pub enum Leaf<Con>{
    Abs(Box<(Leaf<Con>, Leaf<Con>)>),
    App(Box<lome0::Tree<Leaf<Con>>>), // we impl apply for this
    Con(Con)
}
pub struct Tree<Con>(lome0::Tree<Leaf<Con>>);
impl <Con> Tree<Con> {
    pub fn norm<A: ConApplicator<Con>>(self, applicator:&mut A) -> Con {
        match self.0.norm(&mut normm::LeafApplicator(applicator)) {
            Leaf::Con(c) => c,
            _ => unreachable!()
        }
    }
}

mod normm {
use crate::{ConApplicator, Leaf};

pub(super) struct LeafApplicator<From>(pub From);

impl<Con, A: ConApplicator<Con>> lome0::LeafApplicator<Leaf<Con>>
for LeafApplicator<&mut A> {
    type ApplicatorTask = A::ConTask;

    fn task(&mut self, _operator:Leaf<Con>, _operand:Leaf<Con>)
    -> Self::ApplicatorTask {
        // self.0.task(operator.into(), operand.into())
        todo!()
    }

    fn completed(&mut self, task:Self::ApplicatorTask) -> lome0::Tree<Leaf<Con>>
    {lome0::Tree::Lea(Leaf::Con(self.0.completed(task)))}
}


}
