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
    fn task(&mut self, operator:Con, operand:Leaf<Con>) -> Self::ConTask;
    fn completed(&mut self, task:Self::ConTask) -> Con;
}

// we must recognize that we are the Leaf implementors
pub enum Leaf<Con>{
    Abs(Box<(Leaf<Con>, Leaf<Con>)>),
    App(Box<Tree<Con>>),
    Con(Con)
}
pub struct Tree<Con>(lome0::Tree<Leaf<Con>>);
impl <Con> Tree<Con> {
    pub fn norm<A: ConApplicator<Con>>(self, applicator:&mut A) -> Con {
        // match self.0.norm(&mut appli::Applicator(applicator)) {
        //     Leaf::Con(c) => c,
        //     _ => unreachable!(
        //         "Our LeafApplicator.completed() guarantees this is unreachable."
        //     )
        // }
        todo!()
    }
}

mod application {
use crate::{ConApplicator, Leaf, Tree};

pub(super) enum Task<Con, A: ConApplicator<Con>> {
    ConTask(A::ConTask),
    Tree(Tree<Con>)
}

pub(super) fn task<Con, A: ConApplicator<Con>>
(op:Leaf<Con>, x:Leaf<Con>, ator:&mut A) -> Task<Con, A> {
    match op {
        Leaf::App(tree) => todo!(),
        Leaf::Abs(op_) => todo!(),
        Leaf::Con(op_) => Task::ConTask(ator.task(op_, x))
    }
}

pub(super) fn completed<Con, A: ConApplicator<Con>>
(task:Task<Con, A>, ator:&mut A) -> Tree<Con> {
    match task {
        Task::ConTask(ct) => todo!(),
        Task::Tree(tree) => todo!(),
    }
}

}
