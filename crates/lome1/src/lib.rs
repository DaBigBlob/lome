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
    App(Box<lome0::Tree<Leaf<Con>>>),
    Con(Con)
}

pub struct Tree<Con>(lome0::Tree<Leaf<Con>>);
impl <Con> From<lome0::Tree<Leaf<Con>>> for Tree<Con> {
    fn from(value: lome0::Tree<Leaf<Con>>) -> Self {Self(value)}
}
impl <Con> Into<lome0::Tree<Leaf<Con>>> for Tree<Con> {
    fn into(self) -> lome0::Tree<Leaf<Con>> {self.0}
}
impl <Con> Tree<Con> {}

mod application {
use alloc::boxed::Box;

use crate::{ConApplicator, Leaf};

pub(super) enum Task<Con, A: ConApplicator<Con>> {
    ConTask(A::ConTask),
    Tree(lome0::Tree<Leaf<Con>>)
}

pub(super) fn task<Con, A: ConApplicator<Con>>
(op:Leaf<Con>, x:Leaf<Con>, ator:&mut A) -> Task<Con, A> {
    match op {
        Leaf::App(_) => Task::Tree(lome0::Tree::Brc(Box::new(
            (lome0::Tree::Lea(op), lome0::Tree::Lea(x))
        ))),
        Leaf::Abs(op_) => todo!(),
        Leaf::Con(op_) => Task::ConTask(ator.task(op_, x))
    }
}

pub(super) fn completed<Con, A: ConApplicator<Con>>
(task:Task<Con, A>, ator:&mut A) -> lome0::Tree<Leaf<Con>> {
    match task {
        Task::ConTask(ct)
        => lome0::Tree::Lea(Leaf::Con(ator.completed(ct))),
        Task::Tree(tree) => tree,
    }
}

}
