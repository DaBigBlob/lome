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
impl <Con> From<lome0::Tree<Leaf<Con>>> for Tree<Con> {
    fn from(value: lome0::Tree<Leaf<Con>>) -> Self {Self(value)}
}
impl <Con> Into<lome0::Tree<Leaf<Con>>> for Tree<Con> {
    fn into(self) -> lome0::Tree<Leaf<Con>> {self.0}
}
impl <Con> Tree<Con> {
    pub fn norm<A: ConApplicator<Con>>
    (self, applicator:&mut A) -> Leaf<Con> {
        self.0.norm(&mut application::Applicator(applicator))
    }
}

mod application {

use alloc::boxed::Box;
use crate::{ConApplicator, Leaf, Tree};

pub(super) enum Task<Con, ConApp: ConApplicator<Con>> {
    ConTask(ConApp::ConTask),
    Tree(Tree<Con>)
}

pub(super) struct Applicator<ConApp>(pub ConApp);
impl <Con, ConApp: ConApplicator<Con>> lome0::LeafApplicator<Leaf<Con>>
for Applicator<&mut ConApp> {
    type ApplicatorTask = Task<Con, ConApp>;

    fn task(&mut self, operator:Leaf<Con>, operand:Leaf<Con>) -> Self::ApplicatorTask {
        match operator {
            Leaf::App(_) => Task::Tree(lome0::Tree::Brc(Box::new(
                (lome0::Tree::Lea(operator), lome0::Tree::Lea(operand))
            )).into()),
            Leaf::Abs(op_) => todo!(),
            Leaf::Con(op_) => Task::ConTask(self.0.task(op_, operand))
        }
    }

    fn completed(&mut self, task:Self::ApplicatorTask) -> lome0::Tree<Leaf<Con>> {
        match task {
            Task::ConTask(ct)
            => lome0::Tree::Lea(Leaf::Con(self.0.completed(ct))).into(),
            Task::Tree(tree) => tree.into(),
        }
    }
}

}
