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

// type App<Con> = AppTree<Box<Leaf<Con>>>;

// we must recognize that we are the Leaf implementors
pub enum Leaf<Con>{
    Abs(Box<(Leaf<Con>, Leaf<Con>)>),
    // App(Box<lome0::Tree<Leaf<Con>>>), // we impl apply for this
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
use crate::{ConApplicator, Leaf};

pub(super) enum Task<Con, A: ConApplicator<Con>> {
    ConTask(A::ConTask),
    DoneLeaf(Leaf<Con>)
}

pub(super) fn task<Con, A: ConApplicator<Con>>
(op:Leaf<Con>, x:Leaf<Con>, ator:&mut A) -> Task<Con, A> {
    match op {
        Leaf::Abs(_) => todo!(),
        Leaf::Con(op_) => Task::ConTask(ator.task(op_, x))
    }
}

pub(super) fn completed<Con, A: ConApplicator<Con>>
(task:Task<Con, A>, ator:&mut A) -> lome0::Tree<Leaf<Con>> {
    let lf = match task {
        Task::ConTask(ct)
        => Leaf::Con(ator.completed(ct)),
        Task::DoneLeaf(leaf) => leaf,
    };
    lome0::Tree::Lea(lf)
}

// pub struct Applicator<ConApp>(pub ConApp);

// impl <ConApp> Applicator<ConApp> {
//     // Leaf(Leaf) -> Tree
//     fn apply<Con>
//     (op:Leaf<Con>, x:Leaf<Con>) -> lome0::Tree<Leaf<Con>> {
//         todo!()
//     }
// }

// enum Task {

// }

// impl<Con, A: ConApplicator<Con>> lome0::LeafApplicator<Leaf<Con>>
// for Applicator<&mut A> {
//     type ApplicatorTask = A::ConTask;

//     fn task(&mut self, operator:Leaf<Con>, operand:Leaf<Con>)
//     -> Self::ApplicatorTask {
//         match Self::apply(operator, operand) {
//             lome0::Tree::Lea(_) => todo!(),
//             lome0::Tree::Brc(_) => todo!(),
//         }
//     }

//     fn completed(&mut self, task:Self::ApplicatorTask) -> lome0::Tree<Leaf<Con>>
//     {lome0::Tree::Lea(Leaf::Con(self.0.completed(task)))}
// }


}
