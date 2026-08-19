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

// impl<Leaf, F> lome0::LeafApplicator<Leaf> for F
// where
//     F: FnMut(Leaf, Leaf) -> lome0::Tree<Leaf>,
// {
//     type ApplicatorTask = lome0::Tree<Leaf>;

//     fn task(&mut self, operator: Leaf, operand: Leaf) -> Self::ApplicatorTask {
//         self(operator, operand)
//     }

//     fn completed(&mut self, task: Self::ApplicatorTask) -> lome0::Tree<Leaf> {
//         task
//     }
// }

// constructors do:
// constructors(constructors) -> constructors
pub trait ConApplicator<Con> {
    type ConAppTask;
    fn task(&mut self, operator:Con, operand:Con) -> Self::ConAppTask;
    fn completed(&mut self, task:Self::ConAppTask) -> Con;
}

// type App<Con> = AppTree<Box<Leaf<Con>>>;

// we must recognize that we are the Leaf implementors
#[derive(PartialEq, Eq)]
pub enum Leaf<Con>{
    Abs(Box<(Leaf<Con>, Leaf<Con>)>),
    App(lome0::Tree<Box<Leaf<Con>>>), // we impl apply for this
    Con(Con)
}
fn leaf_applicator<Con>(op:Leaf<Con>, x:Leaf<Con>) -> lome0::Tree<Leaf<Con>> {
    todo!()
}

pub fn lol<Con>(x: lome0::Tree<Leaf<Con>>) -> Leaf<Con> {
    // x.norm(&mut (leaf_applicator, |k| k))
    x.norm(&mut (|k, j| (k, j), |(m, n)| leaf_applicator(m, n)))
}

pub struct AsLeafApplicator<CA>(pub CA);
impl<
    Con,
    CA: ConApplicator<Con>> lome0::LeafApplicator<Leaf<Con>
> for AsLeafApplicator<CA> {
    type ApplicatorTask = CA::ConAppTask;

    fn task(
        &mut self,
        operator: Leaf<Con>,
        operand: Leaf<Con>,
    ) -> Self::ApplicatorTask {
        // convert Leaf<Con> -> Con as appropriate
        // self.0.task(operator.into(), operand.into())
        todo!()
    }

    fn completed(
        &mut self,
        task: Self::ApplicatorTask,
    ) -> lome0::Tree<Leaf<Con>> {
        // Leaf::from(self.0.completed(task)).into()
        todo!()
    }
}
// impl <Con, CA: ConApplicator<Con>> lome0::LeafApplicator<Leaf<Con>> for CA {}

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
