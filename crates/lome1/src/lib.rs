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
use core::hash::Hash;
use lome0;

pub trait Constructor: Sized + Default + Eq + Hash + Clone {}
impl <T: Sized + Default + Eq + Hash + Clone> Constructor for T {}

// default is an error constructor
pub trait ConApplicator<Con: Constructor> {
    type ConTask;
    fn task(&mut self, operator:Con, operand:Leaf<Con>) -> Self::ConTask;
    fn completed(&mut self, task:Self::ConTask) -> Con;
}

// we must recognize that we are the Leaf implementors
#[derive(Clone)]
pub enum Leaf<Con: Constructor>{
    Abs(Box<(Leaf<Con>, Leaf<Con>)>),
    App(Box<lome0::Tree<Leaf<Con>>>),
    Con(Con)
}
impl <Con: Constructor> Default for Leaf<Con> {
    /// This is the error constructor.
    fn default() -> Self {Self::Con(Con::default())}
}
impl <Con: Constructor> Leaf<Con> {
    pub fn norm<A: ConApplicator<Con>>
    (self, applicator:&mut A) -> Leaf<Con> {
        match self {
            Leaf::App(bt)=> (*bt).norm(&mut application::Applicator(
                applicator,
                application::context::Context::new()
            )),
            _ => self
        }
    }
}



mod application {
pub mod context {

use crate::{Constructor, Leaf};
use hashbrown::{HashMap, hash_map::Entry};

pub struct Context<Con: Constructor>(HashMap<Con, Leaf<Con>>);
impl <Con: Constructor> Context<Con> {
    #[inline]
    pub fn new() -> Self {Self(HashMap::new())}

    #[inline]
    pub fn get(&self, key:&Con) -> Option<Leaf<Con>>
    {self.0.get(key).cloned()}

    #[inline]
    pub fn set(&mut self, key:Con, val:Leaf<Con>) -> bool {
        match self.0.entry(key) {
            Entry::Occupied(_) => false,
            Entry::Vacant(entry) => {
                entry.insert(val);
                true
            },
        }
    }
}

}

use alloc::boxed::Box;
use crate::{ConApplicator, Constructor, Leaf};
use context::Context;

pub enum Task<Con: Constructor, ConApp: ConApplicator<Con>> {
    ConTask(ConApp::ConTask),
    Tree(lome0::Tree<Leaf<Con>>)
}

pub struct Applicator<'a, Con: Constructor, ConApp: ConApplicator<Con>>
(pub &'a mut ConApp, pub Context<Con>);
impl <
    'a,
    Con: Constructor,
    ConApp: ConApplicator<Con>
> Applicator<'a, Con, ConApp> {
    pub fn apply
    (abs:Box<(Leaf<Con>, Leaf<Con>)>, x:Leaf<Con>) -> Leaf<Con> {
        todo!()
    }
}
impl <
    'a,
    Con: Constructor,
    ConApp: ConApplicator<Con>
> lome0::LeafApplicator<Leaf<Con>> for Applicator<'a, Con, ConApp> {
    type ApplicatorTask = Task<Con, ConApp>;

    fn task(&mut self, operator:Leaf<Con>, operand:Leaf<Con>) -> Self::ApplicatorTask {
        match operator {
            Leaf::App(_) => Task::Tree(lome0::Tree::Brc(Box::new((
                lome0::Tree::Lea(operator),
                lome0::Tree::Lea(operand)
            ))).into()),
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
