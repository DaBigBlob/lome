#![no_std]
#![deny(
    clippy::panic,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::todo,
    clippy::unimplemented
)]
#![allow(
    clippy::unreachable,
    clippy::arithmetic_side_effects,
    clippy::single_match
)]

extern crate alloc;
use core::fmt;
use alloc::boxed::Box;
use executor::Executor;
use norm::FrameQ;

/// Expression
pub enum Tree<Leaf> {
    /// Leaf
    Lea(Leaf),
    /// Branch
    Brc(Box<Branch<Leaf>>)
}
impl <Leaf> From<Leaf> for Tree<Leaf> {
    fn from(value: Leaf) -> Self {Self::Lea(value)}
}
impl <Leaf> From<(Tree<Leaf>, Tree<Leaf>)> for Tree<Leaf> {
    fn from(value: (Tree<Leaf>, Tree<Leaf>)) -> Self {
        Self::Brc(Box::new(Branch{l:value.0, r:value.1}))
    }
}
impl <Leaf: fmt::Debug> fmt::Debug for Tree<Leaf> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Tree::Lea(o) => write!(f, "{o:?}"),
            Tree::Brc(bb) => {
                let (op, x) = (&(*bb).l, &(*bb).r);
                write!(f, "({op:?}) ({x:?})")
            }
        }
    }
}
impl <Leaf: Clone> Clone for Tree<Leaf> {
    fn clone(&self) -> Self {
        match self {
            Self::Lea(o) => Self::Lea(o.clone()),
            Self::Brc(bb) => Self::Brc(bb.clone()),
        }
    }
}

/// Principal Expression i.e. Modus Ponenes
pub struct Branch<Leaf> { l: Tree<Leaf>, r: Tree<Leaf> }
impl <Leaf> Branch<Leaf> {
    pub fn norm<E: Executor<Leaf>>(self, exec:&E) -> Leaf {
        let mut frm = FrameQ::new(self, exec);
        frm.reduce(exec)
    }
}
impl <Leaf: Clone> Clone for Branch<Leaf> {
    fn clone(&self) -> Self {Self{l:self.l.clone(), r:self.r.clone()}}
}

pub mod executor {
    use crate::Tree;
    pub trait Executor<Leaf> {
        type Task;

        /// Submit a computation (to perhaps another thread).
        fn apply(&self, operator:Leaf, operand:Leaf) -> Self::Task;

        /// Wait for and obtain its result.
        fn completed(&self, task: Self::Task) -> Tree<Leaf>;
    }
}

mod norm {
    mod frame {
        use crate::{Branch, Tree, executor::Executor};

        /// DO NOT CONTSRUCT RAW: use InFrame::new()
        pub(super) enum InFrame<Leaf, E: Executor<Leaf>>{
            Task(E::Task),
            Hold{l:Option<Tree<Leaf>>, r:Option<Tree<Leaf>>}
        }
        impl <Leaf, E: Executor<Leaf>> InFrame<Leaf, E> {
            pub(super) fn new(b: Branch<Leaf>, exec:&E) -> Self {
                let mut innr = InFrame::Hold{l:Some(b.l), r:Some(b.r)};
                innr.try_task(exec);
                innr
            }
        }
        impl <Leaf, E: Executor<Leaf>> InFrame<Leaf, E> {
            /// not to be used outside of InFrame
            fn try_task(&mut self, exec:&E) {
                match self {
                    InFrame::Hold { l, r }
                    => match (&*l, &*r) {
                        (
                            Some(Tree::Lea(_)),
                            Some(Tree::Lea(_))
                        ) => match (l.take(), r.take()) {
                            (
                                Some(Tree::Lea(op)),
                                Some(Tree::Lea(x))
                            ) => {
                                *self = Self::Task(exec.apply(op, x));
                            },
                            _ => unreachable!()
                        },
                        _ => ()
                    },
                    // never produced children
                    InFrame::Task(_) => (),
                }
            }

            /// Requires the selected slot to be `None` - i.e. only be called
            /// from a child not lying about its parent.
            pub(super) fn fill_slot(&mut self, right:bool, obj:Leaf, exec:&E) {
                match self {
                    InFrame::Hold { l, r } => {
                        if right {*r = Some(Tree::Lea(obj))}
                        else     {*l = Some(Tree::Lea(obj))}
                        // elim FrameQ-propr-post-expand-done-in
                        self.try_task(exec);
                        // intro FrameQ-propr-post-expand-done-in
                    },
                    // never produced children
                    InFrame::Task(_) => unreachable!(),
                }
            }

            pub(super) fn children(&mut self, exec:&E) -> (Option<Self>, Option<Self>) {

                fn take_slot<Leaf, E: Executor<Leaf>>
                (slot: &mut Option<Tree<Leaf>>, exec:&E) -> Option<InFrame<Leaf, E>> {
                    match &*slot {
                        Some(Tree::Brc(_)) => match slot.take() {
                            Some(Tree::Brc(b)) => {
                                let mut inf = InFrame::Hold{
                                    l:Some(b.l),
                                    r:Some(b.r)
                                };
                                inf.try_task(exec);
                                // ensure FrameQ-propr-post-expand-done-in
                                Some(inf)
                            },
                            _ => unreachable!(),
                        },
                        _ => None,
                    }
                }

                match self {
                    InFrame::Task(_) => (None, None),
                    InFrame::Hold { l, r } => (
                        take_slot(l, exec),
                        take_slot(r, exec)
                    )
                }
            }
        }

        pub(super) struct Frame<Leaf, E: Executor<Leaf>> {
            pub(super) src: Option<(usize, bool)>, // (parent_index, slot_is_right)
            pub(super) innr: InFrame<Leaf, E>
        }
    }

    use alloc::vec::Vec;
    use crate::{Branch, Tree, executor::Executor};
    use frame::{Frame, InFrame};

    // properties:
    //  - FrameQ-propr-min-1
    //  - FrameQ-propr-post-expand-OO-pop
    //  - FrameQ-propr-post-expand-done-in
    pub(super) struct FrameQ<Leaf, E: Executor<Leaf>>
    (Vec<Frame<Leaf, E>>);

    impl <Leaf, E: Executor<Leaf>> FrameQ<Leaf, E> {
        pub(super) fn new(b: Branch<Leaf>, exec:&E) -> Self {
            let q = alloc::vec![Frame{
                src:None,
                innr:InFrame::new(b, exec)
            }];
            // intro FrameQ-propr-min-1
            Self(q)
        }

        fn expand(&mut self, exec:&E) {
            let mut idx = self.0.len() - 1; // by FrameQ-propr-min-1
            while idx < self.0.len() {
                let (lc, rc) = self.0[idx].innr.children(exec);
                if let Some(innr) = lc {
                    self.0.push(Frame{src:Some((idx, false)), innr});
                }
                if let Some(innr) = rc {
                    self.0.push(Frame{src:Some((idx, true)), innr});
                }
                idx += 1;
            }
            // intro FrameQ-propr-post-expand-OO-pop
        }

        pub(super) fn reduce(&mut self, exec:&E) -> Leaf {
            self.expand(exec);

            while let Some(Frame {
                src,
                innr:InFrame::Task(tsk)
            }) = self.0.pop() { // by FrameQ-propr-post-expand-OO-pop
                match exec.completed(tsk) {
                    Tree::Lea(o) => match src {
                        Some((idx, right))
                            => self.0[idx].innr.fill_slot(right, o, exec),
                        None => return o, // elim FrameQ-propr-min-1
                    },
                    Tree::Brc(b) => {
                        self.0.push(Frame {src, innr:InFrame::new(*b, exec)});
                        // emlim FrameQ-propr-post-expand-OO-pop
                        self.expand(exec);
                        // intro FrameQ-propr-post-expand-OO-pop
                    },
                }
            }
            unreachable!() // by FrameQ-propr-post-expand-OO-pop
        }
    }
}
