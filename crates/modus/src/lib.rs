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
    clippy::vec_init_then_push
)]

extern crate alloc;
use alloc::boxed::Box;

use crate::exec::Executor;

pub trait Object: Sized {
    /// apply may fail, but what is means to fail is semantics local to the
    /// implementor - just like what false or absurdity is at the foundations
    /// of mathematics. The implementor must agree with himself on that meaning.
    /// We, on our side, simply do not - and should not - care.
    fn apply(self, x: Self) -> Tree<Self>;
}

/// Expression
pub enum Tree<O: Object> {
    /// Opaque Object
    Obj(O),
    // We use box here for indirection instead of in Branch because
    // if Object is small, we would be wasting less space with relatively
    // small box (approx 1 pointer size) instead of holding at least two
    // pointer sizes.
    /// Modus Ponens
    Brc(Box<Branch<O>>)
}
impl <O: Object> From<O> for Tree<O> {
    fn from(value: O) -> Self {Self::Obj(value)}
}
impl <O: Object> From<Branch<O>> for Tree<O> {
    fn from(value: Branch<O>) -> Self {Self::Brc(Box::new(value))}
}

/// Principal Expression i.e. Modus Ponenes
pub struct Branch<O: Object> { l: Tree<O>, r: Tree<O> }
impl <O: Object> From<(Tree<O>, Tree<O>)> for Branch<O> {
    fn from(value: (Tree<O>, Tree<O>)) -> Self {Self{l:value.0, r:value.1}}
}
impl <O: Object> Branch<O> {
    pub fn norm<'a, E: Executor>(self, exec:&'a E) -> O {
        let mut frm = norm::FrameQ::new(self, exec);
        frm.expand(exec);
        frm.reduce(exec)
    }
}

pub mod exec {
    pub trait Executor {
        type Task<'a, T: 'a>: 'a
            where Self: 'a;
        /// Essentially Spawn.
        fn task<'a, T:  'a, F: FnOnce() -> T +  'a>
        (&'a self, computation: F) -> Self::Task<'a, T>;

        /// Essentially Join.
        fn complete<'a, T:  'a>
        (&'a self, task: Self::Task<'a, T>) -> T;
    }
}

mod norm {
    use alloc::vec::Vec;
    use crate::{Branch, Object, Tree, exec::Executor};

    enum InFrame<'a, O: Object + 'a, E: Executor + 'a>{
        Task(E::Task<'a, Tree<O>>),
        Hold{l:Option<Tree<O>>, r:Option<Tree<O>>}
    }
    impl <'a, O: Object, E: Executor> InFrame<'a, O, E> {
        fn try_task(&mut self, exec:&'a E) {
            match self {
                InFrame::Hold { l, r }
                => match (&*l, &*r) {
                    (
                        Some(Tree::Obj(_)),
                        Some(Tree::Obj(_))
                    ) => match (l.take(), r.take()) {
                        (
                            Some(Tree::Obj(op)),
                            Some(Tree::Obj(x))
                        ) => {
                            *self = Self::Task(exec.task(
                                move || op.apply(x)
                            ));
                        },
                        _ => unreachable!()
                    },
                    _ => ()
                },
                // never produced children
                InFrame::Task(_) => (),
            }
        }

        fn fill_slot(&mut self, right:bool, obj:O) {
            match self {
                InFrame::Hold { l, r } => {
                    if right {*r = Some(Tree::Obj(obj))}
                    else     {*l = Some(Tree::Obj(obj))}
                },
                // never produced children
                InFrame::Task(_) => unreachable!(),
            }
        }

        /// caller must assert `self_idx` is index of this frame.
        fn children(&mut self) -> (Option<Self>, Option<Self>) {

            fn take_slot<'a, O: Object, E: Executor>
            (slot: &mut Option<Tree<O>>) -> Option<InFrame<'a, O, E>> {
                match &*slot {
                    Some(Tree::Brc(_)) => match slot.take() {
                        Some(Tree::Brc(b)) => Some(InFrame::Hold{
                            l:Some(b.l),
                            r:Some(b.r)
                        }),
                        _ => unreachable!(),
                    },
                    _ => None,
                }
            }

            match self {
                InFrame::Task(_) => (None, None),
                InFrame::Hold { l, r } => (
                    take_slot(l),
                    take_slot(r)
                )
            }
        }
    }

    struct Frame<'a, O: Object, E: Executor> {
        src: Option<(usize, bool)>, // (parent_index, slot_is_right)
        innr: InFrame<'a, O, E>
    }

    // properties:
    //  - FrameQ-propr-min-1
    //  - FrameQ-propr-post-expand-OO-pop
    // idiom for push: try_task -> push
    pub struct FrameQ<'a, O: Object, E: Executor>(Vec<Frame<'a, O, E>>);
    impl <'a, O: Object, E: Executor> FrameQ<'a, O, E> {
        pub fn new(b: Branch<O>, exec:&'a E) -> Self {
            let mut q = Vec::new();
            let mut innr = InFrame::Hold{l:Some(b.l), r:Some(b.r)};
            innr.try_task(exec);
            q.push(Frame {src:None, innr});
            // intro FrameQ-propr-min-1
            Self(q)
        }

        pub fn expand(&mut self, exec:&'a E) {
            let mut idx = self.0.len() - 1; // by FrameQ-propr-min-1
            while idx < self.0.len() {
                let (lc, rc) = self.0[idx].innr.children();
                if let Some(mut innr) = lc {
                    innr.try_task(exec);
                    self.0.push(Frame{src:Some((idx, false)), innr});
                }
                if let Some(mut innr) = rc {
                    innr.try_task(exec);
                    self.0.push(Frame{src:Some((idx, true)), innr});
                }
                idx += 1;
            }
            // intro FrameQ-propr-post-expand-OO-pop
        }

        pub fn reduce(&mut self, exec:&'a E) -> O {
            while let Some(Frame {
                src,
                innr:InFrame::Task(tsk)
            }) = self.0.pop() { // by FrameQ-propr-post-expand-OO-pop
                match exec.complete(tsk) {
                    Tree::Obj(o) => match src {
                        Some((idx, right)) => self.0[idx].innr.fill_slot(right, o),
                        None => return o, // elim FrameQ-propr-min-1
                    },
                    Tree::Brc(b) => {
                        let mut innr = InFrame::Hold {l:Some(b.l), r:Some(b.r)};
                        innr.try_task(exec);
                        self.0.push(Frame {src, innr});
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
