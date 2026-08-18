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

pub trait Object: Sized + Send + 'static {
    /// 1. apply() may fail, but what is means to fail is semantics local to the
    ///    implementor - just like what false or absurdity is at the foundations
    ///    of mathematics. The implementor must agree with himself on that meaning.
    ///    We, on our side, simply do not - and should not - care.
    ///
    /// 2. If `Tree::Brc(Box::new(Branch {l:Tree::Obj(op), r:Tree::Obj(x)}))`
    ///    is returned, we naively re-apply.
    ///
    /// 3. apply is assumed to be pure. Whether its actually pure is up to
    ///    implementation - in-fact many times impurity is desired - but that
    ///    is again up to the implementor.
    fn apply(self, x: Self) -> Tree<Self>;
}

/// Expression
pub enum Tree<O: Object> {
    /// Leaf
    Obj(O),
    /// Branch
    Brc(Box<Branch<O>>)
}
impl <O: Object> From<O> for Tree<O> {
    fn from(value: O) -> Self {Self::Obj(value)}
}
impl <O: Object> From<(Tree<O>, Tree<O>)> for Tree<O> {
    fn from(value: (Tree<O>, Tree<O>)) -> Self {
        Self::Brc(Box::new(Branch{l:value.0, r:value.1}))
    }
}
impl <O: Object + fmt::Debug> fmt::Debug for Tree<O> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Tree::Obj(o) => write!(f, "{o:?}"),
            Tree::Brc(bb) => {
                let (op, x) = (&(*bb).l, &(*bb).r);
                write!(f, "({op:?}) ({x:?})")
            }
        }
    }
}
impl <O: Object + Clone> Clone for Tree<O> {
    fn clone(&self) -> Self {
        match self {
            Self::Obj(o) => Self::Obj(o.clone()),
            Self::Brc(bb) => Self::Brc(bb.clone()),
        }
    }
}

/// Principal Expression i.e. Modus Ponenes
pub struct Branch<O: Object> { l: Tree<O>, r: Tree<O> }
impl <O: Object> Branch<O> {
    pub fn norm<E: Executor>(self, exec:&E) -> O {
        let mut frm = FrameQ::new(self, exec);
        frm.reduce(exec)
    }
}
impl <O: Object + Clone> Clone for Branch<O> {
    fn clone(&self) -> Self {Self{l:self.l.clone(), r:self.r.clone()}}
}

pub mod executor {
    pub trait Executor {
        // Task (handle) is kept on the main dependency resolution thread
        // so no need for Send.
        type Task<T: Send + 'static>;

        /// Submit a computation (to perhaps another thread).
        fn task<T: Send + 'static, F: FnOnce() -> T + Send + 'static>
        (&self, computation: F) -> Self::Task<T>;

        /// Wait for and obtain its result.
        fn complete<T: Send + 'static>
        (&self, task: Self::Task<T>) -> T;
    }
}

mod norm {
    mod frame {
        use crate::{Branch, Object, Tree, executor::Executor};

        /// DO NOT CONTSRUCT RAW: use InFrame::new()
        pub(super) enum InFrame<O: Object, E: Executor>{
            Task(E::Task<Tree<O>>),
            Hold{l:Option<Tree<O>>, r:Option<Tree<O>>}
        }
        impl <O: Object, E: Executor> InFrame<O, E> {
            pub(super) fn new(b: Branch<O>, exec:&E) -> Self {
                let mut innr = InFrame::Hold{l:Some(b.l), r:Some(b.r)};
                innr.try_task(exec);
                innr
            }
        }
        impl <O: Object, E: Executor> InFrame<O, E> {
            /// not to be used outside of InFrame
            fn try_task(&mut self, exec:&E) {
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

            /// Requires the selected slot to be `None` - i.e. only be called
            /// from a child not lying about its parent.
            pub(super) fn fill_slot(&mut self, right:bool, obj:O, exec:&E) {
                match self {
                    InFrame::Hold { l, r } => {
                        if right {*r = Some(Tree::Obj(obj))}
                        else     {*l = Some(Tree::Obj(obj))}
                        // elim FrameQ-propr-post-expand-done-in
                        self.try_task(exec);
                        // intro FrameQ-propr-post-expand-done-in
                    },
                    // never produced children
                    InFrame::Task(_) => unreachable!(),
                }
            }

            pub(super) fn children(&mut self, exec:&E) -> (Option<Self>, Option<Self>) {

                fn take_slot<O: Object, E: Executor>
                (slot: &mut Option<Tree<O>>, exec:&E) -> Option<InFrame<O, E>> {
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

        pub(super) struct Frame<O: Object, E: Executor> {
            pub(super) src: Option<(usize, bool)>, // (parent_index, slot_is_right)
            pub(super) innr: InFrame<O, E>
        }
    }

    use alloc::vec::Vec;
    use crate::{Branch, Object, Tree, executor::Executor};
    use frame::{Frame, InFrame};

    // properties:
    //  - FrameQ-propr-min-1
    //  - FrameQ-propr-post-expand-OO-pop
    //  - FrameQ-propr-post-expand-done-in
    // idiom for push: try_task -> push
    pub(super) struct FrameQ<O: Object, E: Executor>
    (Vec<Frame<O, E>>);

    impl <O: Object, E: Executor> FrameQ<O, E> {
        pub(super) fn new(b: Branch<O>, exec:&E) -> Self {
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

        pub(super) fn reduce(&mut self, exec:&E) -> O {
            self.expand(exec);

            while let Some(Frame {
                src,
                innr:InFrame::Task(tsk)
            }) = self.0.pop() { // by FrameQ-propr-post-expand-OO-pop
                match exec.complete(tsk) {
                    Tree::Obj(o) => match src {
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
