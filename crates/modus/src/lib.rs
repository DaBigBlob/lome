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
    clippy::single_match,
    clippy::explicit_auto_deref
)]

macro_rules! unreachable_fast {
    () => {{
        #[cfg(debug_assertions)]
        { unreachable!()}

        #[cfg(not(debug_assertions))]
        // SAFETY: each call site proves unreachable.
        unsafe {
            core::hint::unreachable_unchecked()
        }
    }};
}

extern crate alloc;
use core::fmt;
use alloc::boxed::Box;
use norm::FrameQ;

/// 1. ApplicatorTask failure semantics implementor-local; self-consistency
///    required. We do not/should not care.
/// 2. completed() returning
///    `Brc(Box::new((Lea(op), Lea(x))))` causes naive reapply.
/// 3. LeafApplicator assumed pure. Actual purity implementor-defined;
///    impurity permitted.
pub trait LeafApplicator<Leaf> {
    type ApplicatorTask;

    /// Begin/schedule application, perhaps elsewhere/thread.
    fn apply(&self, operator:Leaf, operand:Leaf) -> Self::ApplicatorTask;

    /// Wait/get application result.
    fn completed(&self, task:Self::ApplicatorTask) -> Tree<Leaf>;
}

/// Principal Expression
pub enum Tree<Leaf> {
    /// Leaf
    Lea(Leaf),
    /// Branch (Modus Ponens)
    Brc(Box<(Tree<Leaf>, Tree<Leaf>)>)
}
impl <Leaf> From<Leaf> for Tree<Leaf> {
    fn from(value: Leaf) -> Self {Self::Lea(value)}
}
impl <Leaf> From<(Tree<Leaf>, Tree<Leaf>)> for Tree<Leaf> {
    fn from(value: (Tree<Leaf>, Tree<Leaf>)) -> Self {
        Self::Brc(Box::new((value.0, value.1)))
    }
}
impl <Leaf> Tree<Leaf> {
    pub fn norm<A: LeafApplicator<Leaf>>(self, applicator:&A) -> Leaf {
        match self {
            Tree::Lea(lf) => lf,
            Tree::Brc(bb) => {
                let frm = FrameQ::new(*bb, applicator);
                frm.reduce(applicator)
            },
        }
    }
}
impl <Leaf: fmt::Debug> fmt::Debug for Tree<Leaf> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Tree::Lea(o) => write!(f, "{o:?}"),
            Tree::Brc(bb) => {
                let (op, x) = (&(*bb).0, &(*bb).1);
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

mod norm {
    // Invariant-Hold-ready:
    //   Hold is never (Some(Lea(_)), Some(Lea(_))).
    // Invariant-expansion-owner:
    //   FrameQ nonempty; Frame 0 alone has src=None.
    //   Frame i>0 has src=Some(Ref(parent,_)) with parent<i.
    //   Refs biject non-bottom Frames with parent None slots.
    //   Each child Frame owns its referenced expansion.
    // Invariant-reduce-entry:
    //   No Hold slot contains Brc.
    //   Top Frame is Task.

    mod frame {
        use crate::{Tree, LeafApplicator};

        /// Construct only through InFrame::new().
        pub(super) enum InFrame<Leaf, A: LeafApplicator<Leaf>>{
            Task(A::ApplicatorTask),
            Hold((Option<Tree<Leaf>>, Option<Tree<Leaf>>))
        }
        impl <Leaf, A: LeafApplicator<Leaf>> InFrame<Leaf, A> {
            pub(super) fn new(b: (Tree<Leaf>, Tree<Leaf>), ator:&A) -> Self {
                let mut innr = InFrame::Hold((Some(b.0), Some(b.1)));
                innr.try_task(ator);
                // #intro Invariant-Hold-ready
                innr
            }

            /// Convert ready Hold to Task.
            #[inline]
            fn try_task(&mut self, ator:&A) {
                match self {
                    InFrame::Hold((l, r))
                    => match (&*l, &*r) {
                        (
                            Some(Tree::Lea(_)),
                            Some(Tree::Lea(_))
                        ) => match (l.take(), r.take()) {
                            (
                                Some(Tree::Lea(op)),
                                Some(Tree::Lea(x))
                            ) => {
                                *self = Self::Task(ator.apply(op, x));
                            },
                            // Both proven Some(Lea(_)); no intervening mutation.
                            _ => unreachable_fast!()
                        },
                        _ => ()
                    },
                    // Task has no slots.
                    InFrame::Task(_) => (),
                }
            }

            /// Requires referenced parent Hold slot=None.
            /// Completes popped child's expansion.
            ///
            // #need Invariant-Hold-ready
            pub(super) fn fill_slot(&mut self, rf:Ref, obj:Leaf, ator:&A) {
                match self {
                    InFrame::Hold(lr) => {
                        match rf.slot(lr) {
                            slot @ None => *slot = Some(Tree::Lea(obj)),
                            // Required slot=None.
                            Some(_) => unreachable_fast!(),
                        }
                        // #elim Invariant-Hold-ready
                        self.try_task(ator);
                        // #intro Invariant-Hold-ready
                    },
                    // Referenced parent has a slot, hence is Hold.
                    InFrame::Task(_) => unreachable_fast!(),
                }
            }

            /// Detach local Brc slots into prospective child Frames.
            /// Detached slots become None. Caller pushes every returned child.
            pub(super) fn children(&mut self, ator:&A) -> (Option<Self>, Option<Self>) {

                fn take_slot<Leaf, A: LeafApplicator<Leaf>>
                (slot: &mut Option<Tree<Leaf>>, ator:&A) -> Option<InFrame<Leaf, A>> {
                    match &*slot {
                        Some(Tree::Brc(_)) => match slot.take() {
                            Some(Tree::Brc(b)) => Some(InFrame::new(*b, ator)),
                            // Some(Brc(_)) proven; no intervening mutation.
                            _ => unreachable_fast!(),
                        },
                        _ => None,
                    }
                }

                match self {
                    InFrame::Task(_) => (None, None),
                    InFrame::Hold((l, r)) => (
                        take_slot(l, ator),
                        take_slot(r, ator)
                    )
                }
            }
        }

        /// Parent Frame and expanded slot.
        pub(super) struct Ref(usize, bool);
        impl Ref {
            /// Requires valid parent index.
            #[inline]
            pub(super) fn right(idx: usize) -> Self {Self(idx, true)}

            /// Requires valid parent index.
            #[inline]
            pub(super) fn left(idx: usize) -> Self {Self(idx, false)}

            /// Select parent slot.
            #[inline]
            pub(super) fn slot<'a, Leaf>
            (&self, frm: &'a mut (Option<Tree<Leaf>>, Option<Tree<Leaf>>))
            -> &'a mut Option<Tree<Leaf>> {
                match self.1 {
                    true => &mut frm.1,
                    false => &mut frm.0,
                }
            }

            /// Requires self.0 < vec.len().
            #[inline]
            pub(super) fn frame<'a, Leaf, A: LeafApplicator<Leaf>>
            (&self, vec: &'a mut [Frame<Leaf, A>])
            -> &'a mut Frame<Leaf, A> { &mut vec[self.0]}
        }

        pub(super) struct Frame<Leaf, A: LeafApplicator<Leaf>> {
            /// None only for bottom Frame.
            pub(super) src: Option<Ref>,
            pub(super) innr: InFrame<Leaf, A>
        }
    }

    use alloc::vec::Vec;
    use crate::{LeafApplicator, Tree};
    use frame::{Frame, InFrame, Ref};

    pub(super) struct FrameQ<Leaf, A: LeafApplicator<Leaf>>
    (Vec<Frame<Leaf, A>>);

    impl <Leaf, A: LeafApplicator<Leaf>> FrameQ<Leaf, A> {
        pub(super) fn new(b: (Tree<Leaf>, Tree<Leaf>), ator:&A) -> Self {
            let q = alloc::vec![Frame{
                src:None,
                innr:InFrame::new(b, ator)
            }];
            // #intro Invariant-Hold-ready
            // #intro Invariant-expansion-owner
            Self(q)
        }

        /// Frames below initial top must contain no Brc slots.
        /// Expands all Brc slots reachable from initial top.
        ///
        // #need Invariant-Hold-ready
        // #need Invariant-expansion-owner
        fn expand(&mut self, ator:&A) {
            // #use Invariant-expansion-owner
            let mut idx = self.0.len() - 1;

            // Dynamic bound processes appended Frames.
            // #use Invariant-Hold-ready
            // #use Invariant-expansion-owner
            while idx < self.0.len() {
                let (lc, rc) = self.0[idx].innr.children(ator);
                // #elim Invariant-expansion-owner

                if let Some(innr) = lc {
                    self.0.push(Frame{src:Some(Ref::left(idx)), innr});
                }

                if let Some(innr) = rc {
                    self.0.push(Frame{src:Some(Ref::right(idx)), innr});
                }
                // #intro Invariant-expansion-owner

                idx += 1;
            }
            // #intro Invariant-reduce-entry
        }

        // #need Invariant-Hold-ready
        // #need Invariant-expansion-owner
        pub(super) fn reduce(mut self, ator:&A) -> Leaf {
            // Initial Frame has no lower Frames.
            // #use Invariant-expansion-owner
            self.expand(ator);

            // #use Invariant-expansion-owner
            // #use Invariant-reduce-entry
            while let Some(Frame {src, innr}) = self.0.pop() {
                // #elim Invariant-expansion-owner
                // #elim Invariant-reduce-entry

                match innr {
                    InFrame::Task(tsk) => match ator.completed(tsk) {
                        Tree::Lea(o) => match src {
                            Some(rf)
                            // Pre-pop Ref targets surviving parent None slot.
                            => rf.frame(&mut self.0).innr.fill_slot(rf, o, ator),
                            // #intro Invariant-expansion-owner
                            // #intro Invariant-reduce-entry

                            // Popped Frame was sole bottom Frame.
                            None => return o,
                        },

                        Tree::Brc(b) => {
                            // Replace popped expansion with same src.
                            self.0.push(Frame {src, innr:InFrame::new(*b, ator)});
                            // #intro Invariant-expansion-owner

                            // Lower Frames remain Brc-free.
                            // #use Invariant-expansion-owner
                            self.expand(ator);
                        },
                    },

                    // Popped top proven Task.
                    _ => unreachable_fast!(),
                }
            }

            // FrameQ cannot be empty at loop entry.
            // #use Invariant-expansion-owner
            unreachable_fast!()
        }
    }
}
