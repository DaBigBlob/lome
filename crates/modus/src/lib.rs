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
        unsafe {
            // SAFETY: caller asserts unreachable.
            core::hint::unreachable_unchecked()
        }
    }};
}

extern crate alloc;
use core::fmt;
use alloc::boxed::Box;
use norm::FrameQ;

/// 1. ApplicatorTask "failure" semantics implementor-local; implementor must
///    self-agree. We do not/should not care.
/// 2. completed() returning
///    `Brc(Box::new((Lea(op), Lea(x))))` causes naive reapply.
/// 3. LeafApplicator assumed pure. Actual purity implementor-defined; impurity
///    permitted/possibly desired.
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
    mod frame {
        use crate::{Tree, LeafApplicator};

        /// DO NOT CONSTRUCT RAW: use InFrame::new()
        pub(super) enum InFrame<Leaf, A: LeafApplicator<Leaf>>{
            Task(A::ApplicatorTask),
            Hold((Option<Tree<Leaf>>, Option<Tree<Leaf>>))
        }
        impl <Leaf, A: LeafApplicator<Leaf>> InFrame<Leaf, A> {
            /// #intro Invariant-(Lea,Lea)->Task
            /// Hold((Some(Lea(_)),Some(Lea(_)))) -> Task(_).
            pub(super) fn new(b: (Tree<Leaf>, Tree<Leaf>), ator:&A) -> Self {
                let mut innr = InFrame::Hold((Some(b.0), Some(b.1)));
                innr.try_task(ator);
                innr
            }

            /// Internal.
            /// #intro Invariant-(Lea,Lea)->Task
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
                            // Both just proven Some(Lea(_)); no mutation.
                            _ => unreachable_fast!()
                        },
                        _ => ()
                    },
                    // Task(_) has no children.
                    InFrame::Task(_) => (),
                }
            }

            /// Requires selected slot=None; truthful Ref.
            ///
            /// #using Invariant-child-slot-None
            /// #elim Invariant-child-slot-None for this child/slot expansion.
            pub(super) fn fill_slot(&mut self, rf:Ref, obj:Leaf, ator:&A) {
                match self {
                    InFrame::Hold(lr) => {
                        match rf.slot(lr) {
                            slot @ None => *slot = Some(Tree::Lea(obj)),
                            Some(_) => unreachable_fast!(), // #using Invariant-child-slot-None
                        }
                        self.try_task(ator); // #intro Invariant-(Lea,Lea)->Task
                    },
                    // #using Invariant-child-slot-None
                    InFrame::Task(_) => unreachable_fast!(),
                }
            }

            /// Extract locally-owned Brc(_) to child InFrame.
            ///
            /// Each child: parent slot=None; child owns extracted Tree.
            /// Caller attaches Ref, completing Invariant-child-slot-None.
            pub(super) fn children(&mut self, ator:&A) -> (Option<Self>, Option<Self>) {

                fn take_slot<Leaf, A: LeafApplicator<Leaf>>
                (slot: &mut Option<Tree<Leaf>>, ator:&A) -> Option<InFrame<Leaf, A>> {
                    match &*slot {
                        Some(Tree::Brc(_)) => match slot.take() {
                            Some(Tree::Brc(b)) => Some(InFrame::new(*b, ator)),
                            // Some(Brc(_)) just proven; no mutation.
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

        /// Parent Frame + slot expanded by child Frame.
        ///
        /// Invariant-parent-before-child:
        /// Ref of Frame at index i => self.0 < i.
        pub(super) struct Ref(usize, bool);
        impl Ref {
            /// Caller asserts idx valid.
            #[inline]
            pub(super) fn right(idx: usize) -> Self {Self(idx, true)}

            /// Caller asserts idx valid.
            #[inline]
            pub(super) fn left(idx: usize) -> Self {Self(idx, false)}

            /// Select referenced parent slot.
            #[inline]
            pub(super) fn slot<'a, Leaf>
            (&self, frm: &'a mut (Option<Tree<Leaf>>, Option<Tree<Leaf>>))
            -> &'a mut Option<Tree<Leaf>> {
                match self.1 {
                    true => &mut frm.1,
                    false => &mut frm.0,
                }
            }

            /// Get referenced parent Frame.
            ///
            /// #using Invariant-parent-before-child:
            /// just-popped Frame at index i => self.0<i==vec.len().
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

    // Invariants:
    //
    // Invariant-parent-before-child:
    //   Frame at index i, src=Some(Ref(parent,_)) => parent<i.
    //
    // Invariant-child-slot-None:
    //   non-bottom Frame <-> has exactly one None parent slot.
    //   child Frame owns that slot's expansion.
    //
    // Invariant-(Lea,Lea)->Task:
    //   Hold never has (Some(Lea(_)),Some(Lea(_)));
    //   that state immediately -> Task(_).
    //
    // Invariant-expand'd-Hold-not-Brc:
    //   post-expand Hold slots only None|Some(Lea(_)), never Some(Brc(_));
    //   every Hold waits on >=1 live child Frame.
    //
    // Invariant-top-Task:
    //   every reduce-loop entry: top Frame has Task(_).
    //
    // Invariant-bottom-src-None:
    //   every reduce-loop entry: exactly one live src=None bottom Frame.
    //   each iteration returns bottom Lea(_) or leaves live bottom Frame
    //   + nonempty FrameQ.
    pub(super) struct FrameQ<Leaf, A: LeafApplicator<Leaf>>
    (Vec<Frame<Leaf, A>>);

    impl <Leaf, A: LeafApplicator<Leaf>> FrameQ<Leaf, A> {
        pub(super) fn new(b: (Tree<Leaf>, Tree<Leaf>), ator:&A) -> Self {
            let q = alloc::vec![Frame{
                src:None,
                innr:InFrame::new(b, ator)
            }];
            // #intro Invariant-bottom-src-None
            Self(q)
        }

        /// Requires nonempty FrameQ.
        ///
        /// Extract all locally-owned Brc(_) reachable from current suffix.
        /// Return:
        ///  - #intro Invariant-expand'd-Hold-not-Brc
        ///  - preserve Invariant-parent-before-child
        ///  - preserve/#intro Invariant-child-slot-None
        ///  - #intro Invariant-top-Task
        fn expand(&mut self, ator:&A) {
            // Nonempty call sites:
            //  - initial FrameQ::new;
            //  - Brc(_) after replacement push.
            let mut idx = self.0.len() - 1;
            while idx < self.0.len() {
                let (lc, rc) = self.0[idx].innr.children(ator);

                if let Some(innr) = lc {
                    // detach left Brc(_) => parent slot=None.
                    // push child Frame strictly after parent Frame.
                    self.0.push(Frame{src:Some(Ref::left(idx)), innr});
                    // #intro Invariant-parent-before-child
                    // #intro Invariant-child-slot-None
                }

                if let Some(innr) = rc {
                    // same for right.
                    self.0.push(Frame{src:Some(Ref::right(idx)), innr});
                    // #intro Invariant-parent-before-child
                    // #intro Invariant-child-slot-None
                }

                idx += 1;
            }

            // No live Hold has local Brc(_).
            // #intro Invariant-expand'd-Hold-not-Brc
            //
            // #using Invariant-(Lea,Lea)->Task:
            // top Hold => >=1 None.
            // #using Invariant-child-slot-None:
            // None => live child Frame above; contradiction.
            // #intro Invariant-top-Task
        }

        pub(super) fn reduce(mut self, ator:&A) -> Leaf {
            self.expand(ator);

            while let Some(Frame {src, innr}) = self.0.pop() {match innr {
                // #using Invariant-top-Task
                InFrame::Task(tsk) => match ator.completed(tsk) {
                    Tree::Lea(o) => match src {
                        Some(rf)
                        // #using Invariant-parent-before-child:
                        // parent Frame survives child Frame pop.
                        // #using Invariant-child-slot-None:
                        // referenced slot=None.
                        => rf.frame(&mut self.0).innr.fill_slot(rf, o, ator),

                        // #elim Invariant-bottom-src-None
                        None => return o,
                    },

                    Tree::Brc(b) => {
                        // Replace expansion; preserve src.
                        self.0.push(Frame {src, innr:InFrame::new(*b, ator)});

                        // #elim Invariant-expand'd-Hold-not-Brc
                        // #elim Invariant-top-Task
                        self.expand(ator);
                        // #intro Invariant-expand'd-Hold-not-Brc
                        // #intro Invariant-top-Task
                    },
                },

                _ => unreachable_fast!(), // #using Invariant-top-Task
            }}

            // #using Invariant-bottom-src-None
            unreachable_fast!()
        }
    }
}
