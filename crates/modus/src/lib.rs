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
///    `Tree::Brc(Box::new((Tree::Lea(op), Tree::Lea(x))))` causes naive reapply.
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
                let mut frm = FrameQ::new(*bb, applicator);
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
            /// Establish FrameQ-inv-ready-is-task: Hold(Lea,Lea) -> Task.
            pub(super) fn new(b: (Tree<Leaf>, Tree<Leaf>), ator:&A) -> Self {
                let mut innr = InFrame::Hold((Some(b.0), Some(b.1)));
                innr.try_task(ator);
                innr
            }

            /// Internal. Preserve FrameQ-inv-ready-is-task.
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
                            // Both just proven Some(Lea); no intervening mutation.
                            _ => unreachable_fast!()
                        },
                        _ => ()
                    },
                    // Task: no children, ready.
                    InFrame::Task(_) => (),
                }
            }

            /// Requires selected slot=None; truthful child-parent Ref.
            ///
            /// FrameQ-inv-child-slot: parent slot None while child live.
            /// Fill consumes correspondence.
            pub(super) fn fill_slot(&mut self, rf:Ref, obj:Leaf, ator:&A) {
                match self {
                    InFrame::Hold(lr) => {
                        match rf.slot(lr) {
                            slot @ None => *slot = Some(Tree::Lea(obj)),
                            Some(_) => unreachable_fast!(), // FrameQ-inv-child-slot
                        }
                        self.try_task(ator); // preserve FrameQ-inv-ready-is-task
                    },
                    // Child only references parent Hold with detached slot.
                    InFrame::Task(_) => unreachable_fast!(), // FrameQ-inv-child-slot
                }
            }

            /// Extract locally-owned branches to child frames.
            ///
            /// Each child: parent slot=None; child owns extracted computation.
            /// Caller attaches Ref, completing FrameQ-inv-child-slot.
            pub(super) fn children(&mut self, ator:&A) -> (Option<Self>, Option<Self>) {

                fn take_slot<Leaf, A: LeafApplicator<Leaf>>
                (slot: &mut Option<Tree<Leaf>>, ator:&A) -> Option<InFrame<Leaf, A>> {
                    match &*slot {
                        Some(Tree::Brc(_)) => match slot.take() {
                            Some(Tree::Brc(b)) => Some(InFrame::new(*b, ator)),
                            // Brc just proven; no intervening mutation.
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

        /// Parent frame + slot computed by child.
        ///
        /// FrameQ-inv-parent-before-child:
        /// Ref of frame i => self.0 < i.
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

            /// Get referenced parent frame.
            ///
            /// Just-popped child i: parent<i==vec.len()
            /// by FrameQ-inv-parent-before-child.
            #[inline]
            pub(super) fn frame<'a, Leaf, A: LeafApplicator<Leaf>>
            (&self, vec: &'a mut [Frame<Leaf, A>])
            -> &'a mut Frame<Leaf, A> { &mut vec[self.0]}
        }

        pub(super) struct Frame<Leaf, A: LeafApplicator<Leaf>> {
            /// None only root continuation.
            pub(super) src: Option<Ref>,
            pub(super) innr: InFrame<Leaf, A>
        }
    }

    use alloc::vec::Vec;
    use crate::{LeafApplicator, Tree};
    use frame::{Frame, InFrame, Ref};

    // FrameQ invariants:
    //
    // FrameQ-inv-parent-before-child:
    //   frame i, src=Some(Ref(parent,_)) => parent<i.
    //
    // FrameQ-inv-child-slot:
    //   non-root frame <-> exactly one None parent slot.
    //   child owns that slot's computation.
    //
    // FrameQ-inv-ready-is-task:
    //   Hold never has two Lea; Hold(Lea,Lea) immediately -> Task.
    //
    // FrameQ-inv-expanded-hold:
    //   post-expand Hold slots only None|Lea, never Brc;
    //   every Hold waits on >=1 live child.
    //
    // FrameQ-inv-top-task:
    //   every reduce-loop entry: final frame Task.
    //
    // FrameQ-inv-root-continuation:
    //   every reduce-loop entry: exactly one live src=None root continuation.
    //   each iteration returns root Lea or leaves live root + nonempty queue.
    //
    // Derived:
    //   child-slot
    // + parent-before-child
    // + ready-is-task
    // + expanded-hold
    // => top-task.
    pub(super) struct FrameQ<Leaf, A: LeafApplicator<Leaf>>
    (Vec<Frame<Leaf, A>>);

    impl <Leaf, A: LeafApplicator<Leaf>> FrameQ<Leaf, A> {
        pub(super) fn new(b: (Tree<Leaf>, Tree<Leaf>), ator:&A) -> Self {
            let q = alloc::vec![Frame{
                src:None,
                innr:InFrame::new(b, ator)
            }];
            // Establish unique root continuation.
            Self(q)
        }

        /// Requires nonempty queue.
        ///
        /// Extract all locally-owned Brc reachable from current suffix.
        /// Return:
        ///  - establish expanded-hold;
        ///  - preserve parent-before-child;
        ///  - preserve/establish child-slot;
        ///  - with other invariants establish top-task.
        fn expand(&mut self, ator:&A) {
            // Nonempty call sites:
            //  - initial FrameQ::new;
            //  - returned Brc after replacement push.
            let mut idx = self.0.len() - 1;
            while idx < self.0.len() {
                let (lc, rc) = self.0[idx].innr.children(ator);

                if let Some(innr) = lc {
                    // detach left Brc => parent slot=None;
                    // push child strictly after parent.
                    self.0.push(Frame{src:Some(Ref::left(idx)), innr});
                    // establish child's parent-before-child + child-slot.
                }

                if let Some(innr) = rc {
                    // same right.
                    self.0.push(Frame{src:Some(Ref::right(idx)), innr});
                    // establish child's parent-before-child + child-slot.
                }

                idx += 1;
            }
            // No live Hold has local Brc => expanded-hold.
            //
            // Hold cannot have two Lea (ready-is-task), so topmost Hold has None.
            // child-slot => live child above it, contradiction.
            // Therefore top frame Task => top-task.
        }

        pub(super) fn reduce(&mut self, ator:&A) -> Leaf {
            self.expand(ator);

            while let Some(Frame {src, innr}) = self.0.pop() {match innr {
                // FrameQ-inv-top-task
                InFrame::Task(tsk) => match ator.completed(tsk) {
                    Tree::Lea(o) => match src {
                        Some(rf)
                        // parent-before-child => parent survives child pop;
                        // child-slot => referenced slot=None.
                        => rf.frame(&mut self.0).innr.fill_slot(rf, o, ator),

                        // root continuation complete.
                        None => return o,
                    },

                    Tree::Brc(b) => {
                        // Replace computation; preserve continuation/src.
                        self.0.push(Frame {src, innr:InFrame::new(*b, ator)});

                        // Re-establish expanded-hold/top-task.
                        self.expand(ator);
                    },
                },

                _ => unreachable_fast!(), // FrameQ-inv-top-task
            }}

            // Non-root completion leaves parent.
            // Root completion returns or pushes replacement root.
            unreachable_fast!() // FrameQ-inv-root-continuation
        }
    }
}
