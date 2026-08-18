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

extern crate alloc;
use core::fmt;
use alloc::boxed::Box;
use norm::FrameQ;

/// 1. ApplicatorTask may "fail", but what is means to "fail" is semantics local
///    to the implementor - just like what false or absurdity is at the
///    foundations of mathematics. The implementor must agree with himself
///    on that meaning. We, on our side, simply do not - and should not - care.
/// 2. If `Tree::Brc(Box::new(Branch {l:Tree::Lea(op), r:Tree::Lea(x)}))`
///    is returned by completed(), is it naively re-apply-ed.
/// 3. LeafApplicator is assumed to be pure. Whether its actually pure
///    is up to implementation - in-fact many times impurity is desired
///    - but that is again up to the implementor.
pub trait LeafApplicator<Leaf> {
    type ApplicatorTask;

    /// Begin or schedule an application (perhaps by another thread).
    fn apply(&self, operator:Leaf, operand:Leaf) -> Self::ApplicatorTask;

    /// Wait for and obtain application result.
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

        /// DO NOT CONTSRUCT RAW: use InFrame::new()
        pub(super) enum InFrame<Leaf, A: LeafApplicator<Leaf>>{
            Task(A::ApplicatorTask),
            Hold((Option<Tree<Leaf>>, Option<Tree<Leaf>>))
        }
        impl <Leaf, A: LeafApplicator<Leaf>> InFrame<Leaf, A> {
            pub(super) fn new(b: (Tree<Leaf>, Tree<Leaf>), ator:&A) -> Self {
                let mut innr = InFrame::Hold((Some(b.0), Some(b.1)));
                innr.try_task(ator);
                innr
            }
        }
        impl <Leaf, A: LeafApplicator<Leaf>> InFrame<Leaf, A> {
            /// not to be used outside of InFrame
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
            pub(super) fn fill_slot(&mut self, rf:Ref, obj:Leaf, ator:&A) {
                match self {
                    InFrame::Hold(lr) => {
                        *(rf.slot(lr)) = Some(Tree::Lea(obj));
                        // elim FrameQ-propr-post-expand-done-in
                        self.try_task(ator);
                        // intro FrameQ-propr-post-expand-done-in
                    },
                    // never produced children
                    InFrame::Task(_) => unreachable!(),
                }
            }

            pub(super) fn children(&mut self, ator:&A) -> (Option<Self>, Option<Self>) {

                fn take_slot<Leaf, A: LeafApplicator<Leaf>>
                (slot: &mut Option<Tree<Leaf>>, ator:&A) -> Option<InFrame<Leaf, A>> {
                    match &*slot {
                        Some(Tree::Brc(_)) => match slot.take() {
                            Some(Tree::Brc(b)) => {
                                let mut inf = InFrame::Hold((Some(b.0), Some(b.1)));
                                inf.try_task(ator);
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
                    InFrame::Hold((l, r)) => (
                        take_slot(l, ator),
                        take_slot(r, ator)
                    )
                }
            }
        }

        pub(super) struct Ref(usize, bool);
        impl Ref {
            /// Caller must assert this idx is valid
            #[inline]
            pub(super) fn right(idx: usize) -> Self {Self(idx, true)}

            /// Caller must assert this idx is valid
            #[inline]
            pub(super) fn left(idx: usize) -> Self {Self(idx, false)}

            #[inline]
            pub(super) fn slot<'a, Leaf>
            (&self, frm: &'a mut (Option<Tree<Leaf>>, Option<Tree<Leaf>>))
            -> &'a mut Option<Tree<Leaf>> {
                match self.1 {
                    true => &mut frm.1,
                    false => &mut frm.0,
                }
            }

            #[inline]
            pub(super) fn frame<'a, Leaf, A: LeafApplicator<Leaf>>
            (&self, vec: &'a mut [Frame<Leaf, A>])
            -> &'a mut Frame<Leaf, A> { &mut vec[self.0]}
        }

        pub(super) struct Frame<Leaf, A: LeafApplicator<Leaf>> {
            pub(super) src: Option<Ref>, // (parent_index, slot_is_right)
            pub(super) innr: InFrame<Leaf, A>
        }
    }

    use alloc::vec::Vec;
    use crate::{LeafApplicator, Tree};
    use frame::{Frame, InFrame, Ref};

    // properties:
    //  - FrameQ-propr-min-1
    //  - FrameQ-propr-post-expand-OO-pop
    //  - FrameQ-propr-post-expand-done-in
    pub(super) struct FrameQ<Leaf, A: LeafApplicator<Leaf>>
    (Vec<Frame<Leaf, A>>);

    impl <Leaf, A: LeafApplicator<Leaf>> FrameQ<Leaf, A> {
        pub(super) fn new(b: (Tree<Leaf>, Tree<Leaf>), ator:&A) -> Self {
            let q = alloc::vec![Frame{
                src:None,
                innr:InFrame::new(b, ator)
            }];
            // intro FrameQ-propr-min-1
            Self(q)
        }

        fn expand(&mut self, ator:&A) {
            let mut idx = self.0.len() - 1; // by FrameQ-propr-min-1
            while idx < self.0.len() {
                let (lc, rc) = self.0[idx].innr.children(ator);
                if let Some(innr) = lc {
                    self.0.push(Frame{src:Some(Ref::left(idx)), innr});
                }
                if let Some(innr) = rc {
                    self.0.push(Frame{src:Some(Ref::right(idx)), innr});
                }
                idx += 1;
            }
            // intro FrameQ-propr-post-expand-OO-pop
        }

        pub(super) fn reduce(&mut self, ator:&A) -> Leaf {
            self.expand(ator);

            while let Some(Frame {
                src,
                innr:InFrame::Task(tsk)
            }) = self.0.pop() { // by FrameQ-propr-post-expand-OO-pop
                match ator.completed(tsk) {
                    Tree::Lea(o) => match src {
                        Some(rf)
                        => rf.frame(&mut self.0).innr.fill_slot(rf, o, ator),
                        None => return o, // elim FrameQ-propr-min-1
                    },
                    Tree::Brc(b) => {
                        self.0.push(Frame {src, innr:InFrame::new(*b, ator)});
                        // emlim FrameQ-propr-post-expand-OO-pop
                        self.expand(ator);
                        // intro FrameQ-propr-post-expand-OO-pop
                    },
                }
            }
            unreachable!() // by FrameQ-propr-post-expand-OO-pop
        }
    }
}
