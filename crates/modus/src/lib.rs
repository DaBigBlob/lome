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
        { unreachable!() }
        #[cfg(not(debug_assertions))]
        // SAFETY: each call site proves unreachable.
        unsafe {core::hint::unreachable_unchecked()}
    }};
    ($($arg:tt)+) => {{
        #[cfg(debug_assertions)]
        { unreachable!($($arg)+) }
        #[cfg(not(debug_assertions))]
        // SAFETY: each call site proves unreachable.
        unsafe {core::hint::unreachable_unchecked()}
    }};
}

extern crate alloc;
use core::fmt;
use alloc::boxed::Box;
use norm::FrameQ;

/// Performs applications of Leaf operators to Leaf operands.
///
/// Application failure semantics are implementor-local. The implementor must
/// use them consistently; the normalizer treats every returned Tree uniformly.
///
/// Returning `Tree::Brc(Box::new((Tree::Lea(operator), Tree::Lea(operand))))`
/// causes (eventual) naive reapplication.
///
/// If each completed application observationally depends only on its operator
/// and operand, normalization is schedule-independent. Otherwise behavior may
/// depend on scheduling and execution order.
///
/// Task protocol:
/// 1. Multiple ApplicatorTasks may coexist.
/// 2. apply() must remain usable while earlier ApplicatorTasks are outstanding.
/// 3. Later calls must not invalidate earlier ApplicatorTasks.
/// 4. ApplicatorTasks may be passed to completed() in unspecified order.
/// 5. completed() consumes exactly one ApplicatorTask and returns the result of
///    the exact application represented by that task.
/// 6. completed() may wait for or execute the represented application.
/// 7. Dropping an ApplicatorTask without calling completed() must safely cancel,
///    detach, or discard it. This may occur during unwinding.
/// 8. ApplicatorTask need not be Send; handles remain on the normalization
///    thread.
pub trait LeafApplicator<Leaf> {
    /// Owned handle for one application.
    type ApplicatorTask;

    /// Begin or schedule `operator operand`.
    fn apply(&self, operator:Leaf, operand:Leaf) -> Self::ApplicatorTask;

    /// Wait for or execute `task`, then return its application result.
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

/// DONT CONSTRUCT RAW: use InFrame::new().
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

    /// try Hold -> Task.
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
                    _ => unreachable_fast!("trivial")
                },
                _ => ()
            },
            InFrame::Task(_) => (),
        }
    }

    pub(super) fn fill_slot(&mut self, self_ref:Ref, with:Leaf, ator:&A) {
        match self {
            InFrame::Hold(lr) => {
                match self_ref.slot(lr) {
                    slot @ None => *slot = Some(Tree::Lea(with)),
                    Some(_) => unreachable_fast!(
                        "Caller guarantees the referenced slot is None."
                    ),
                }
                self.try_task(ator);
            },
            InFrame::Task(_) => unreachable_fast!(
                "A referenced parent slot can exist only in Hold."
            ),
        }
    }

    pub(super) fn pop_children(&mut self, ator:&A) -> (Option<Self>, Option<Self>) {

        fn slot2child<Leaf, A: LeafApplicator<Leaf>>
        (slot: &mut Option<Tree<Leaf>>, ator:&A) -> Option<InFrame<Leaf, A>> {
            match &*slot {
                Some(Tree::Brc(_)) => match slot.take() {
                    Some(Tree::Brc(b)) => Some(InFrame::new(*b, ator)),
                    _ => unreachable_fast!("trivial"),
                },
                _ => None,
            }
        }

        match self {
            InFrame::Task(_) => (None, None),
            InFrame::Hold((l, r)) => (
                slot2child(l, ator),
                slot2child(r, ator)
            )
        }
    }
}

/// Parent Frame and expanded slot.
pub(super) struct Ref(usize, bool);
impl Ref {
    /// Caller ensures idx is valid.
    #[inline]
    pub(super) fn right(idx: usize) -> Self {Self(idx, true)}
    /// Caller ensures idx is valid.
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
    /// None only for the bottom Frame.
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
            let q = alloc::vec![Frame{src:None, innr:InFrame::new(b, ator)}];
            Self(q)
        }

        fn expand(&mut self, ator:&A) {
            // alwys have >=1 frame unless self dropped
            let mut idx = self.0.len() - 1;
            while idx < self.0.len() {
                let (lc, rc) = self.0[idx].innr.pop_children(ator);
                if let Some(innr) = lc {
                    self.0.push(Frame{src:Some(Ref::left(idx)), innr});
                }
                if let Some(innr) = rc {
                    self.0.push(Frame{src:Some(Ref::right(idx)), innr});
                }
                idx += 1;
            }
        }

        pub(super) fn reduce(mut self, ator:&A) -> Leaf {
            self.expand(ator); // reduce without expand is undefined

            // we take top
            while let Some(Frame {src, innr}) = self.0.pop() {match innr {
                InFrame::Task(tsk) => match ator.completed(tsk) {
                    // nice
                    Tree::Lea(o) => match src {
                        // parent slot fill
                        Some(rf) => rf.frame(&mut self.0).
                                    innr.fill_slot(rf, o, ator),
                        // seems like we have reached the end of queue
                        None => return o,
                    },
                    // one must imagine sisyphus happy
                    Tree::Brc(b) => {
                        // like inside FrameQ::new()
                        self.0.push(Frame {src, innr:InFrame::new(*b, ator)});
                        // like start of reduce()
                        self.expand(ator);
                    },
                },
                _ => unreachable_fast!(
                    "expand() and each non-returning iteration leave top Task."
                ),
            }}
            unreachable_fast!(
                "The bottom Frame remains until it returns a leaf."
            )
        }
    }
}
