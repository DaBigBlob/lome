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

// leaf is now constructor
// pub trait ConApplicator<Con> {
//     /// Owned handle for one application.
//     type ApplicatorTask;

//     /// Begin or schedule `operator operand`.
//     fn task(&mut self, operator:Con, operand:Con) -> Self::ApplicatorTask;

//     /// Wait for or execute `task`, then return its application result.
//     fn completed(&mut self, task:Self::ApplicatorTask) -> Tree<Con>;
// }

/*

we only need to care about reducing to App(Con, Con).
we will now decide and fill in when the

(Con, Con) is taken from above
app is handled below.
we need to construct pure App in terms of Con.

*/

// type AppTree<L> = lome0::Tree<L>;

// we must recognize that we are the Leaf implementors
#[derive(PartialEq, Eq)]
pub enum AppLeaf<Con>{
    Abs(Box<(AppLeaf<Con>, AppLeaf<Con>)>),
    App(AppTree<Con>),
    Lea(Con)
}
// now we impl apply on all pairs of Tree<Con>
// (Con, Con) -> Tree<Con> is offloaded to above

pub type AppTree<Con> = lome0::Tree<Box<AppLeaf<Con>>>;

// we must now implement applicator for (Leaf, Leaf)
// - that is our responsibility, of which,
// (Leaf::Con, Leaf::Con) is the responsibility of above level
