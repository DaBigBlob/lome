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

use lome_modus as modus;

/// Abstraction
pub struct Abs;

/// Applicator
pub struct Applicator;
impl modus::LeafApplicator<Abs> for Applicator {
    type ApplicatorTask = (Abs, Abs);

    fn task(&self, operator:Abs, operand:Abs) -> Self::ApplicatorTask {
        todo!()
    }

    fn completed(&self, task:Self::ApplicatorTask) -> lome_modus::Tree<Abs> {
        todo!()
    }
}
