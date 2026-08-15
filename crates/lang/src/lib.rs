#![no_std]
#![deny(
    unsafe_op_in_unsafe_fn,
    clippy::panic,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::todo,
    clippy::unreachable,
    clippy::unimplemented,
    clippy::indexing_slicing,
    clippy::arithmetic_side_effects,
    clippy::undocumented_unsafe_blocks,
)]

use lome_calc::*;

/// extended expression
pub struct STmt<ID: IDtrt> {id:ID, exp:Expr<ID>}

pub fn lol<ID: IDtrt>() {
    let a: Ctx<ID> = lome_calc::Ctx::new();
}
