#![no_std]
#![deny(
    clippy::panic,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::todo,
    clippy::unimplemented,
    clippy::arithmetic_side_effects,
    clippy::unreachable
)]

use lome_calc::*;

/// extended expression
pub struct STmt<ID: IDtrt> {id:ID, exp:Expr<ID>}

pub fn lol<ID: IDtrt>() {
    let a: Ctx<ID> = lome_calc::Ctx::new();
}
