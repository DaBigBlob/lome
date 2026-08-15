/* BSD-3 License */
#![no_std]
#![deny(
    unsafe_op_in_unsafe_fn,
    clippy::panic,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::todo,
    clippy::unimplemented,
    clippy::indexing_slicing,
    clippy::arithmetic_side_effects,
    clippy::undocumented_unsafe_blocks,
)]
#![allow(clippy::unreachable)]

extern crate alloc;
use alloc::boxed::Box;
use core::{fmt, hash::Hash, mem};
use hashbrown::HashMap;

/// de bruijn index
/// beware: IDs will be cloned as often as terms
pub trait IDtrt: Eq + Hash + Clone + fmt::Debug {}
impl<T: Eq + Hash + Clone + fmt::Debug> IDtrt for T {}

/// expression
#[derive(PartialEq, Eq, Clone)]
pub enum Expr<ID: IDtrt> {
    /// rule; abstraction
    Rul{m:Box<Expr<ID>>, b:Box<Expr<ID>>},
    /// modus ponens; application
    Mod{f:Box<Expr<ID>>, x:Box<Expr<ID>>},
    /// hypothesis; variable; free variables are axioms
    Hyp(ID),
    /// tombstone; intermediate representation;
    /// placed in redex when it is to be dropped after this use
    #[doc(hidden)]
    Taken
}
impl <ID: IDtrt> Expr<ID> {
    /// in-place normalize
    /// Ok() is good else bad; in ok, true is normalized else not
    pub fn norm(&mut self) -> Result<bool, ()> {
        match self {
            Expr::Mod { f, x } => match f.as_mut() {
                Expr::Rul { m, b } => {
                    // norm m, x before match; success does not matter
                    match (m.norm(), x.norm()) { // call-by-value
                        (Ok(_), Ok(_)) => { // now match
                            let mut map: IDMapExpr<ID> = IDMapExpr::new();
                            match map.mtch(x, m) {
                                true => {
                                    *self = map.bound(b);
                                    self.norm() // recur till Ok(false) or Err
                                },
                                false => Err(()), // did not match
                            }
                        }
                        _ => Err(())
                    }
                },
                kf => match kf.norm() {
                    Ok(true) => self.norm(), // self changed, retry
                    x => x, // else forward; includes (hyp ...) as Ok(false)
                }
            }
            _ => Ok(false) // nothing to do but okay
        }
    }

    fn take(&mut self) -> Self {mem::replace(self, Expr::Taken)}
}

impl  <ID: IDtrt> fmt::Debug for Expr<ID> {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Rul { m, b } => write!(fmt, "({m:?}) -> ({b:?})"),
            Self::Mod { f, x } => write!(fmt, "({f:?}) ({x:?})"),
            Self::Hyp(id) => write!(fmt, "{id:?}"),
            Self::Taken => write!(fmt, "<TAKEN>"),
        }
    }
}

struct IDMapExpr<ID: IDtrt>(HashMap<ID, Expr<ID>>);
impl <ID: IDtrt> IDMapExpr<ID> {
    pub fn new() -> Self { Self(HashMap::new()) }
    // we only clone id and v if they dont exist in map
    fn set(&mut self, id: ID, v: Expr<ID>) -> bool {
        match self.0.get(&id) {
            Some(exp) => {exp == &v},
            None => {
                self.0.insert(id, v);
                true
            }
        }
    }
    /// populates map with [xx/hol(mm)], replaces xx and hol(mm) with tombstone
    /// note: exp and m must be normalized individually before calling mtch;
    fn mtch(&mut self, xx:&mut Expr<ID>, mm:&mut Expr<ID>) -> bool {
        match mm.take() {
            Expr::Hyp(id) => self.set(id, xx.take()),
            mut mmm => match (xx, &mut mmm) {
                (
                    Expr::Rul{ m:em, b:eb },
                    Expr::Rul{ m:mm, b:mb }
                ) => matches!((self.mtch(em, mm), self.mtch(eb, mb)), (true, true)),
                (
                    Expr::Mod{ f:ef, x:ex },
                    Expr::Mod{ f:mf, x:mx }
                ) => matches!((self.mtch(ef, mf), self.mtch(ex, mx)), (true, true)),
                _ => false
            }, // drop mmm with tombstones
        }
    }
    /// returns bb[val/var], replaces bb with tombstone
    /// note: b must not be normalized before calling bind
    fn bound(&mut self, bb:&mut Expr<ID>) -> Expr<ID> {
        match bb {
            Expr::Rul { m, b } => {
                **m = self.bound(m);
                **b = self.bound(b);
                bb.take()
            },
            Expr::Mod { f, x } => {
                **f = self.bound(f);
                **x = self.bound(x);
                bb.take()
            },
            Expr::Hyp(id) => match self.0.get(id) {
                Some(ex) => ex.clone(),
                None => bb.take(), // free variable
            }
            Expr::Taken => unreachable!() // converging + same branch is taken once
        }
    }
}
