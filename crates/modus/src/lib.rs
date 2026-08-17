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

use alloc::{boxed::Box, vec::Vec};
use core::fmt;

pub trait Object:  Sized {
    /// Override this if the object is an operator.
    /// A default implementation as non-operator is provided.
    ///
    /// Note: Input x is Object because that is the logical conclusion of Call-by-Value.
    fn apply(self, x: Self) -> Result<Expr<Self>, (Expr<Self>, Expr<Self>)> {
        Err((Expr::Obj(self), Expr::Obj(x)))
    }
}

/// Expression
pub enum Expr<O: Object> {
    /// Opaque Object
    Obj(O),
    /// Modus Ponens
    Mod(Box<(Expr<O>, Expr<O>)>)
}

pub trait Executor: Sync {
    type Task<'a, T: Send + 'a>: 'a
        where Self: 'a;
    /// Create a task for multiprocessing.
    ///
    /// Note for implementor: If you intend to circumvent multiprocessing,
    /// only store computation:F using this function.
    fn task<
        'a,
        T: Send + 'a,
        F: FnOnce() -> T + Send + 'a,
    >(&'a self, computation: F) -> Self::Task<'a, T>;
    /// Wait till the task is completed by whoever was executing the task.
    ///
    /// Note for implementor: If you intend to circumvent multiprocessing,
    /// run computation:F using this function.
    fn complete<
        'a,
        T: Send + 'a,
    >(&'a self, task: Self::Task<'a, T>) -> T;
}

impl <O: Object + Send> Expr<O> {
    /// Ok: Completely normalizez to a single Object.
    ///
    /// Err: Returns the A.apply(B) which failed as Expr::Mod(Box::new((A, B)).
    pub fn norm<Exec: Executor>(self, exec:&Exec) -> Result<O, Expr<O>> {
        let mut args = Vec::new();
        let mut exp = self;
        loop {
            match exp {
                Expr::Obj(op) => match args.pop() {
                    Some(task) => match exec.complete(task) {
                        Ok(x) => match op.apply(x) {
                            Ok(exp_) => {exp = exp_;}, // loop continue
                            Err(ee_) => return Err(Expr::Mod(Box::new(ee_))),
                        },
                        err => return err
                    },
                    None => return Ok(op),
                }
                Expr::Mod(bee) => {
                    let ee = *bee;
                    args.push(exec.task(move || ee.1.norm(exec)));
                    exp = ee.0;
                },
            }
        }
    }
}

impl <O: Object + fmt::Debug> fmt::Debug for Expr<O> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Obj(o) => write!(f, "{o:?}"),
            Expr::Mod(ee) => {
                let op = &(*ee).0;
                let x = &(*ee).1;
                write!(f, "({op:?}) ({x:?})")
            },
        }
    }
}

impl <O: Object + Clone> Clone for Expr<O> {
    fn clone(&self) -> Self {
        match self {
            Self::Obj(o) => Self::Obj(o.clone()),
            Self::Mod(bee) => Self::Mod(bee.clone()),
        }
    }
}
