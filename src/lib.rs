#![doc = include!("../README.md")]

mod context;
mod known_atoms;
mod sexpr;
mod solver;

pub use context::{Context, Response};
pub use sexpr::{DisplayExpr, SExpr, SExprData};
