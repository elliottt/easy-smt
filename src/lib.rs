#![doc = include_str!("../README.md")]

mod context;
mod known_atoms;
mod sexpr;
mod solver;

pub use context::{Context, ContextBuilder, Response};
pub use sexpr::{DisplayExpr, SExpr, SExprData};
