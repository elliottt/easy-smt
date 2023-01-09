<div align="center">
  <h1><code>easy-smt</code></h1>

  <p>
    <strong>An easy way to interact with an SMT solver!</strong>
  </p>

  <p>
    <a href="https://github.com/elliottt/easy-smt/actions?query=workflow%3ACI"><img src="https://github.com/elliottt/easy-smt/actions/workflows/ci.yml/badge.svg" alt="Build status" /></a>
    <img src="https://img.shields.io/badge/rustc-stable+-green.svg" alt="Supports rustc stable" />
    <a href="https://docs.rs/easy-smt"><img src="https://docs.rs/easy-smt/badge.svg" alt="Documentation Status" /></a>
  </p>
</div>

## About

`easy-smt` is a crate for interacting with an SMT solver subprocess. This crate
provides APIs for

* building up expressions and assertions using [the SMT-LIB 2
  language](https://smtlib.cs.uiowa.edu/),
* querying an SMT solver for solutions to those assertions,
* and inspecting the solver's results.

`easy-smt` works with any solver, as long as the solver has an interactive REPL
mode. You just tell `easy-smt` how to spawn the subprocess.

## Example

```rust
# fn run() -> std::io::Result<()> {
use easy_smt::{Context, Response};

// Create a new context, backed by a Z3 subprocess.
let mut ctx = easy_smt::Context::new("z3", ["-smt2", "-in"])?;

// Declare `x` and `y` variables that are bitvectors of width 32.
let bv32 = ctx.bit_vec_sort(ctx.i32(32));
let x = ctx.declare("x", bv32)?;
let y = ctx.declare("y", bv32)?;

// Assert that `x * y = 0x12`.
ctx.assert(ctx.eq(
    ctx.bvmul(x, y),
    ctx.atom("#x00000012"),
))?;

// And assert that neither `x` nor `y` is 1.
ctx.assert(ctx.not(ctx.eq(x, ctx.atom("#x00000001"))))?;
ctx.assert(ctx.not(ctx.eq(y, ctx.atom("#x00000001"))))?;

// Check whether the assertions are satisfiable. They should be in this example.
assert_eq!(ctx.check()?, Response::Sat);

// Print the solution!
let solution = ctx.get_value(vec![x, y])?;
for (variable, value) in solution {
    println!("{} = {}", ctx.display(variable), ctx.display(value));
}
// There are many solutions, but the one I get from Z3 is:
//
//     x = #x10000012
//     y = #x38000001
//
// Solvers are great at finding edge cases and surprising-to-humans results! In
// this case, I would have naively expected something like `x = 2, y = 9` or
// `x = 3, y = 6`, but the solver found a solution where the multiplication
// wraps around. Neat!
# Ok(())
# }
# let _ = run();
```

## Inspiration

Inspired by the [`simple-smt`](https://hackage.haskell.org/package/simple-smt)
haskell package.
