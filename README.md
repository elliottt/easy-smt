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
use easy_smt::{ContextBuilder, Response};

fn main() -> std::io::Result<()> {
    // Create a new context, backed by a Z3 subprocess.
    let mut ctx = ContextBuilder::new()
        .solver("z3", ["-smt2", "-in"])
        .build()?;

    // Declare `x` and `y` variables that are bitvectors of width 32.
    let bv32 = ctx.bit_vec_sort(ctx.numeral(32));
    let x = ctx.declare("x", bv32)?;
    let y = ctx.declare("y", bv32)?;

    // Assert that `x * y = 18`.
    ctx.assert(ctx.eq(
        ctx.bvmul(x, y),
        ctx.binary(32, 18),
    ))?;

    // And assert that neither `x` nor `y` is 1.
    ctx.assert(ctx.not(ctx.eq(x, ctx.binary(32, 1))))?;
    ctx.assert(ctx.not(ctx.eq(y, ctx.binary(32, 1))))?;

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
    Ok(())
}
```

## Debugging

### Displaying S-Expressions

Want to display an S-Expression that you've built up to make sure it is what you
expect? You can use the `easy_smt::Context::display` method:

```rust
use easy_smt::ContextBuilder;

let ctx = ContextBuilder::new().build().unwrap();

let my_s_expr = ctx.list(vec![
    ctx.atom("hi"),
    ctx.atom("hello"),
    ctx.numeral(42),
]);

let string = format!("{}", ctx.display(my_s_expr));
assert_eq!(string, "(hi hello 42)");
```

### Logging Solver Interactions

Need to debug exactly what is being sent to and received from the underlying
solver? `easy-smt` uses the `log` crate and logs all communication with the
solver at the `TRACE` log level.

For example, you can use `env_logger` to see the log messages. Initialize the
logger at the start of `main`:

```rust
fn main() {
    env_logger::init();

    // ...
}
```

And then run your program with the `RUST_LOG="easy_smt=trace"` environment
variable set to see the `TRACE` logs:

```shell
$ RUST_LOG="easy_smt=trace" cargo run --example sudoku
[2023-01-09T23:41:05Z TRACE easy_smt::solver] -> (set-option :print-success true)
[2023-01-09T23:41:05Z TRACE easy_smt::solver] <- success
[2023-01-09T23:41:05Z TRACE easy_smt::solver] -> (set-option :produce-models true)
[2023-01-09T23:41:05Z TRACE easy_smt::solver] <- success
[2023-01-09T23:41:05Z TRACE easy_smt::solver] -> (set-option :produce-unsat-cores true)
[2023-01-09T23:41:05Z TRACE easy_smt::solver] <- success
[2023-01-09T23:41:05Z TRACE easy_smt::solver] -> (declare-fun cell_0_0 () Int)
[2023-01-09T23:41:05Z TRACE easy_smt::solver] <- success
[2023-01-09T23:41:05Z TRACE easy_smt::solver] -> (assert (and (> cell_0_0 0) (<= cell_0_0 9)))
[2023-01-09T23:41:05Z TRACE easy_smt::solver] <- success
[2023-01-09T23:41:05Z TRACE easy_smt::solver] -> (declare-fun cell_0_1 () Int)
[2023-01-09T23:41:05Z TRACE easy_smt::solver] <- success
[2023-01-09T23:41:05Z TRACE easy_smt::solver] -> (assert (and (> cell_0_1 0) (<= cell_0_1 9)))
[2023-01-09T23:41:05Z TRACE easy_smt::solver] <- success
...
```

### Replaying Solver Interactions

You can save all commands that are being sent to the solver to a file that you
can replay without needing to dynamically rebuild your expressions, assertions,
and commands.

```rust
use easy_smt::ContextBuilder;

fn main() -> std::io::Result<()> {
    let ctx = ContextBuilder::new()
        // Everything needed to replay the solver session will be written
        // to `replay.smt2`.
        .replay_file(Some(std::fs::File::create("replay.smt2")?))
        .solver("z3", ["-smt2", "-in"])
        .build()?;

    // ...

    Ok(())
}
```

## Inspiration

Inspired by the [`simple-smt`](https://hackage.haskell.org/package/simple-smt)
haskell package.
