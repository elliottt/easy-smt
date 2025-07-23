use crate::{
    known_atoms::KnownAtoms,
    sexpr::{Arena, DisplayExpr, SExpr, SExprData},
    solver::Solver,
};
use std::{ffi, io, mem};

macro_rules! variadic {
    ($name:ident, $op:ident) => {
        pub fn $name<I: IntoIterator<Item = SExpr>>(&self, items: I) -> SExpr {
            let mut iter = items.into_iter().peekable();
            let first = iter.next().expect("At least one argument is expected");

            if iter.peek().is_some() {
                let args = std::iter::once(self.atoms.$op)
                    .chain(std::iter::once(first))
                    .chain(iter)
                    .collect();
                self.list(args)
            } else {
                first
            }
        }
    };
}

macro_rules! unary {
    ($name:ident, $op:ident) => {
        pub fn $name(&self, val: SExpr) -> SExpr {
            self.list(vec![self.atoms.$op, val])
        }
    };
}

macro_rules! binop {
    ($name:ident, $op:ident) => {
        pub fn $name(&self, lhs: SExpr, rhs: SExpr) -> SExpr {
            self.list(vec![self.atoms.$op, lhs, rhs])
        }
    };
}

macro_rules! right_assoc {
    ($name:ident, $many:ident, $op:ident) => {
        binop!($name, $op);
        variadic!($many, $op);
    };
}

macro_rules! left_assoc {
    ($name:ident, $many:ident, $op:ident) => {
        binop!($name, $op);
        variadic!($many, $op);
    };
}

macro_rules! chainable {
    ($name:ident, $many:ident, $op:ident) => {
        binop!($name, $op);
        variadic!($many, $op);
    };
}

macro_rules! pairwise {
    ($name:ident, $many:ident, $op:ident) => {
        binop!($name, $op);
        variadic!($many, $op);
    };
}

#[derive(Default)]
pub struct ContextBuilder {
    solver: Option<ffi::OsString>,
    solver_args: Vec<ffi::OsString>,
    replay_file: Option<Box<dyn io::Write + Send>>,
}

impl ContextBuilder {
    /// Construct a new builder with the default configuration.
    pub fn new() -> Self {
        Self::default()
    }

    /// Initialize the builder with Z3 defaults.
    pub fn with_z3_defaults(&mut self) -> &mut Self {
        self.solver("z3").solver_args(["-smt2", "-in", "-v:0"])
    }

    /// Initialize the builder with CVC5 defaults.
    pub fn with_cvc5_defaults(&mut self) -> &mut Self {
        self.solver("cvc5").solver_args(["--quiet", "--lang=smt2", "--incremental"])
    }

    /// Configure the solver that will be used.
    ///
    /// You can pass arguments to the underlying solver via the
    /// [`solver_args`][Self::solver_args] method.
    ///
    /// By default, no solver is configured, and any `Context` created will only
    /// be able to build and display expressions, not assert them or query for
    /// their satisfiability.
    pub fn solver<P>(&mut self, program: P) -> &mut Self
    where
        P: Into<ffi::OsString>,
    {
        self.solver = Some(program.into());
        self
    }

    /// Configure the arguments that will be passed to the solver.
    ///
    /// By default, no arguments are passed to the solver.
    pub fn solver_args<A>(&mut self, args: A) -> &mut Self
    where
        A: IntoIterator,
        A::Item: Into<ffi::OsString>,
    {
        self.solver_args = args.into_iter().map(|a| a.into()).collect();
        self
    }

    /// Clear the solver configuration, if any.
    ///
    /// This returns to the default, no-solver configuration, where any
    /// `Context` created will only be able to build and display expressions,
    /// not assert them or query for their satisfiability.
    pub fn without_solver(&mut self) -> &mut Self {
        self.solver = None;
        self.solver_args.clear();
        self
    }

    /// An optional file (or anything else that is `std::io::Write`-able) where
    /// all solver queries and commands are tee'd too.
    ///
    /// This let's you replay interactions with the solver offline, without
    /// needing to dynamically rebuild your expressions, queries, or commands.
    ///
    /// This is unused if no solver is configured.
    ///
    /// By default, there is no replay file configured.
    pub fn replay_file<W>(&mut self, replay_file: Option<W>) -> &mut Self
    where
        W: 'static + io::Write + Send,
    {
        self.replay_file = replay_file.map(|w| Box::new(w) as _);
        self
    }

    /// Finish configuring the context and build it.
    pub fn build(&mut self) -> io::Result<Context> {
        let arena = Arena::new();
        let atoms = KnownAtoms::new(&arena);

        let solver = if let Some(program) = self.solver.take() {
            Some(Solver::new(
                program,
                mem::take(&mut self.solver_args),
                self.replay_file
                    .take()
                    .unwrap_or_else(|| Box::new(io::sink())),
            )?)
        } else {
            None
        };

        let mut ctx = Context {
            solver,
            arena,
            atoms,
        };

        if ctx.solver.is_some() {
            ctx.set_option(":print-success", ctx.true_())?;
            ctx.set_option(":produce-models", ctx.true_())?;
        }

        Ok(ctx)
    }
}

/// An SMT-LIB 2 context, usually backed by a solver subprocess.
///
/// Created via a [`ContextBuilder`][crate::ContextBuilder].
pub struct Context {
    solver: Option<Solver>,
    arena: Arena,
    atoms: KnownAtoms,
}

/// # Solver Commands and Assertions
///
/// These methods send a command or assertion to the context's underlying
/// solver. As such, they involve I/O with a subprocess and are therefore
/// fallible.
///
/// ## Panics
///
/// These methods will panic when called if the context was not created with an
/// underlying solver (via
/// [`ContextBuilder::solver`][crate::ContextBuilder::solver]).
impl Context {
    pub fn set_option<K>(&mut self, name: K, value: SExpr) -> io::Result<()>
    where
        K: Into<String> + AsRef<str>,
    {
        let solver = self
            .solver
            .as_mut()
            .expect("set_option requires a running solver");
        solver.ack_command(
            &self.arena,
            self.atoms.success,
            self.arena
                .list(vec![self.atoms.set_option, self.arena.atom(name), value]),
        )
    }

    /// Assert `check-sat-assuming` with the given list of assumptions.
    pub fn check_assuming(
        &mut self,
        props: impl IntoIterator<Item = SExpr>,
    ) -> io::Result<Response> {
        let solver = self
            .solver
            .as_mut()
            .expect("check requires a running solver");
        let args = self.arena.list(props.into_iter().collect());
        solver.send(
            &self.arena,
            self.arena.list(vec![self.atoms.check_sat_assuming, args]),
        )?;
        let resp = solver.recv(&self.arena)?;
        if resp == self.atoms.sat {
            Ok(Response::Sat)
        } else if resp == self.atoms.unsat {
            Ok(Response::Unsat)
        } else if resp == self.atoms.unknown {
            Ok(Response::Unknown)
        } else {
            Err(io::Error::new(
                io::ErrorKind::Other,
                format!("Unexpected result from solver: {}", self.display(resp)),
            ))
        }
    }

    /// Assert `check-sat` for the current context.
    pub fn check(&mut self) -> io::Result<Response> {
        let solver = self
            .solver
            .as_mut()
            .expect("check requires a running solver");
        solver.send(&self.arena, self.arena.list(vec![self.atoms.check_sat]))?;
        let resp = solver.recv(&self.arena)?;
        if resp == self.atoms.sat {
            Ok(Response::Sat)
        } else if resp == self.atoms.unsat {
            Ok(Response::Unsat)
        } else if resp == self.atoms.unknown {
            Ok(Response::Unknown)
        } else {
            Err(io::Error::new(
                io::ErrorKind::Other,
                format!("Unexpected result from solver: {}", self.display(resp)),
            ))
        }
    }

    /// Declare a new constant with the provided sort
    pub fn declare_const<S: Into<String> + AsRef<str>>(
        &mut self,
        name: S,
        sort: SExpr,
    ) -> io::Result<SExpr> {
        let name = self.atom(name);
        let solver = self
            .solver
            .as_mut()
            .expect("declare_const requires a running solver");
        solver.ack_command(
            &self.arena,
            self.atoms.success,
            self.arena.list(vec![self.atoms.declare_const, name, sort]),
        )?;
        Ok(name)
    }

    pub fn declare_datatype<S: Into<String> + AsRef<str>>(
        &mut self,
        name: S,
        decl: SExpr,
    ) -> io::Result<SExpr> {
        let name = self.atom(name);
        let solver = self
            .solver
            .as_mut()
            .expect("declare_datatype requires a running solver");
        solver.ack_command(
            &self.arena,
            self.atoms.success,
            self.arena
                .list(vec![self.atoms.declare_datatype, name, decl]),
        )?;
        Ok(name)
    }

    pub fn declare_datatypes<N, S, D>(&mut self, sorts: S, decls: D) -> io::Result<()>
    where
        N: Into<String> + AsRef<str>,
        S: IntoIterator<Item = (N, i32)>,
        D: IntoIterator<Item = SExpr>,
    {
        let sorts = sorts
            .into_iter()
            .map(|(n, i)| self.list(vec![self.atom(n), self.numeral(i)]))
            .collect();
        let decls = decls.into_iter().collect();

        let solver = self
            .solver
            .as_mut()
            .expect("declare_datatype requires a running solver");
        solver.ack_command(
            &self.arena,
            self.atoms.success,
            self.arena.list(vec![
                self.atoms.declare_datatypes,
                self.arena.list(sorts),
                self.arena.list(decls),
            ]),
        )
    }

    /// Declares a new, uninterpreted function symbol.
    pub fn declare_fun<S: Into<String> + AsRef<str>>(
        &mut self,
        name: S,
        args: Vec<SExpr>,
        out: SExpr,
    ) -> io::Result<SExpr> {
        let name = self.atom(name);
        let solver = self
            .solver
            .as_mut()
            .expect("declare_fun requires a running solver");
        solver.ack_command(
            &self.arena,
            self.atoms.success,
            self.arena.list(vec![
                self.atoms.declare_fun,
                name,
                self.arena.list(args),
                out,
            ]),
        )?;
        Ok(name)
    }

    /// Defines a new function with a body.
    pub fn define_fun<S: Into<String> + AsRef<str>>(
        &mut self,
        name: S,
        args: Vec<(S, SExpr)>,
        out: SExpr,
        body: SExpr,
    ) -> io::Result<SExpr> {
        let name = self.atom(name);
        let args = args
            .into_iter()
            .map(|(n, s)| self.list(vec![self.atom(n), s]))
            .collect();
        let solver = self
            .solver
            .as_mut()
            .expect("define_fun requires a running solver");
        solver.ack_command(
            &self.arena,
            self.atoms.success,
            self.arena.list(vec![
                self.atoms.define_fun,
                name,
                self.arena.list(args),
                out,
                body,
            ]),
        )?;
        Ok(name)
    }

    /// Define a constant with a body with a value.
    /// This is a convenience wrapper over [Self::define_fun] since constants
    /// are nullary functions.
    pub fn define_const<S: Into<String> + AsRef<str>>(
        &mut self,
        name: S,
        out: SExpr,
        body: SExpr,
    ) -> io::Result<SExpr> {
        self.define_fun(name, vec![], out, body)
    }

    pub fn declare_sort<S: Into<String> + AsRef<str>>(
        &mut self,
        symbol: S,
        arity: i32,
    ) -> io::Result<SExpr> {
        let symbol = self.atom(symbol);
        let arity = self.numeral(arity);
        let solver = self
            .solver
            .as_mut()
            .expect("declare_sort requires a running solver");
        solver.ack_command(
            &self.arena,
            self.atoms.success,
            self.arena
                .list(vec![self.atoms.declare_sort, symbol, arity]),
        )?;
        Ok(symbol)
    }

    pub fn assert(&mut self, expr: SExpr) -> io::Result<()> {
        let solver = self
            .solver
            .as_mut()
            .expect("assert requires a running solver");
        solver.ack_command(
            &self.arena,
            self.atoms.success,
            self.arena.list(vec![self.atoms.assert, expr]),
        )
    }

    /// Get a model out from the solver. This is only meaningful after a `check-sat` query.
    pub fn get_model(&mut self) -> io::Result<SExpr> {
        let solver = self
            .solver
            .as_mut()
            .expect("get_model requires a running solver");
        solver.send(&self.arena, self.arena.list(vec![self.atoms.get_model]))?;
        solver.recv(&self.arena)
    }

    /// Get bindings for values in the model. This is only meaningful after a `check-sat` query.
    pub fn get_value(&mut self, vals: Vec<SExpr>) -> io::Result<Vec<(SExpr, SExpr)>> {
        if vals.is_empty() {
            return Ok(vec![]);
        }

        let solver = self
            .solver
            .as_mut()
            .expect("get_value requires a running solver");
        solver.send(
            &self.arena,
            self.arena
                .list(vec![self.atoms.get_value, self.arena.list(vals)]),
        )?;

        let resp = solver.recv(&self.arena)?;
        match self.arena.get(resp) {
            SExprData::List(pairs) => {
                let mut res = Vec::with_capacity(pairs.len());
                for expr in pairs {
                    match self.arena.get(*expr) {
                        SExprData::List(pair) => {
                            assert_eq!(2, pair.len());
                            res.push((pair[0], pair[1]));
                        }
                        _ => unreachable!(),
                    }
                }
                Ok(res)
            }

            _ => Err(io::Error::new(
                io::ErrorKind::Other,
                "Failed to parse solver output",
            )),
        }
    }

    /// Returns the names of the formulas involved in a contradiction.
    pub fn get_unsat_core(&mut self) -> io::Result<SExpr> {
        let solver = self
            .solver
            .as_mut()
            .expect("get_unsat_core requires a running solver");
        solver.send(
            &self.arena,
            self.arena.list(vec![self.atoms.get_unsat_core]),
        )?;
        solver.recv(&self.arena)
    }

    pub fn set_logic<L: Into<String> + AsRef<str>>(&mut self, logic: L) -> io::Result<()> {
        let solver = self
            .solver
            .as_mut()
            .expect("set_logic requires a running solver");
        solver.ack_command(
            &self.arena,
            self.atoms.success,
            self.arena
                .list(vec![self.atoms.set_logic, self.arena.atom(logic)]),
        )
    }

    /// Instruct the solver to exit.
    pub fn exit(&mut self) -> io::Result<()> {
        let solver = self
            .solver
            .as_mut()
            .expect("exit requires a running solver");
        solver.ack_command(
            &self.arena,
            self.atoms.success,
            self.arena.list(vec![self.atoms.exit]),
        )
    }

    /// Push a new context frame in the solver. Same as SMTLIB's `push` command.
    pub fn push(&mut self) -> io::Result<()> {
        let solver = self
            .solver
            .as_mut()
            .expect("push requires a running solver");
        solver.ack_command(
            &self.arena,
            self.atoms.success,
            self.arena.list(vec![self.atoms.push]),
        )
    }

    pub fn push_many(&mut self, n: usize) -> io::Result<()> {
        let solver = self
            .solver
            .as_mut()
            .expect("push_many requires a running solver");
        solver.ack_command(
            &self.arena,
            self.atoms.success,
            self.arena
                .list(vec![self.atoms.push, self.arena.atom(n.to_string())]),
        )
    }

    /// Pop a context frame in the solver. Same as SMTLIB's `pop` command.
    pub fn pop(&mut self) -> io::Result<()> {
        let solver = self.solver.as_mut().expect("pop requires a running solver");
        solver.ack_command(
            &self.arena,
            self.atoms.success,
            self.arena.list(vec![self.atoms.pop]),
        )
    }

    pub fn pop_many(&mut self, n: usize) -> io::Result<()> {
        let solver = self
            .solver
            .as_mut()
            .expect("pop_many requires a running solver");
        solver.ack_command(
            &self.arena,
            self.atoms.success,
            self.arena
                .list(vec![self.atoms.pop, self.arena.atom(n.to_string())]),
        )
    }

    /// Directly send an expression to the solver.
    ///
    /// You are responsible for reading the response, if any, from the solver by
    /// calling `context.raw_recv()` immediately after sending a message to the
    /// solver. Failing to call `context.raw_recv()` afterwards if the solver
    /// sends a response to your message, or calling it if the solver doesn't
    /// send a response, will lead to general breakage such as dead locks,
    /// nonsensical query results, and more.
    ///
    /// This is a low-level API and should be used sparingly, such as for
    /// solver-specific commands that this crate does not provide built-in
    /// support for. When possible, use the higher-level interfaces provided by
    /// this crate, for example by calling `context.assert(foo)` rather than
    /// `context.raw_send(context.list([context.atom("assert"), foo]))`.
    pub fn raw_send(&mut self, cmd: SExpr) -> io::Result<()> {
        let solver = self
            .solver
            .as_mut()
            .expect("send requires a running solver");
        solver.send(&self.arena, cmd)
    }

    /// Directly receive a response from the solver.
    ///
    /// This method should only be used immediately after calling
    /// `context.raw_send(...)`, to receive the solver's response to that sent
    /// message. Calling this method at other times, failing to call it when the
    /// solver sends a response, or calling it when the solver does not send a
    /// response, will lead to general breakage such as dead locks, nonsensical
    /// query results, and more.
    ///
    /// This is a low-level API and should be used sparingly, such as for
    /// solver-specific commands that this crate does not provide built-in
    /// support for. When possible, use the higher-level interfaces provided by
    /// this crate, for example by calling `context.assert(foo)` rather than
    /// `context.raw_send(context.list([context.atom("assert"), foo]))`.
    pub fn raw_recv(&mut self) -> io::Result<SExpr> {
        let solver = self
            .solver
            .as_mut()
            .expect("recv requires a running solver");
        solver.recv(&self.arena)
    }
}

/// # Basic S-Expression Construction and Inspection
///
/// These methods provide the foundation of building s-expressions. Even if you
/// end up using higher-level helper methods most of the time, everything
/// bottoms out in calls to these methods.
impl Context {
    /// Construct a non-list s-expression from the given string.
    pub fn atom(&self, name: impl Into<String> + AsRef<str>) -> SExpr {
        self.arena.atom(name)
    }

    /// Construct a list s-expression from the given elements.
    pub fn list(&self, list: Vec<SExpr>) -> SExpr {
        self.arena.list(list)
    }

    /// Create a numeral s-expression.
    pub fn numeral(&self, val: impl IntoNumeral) -> SExpr {
        self.arena.atom(val.to_string())
    }

    /// Create a decimal s-expression.
    pub fn decimal(&self, val: impl IntoDecimal) -> SExpr {
        self.arena.atom(val.to_string())
    }

    /// Create a binary s-expression of the given bit width.
    pub fn binary(&self, bit_width: usize, val: impl IntoBinary) -> SExpr {
        let val = format!("#b{val:0>bit_width$b}");
        self.arena.atom(val)
    }

    /// Get a `std::fmt::Display` representation of the given s-expression.
    ///
    /// This allows you to print, log, or otherwise format an s-expression
    /// creating within this context.
    ///
    /// You may only pass in `SExpr`s that were created by this
    /// `Context`. Failure to do so is safe, but may trigger a panic or return
    /// invalid data.
    pub fn display(&self, expr: SExpr) -> DisplayExpr {
        self.arena.display(expr)
    }

    /// Get the atom or list data for the given s-expression.
    ///
    /// This allows you to inspect s-expressions.
    ///
    /// You may only pass in `SExpr`s that were created by this
    /// `Context`. Failure to do so is safe, but may trigger a panic or return
    /// invalid data.
    pub fn get(&self, expr: SExpr) -> SExprData {
        self.arena.get(expr)
    }

    /// Get the atom data for the given s-expression.
    ///
    /// This allows you to inspect s-expressions. If the s-expression is not an
    /// atom this function returns `None`.
    ///
    /// You may only pass in `SExpr`s that were created by this
    /// `Context`. Failure to do so is safe, but may trigger a panic or return
    /// invalid data.
    pub fn get_atom(&self, expr: SExpr) -> Option<&str> {
        self.arena.get_atom(expr)
    }

    /// Get the string data for the given s-expression.
    ///
    /// This allows you to inspect s-expressions. If the s-expression is not an
    /// string this function returns `None`.
    ///
    /// You may only pass in `SExpr`s that were created by this
    /// `Context`. Failure to do so is safe, but may trigger a panic or return
    /// invalid data.
    pub fn get_str(&self, expr: SExpr) -> Option<&str> {
        self.arena.get_str(expr)
    }

    /// Get the list data for the given s-expression.
    ///
    /// This allows you to inspect s-expressions.If the s-expression is not an
    /// list this function returns `None`.
    ///
    /// You may only pass in `SExpr`s that were created by this
    /// `Context`. Failure to do so is safe, but may trigger a panic or return
    /// invalid data.
    pub fn get_list(&self, expr: SExpr) -> Option<&[SExpr]> {
        self.arena.get_list(expr)
    }

    /// Get the data for the given s-expression as an `u8`.
    ///
    /// This allows you to inspect s-expressions. If the s-expression is not an
    /// cannot be parsed into an `u8` this function returns `None`.
    ///
    /// You may only pass in `SExpr`s that were created by this
    /// `Context`. Failure to do so is safe, but may trigger a panic or return
    /// invalid data.
    pub fn get_u8(&self, expr: SExpr) -> Option<u8> {
        self.arena.get_i(expr)
    }

    /// Get the data for the given s-expression as an `u16`.
    ///
    /// This allows you to inspect s-expressions. If the s-expression is not an
    /// cannot be parsed into an `u16` this function returns `None`.
    ///
    /// You may only pass in `SExpr`s that were created by this
    /// `Context`. Failure to do so is safe, but may trigger a panic or return
    /// invalid data.
    pub fn get_u16(&self, expr: SExpr) -> Option<u16> {
        self.arena.get_i(expr)
    }

    /// Get the data for the given s-expression as an `u32`.
    ///
    /// This allows you to inspect s-expressions. If the s-expression is not an
    /// cannot be parsed into an `u32` this function returns `None`.
    ///
    /// You may only pass in `SExpr`s that were created by this
    /// `Context`. Failure to do so is safe, but may trigger a panic or return
    /// invalid data.
    pub fn get_u32(&self, expr: SExpr) -> Option<u32> {
        self.arena.get_i(expr)
    }

    /// Get the data for the given s-expression as an `u64`.
    ///
    /// This allows you to inspect s-expressions. If the s-expression is not an
    /// cannot be parsed into an `u64` this function returns `None`.
    ///
    /// You may only pass in `SExpr`s that were created by this
    /// `Context`. Failure to do so is safe, but may trigger a panic or return
    /// invalid data.
    pub fn get_u64(&self, expr: SExpr) -> Option<u64> {
        self.arena.get_i(expr)
    }

    /// Get the data for the given s-expression as an `u128`.
    ///
    /// This allows you to inspect s-expressions. If the s-expression is not an
    /// cannot be parsed into an `u128` this function returns `None`.
    ///
    /// You may only pass in `SExpr`s that were created by this
    /// `Context`. Failure to do so is safe, but may trigger a panic or return
    /// invalid data.
    pub fn get_u128(&self, expr: SExpr) -> Option<u128> {
        self.arena.get_i(expr)
    }

    /// Get the data for the given s-expression as an `usize`.
    ///
    /// This allows you to inspect s-expressions. If the s-expression is not an
    /// cannot be parsed into an `usize` this function returns `None`.
    ///
    /// You may only pass in `SExpr`s that were created by this
    /// `Context`. Failure to do so is safe, but may trigger a panic or return
    /// invalid data.
    pub fn get_usize(&self, expr: SExpr) -> Option<usize> {
        self.arena.get_i(expr)
    }

    /// Get the data for the given s-expression as an `i8`.
    ///
    /// This allows you to inspect s-expressions. If the s-expression is not an
    /// cannot be parsed into an `i8` this function returns `None`.
    ///
    /// You may only pass in `SExpr`s that were created by this
    /// `Context`. Failure to do so is safe, but may trigger a panic or return
    /// invalid data.
    pub fn get_i8(&self, expr: SExpr) -> Option<i8> {
        self.arena.get_i(expr)
    }

    /// Get the data for the given s-expression as an `i16`.
    ///
    /// This allows you to inspect s-expressions. If the s-expression is not an
    /// cannot be parsed into an `i16` this function returns `None`.
    ///
    /// You may only pass in `SExpr`s that were created by this
    /// `Context`. Failure to do so is safe, but may trigger a panic or return
    /// invalid data.
    pub fn get_i16(&self, expr: SExpr) -> Option<i16> {
        self.arena.get_i(expr)
    }

    /// Get the data for the given s-expression as an `i32`.
    ///
    /// This allows you to inspect s-expressions. If the s-expression is not an
    /// cannot be parsed into an `i32` this function returns `None`.
    ///
    /// You may only pass in `SExpr`s that were created by this
    /// `Context`. Failure to do so is safe, but may trigger a panic or return
    /// invalid data.
    pub fn get_i32(&self, expr: SExpr) -> Option<i32> {
        self.arena.get_i(expr)
    }

    /// Get the data for the given s-expression as an `i64`.
    ///
    /// This allows you to inspect s-expressions. If the s-expression is not an
    /// cannot be parsed into an `i64` this function returns `None`.
    ///
    /// You may only pass in `SExpr`s that were created by this
    /// `Context`. Failure to do so is safe, but may trigger a panic or return
    /// invalid data.
    pub fn get_i64(&self, expr: SExpr) -> Option<i64> {
        self.arena.get_i(expr)
    }

    /// Get the data for the given s-expression as an `i128`.
    ///
    /// This allows you to inspect s-expressions. If the s-expression is not an
    /// cannot be parsed into an `i128` this function returns `None`.
    ///
    /// You may only pass in `SExpr`s that were created by this
    /// `Context`. Failure to do so is safe, but may trigger a panic or return
    /// invalid data.
    pub fn get_i128(&self, expr: SExpr) -> Option<i128> {
        self.arena.get_i(expr)
    }

    /// Get the data for the given s-expression as an `isize`.
    ///
    /// This allows you to inspect s-expressions. If the s-expression is not an
    /// cannot be parsed into an `isize` this function returns `None`.
    ///
    /// You may only pass in `SExpr`s that were created by this
    /// `Context`. Failure to do so is safe, but may trigger a panic or return
    /// invalid data.
    pub fn get_isize(&self, expr: SExpr) -> Option<isize> {
        self.arena.get_i(expr)
    }

    /// Get the data for the given s-expression as a `f32`.
    ///
    /// This allows you to inspect s-expressions. If the s-expression is not an
    /// cannot be parsed into an `f32` this function returns `None`.
    ///
    /// You may only pass in `SExpr`s that were created by this
    /// `Context`. Failure to do so is safe, but may trigger a panic or return
    /// invalid data.
    pub fn get_f32(&self, expr: SExpr) -> Option<f32> {
        self.arena.get_f(expr)
    }

    /// Get the data for the given s-expression as a `f64`.
    ///
    /// This allows you to inspect s-expressions. If the s-expression is not an
    /// cannot be parsed into an `f64` this function returns `None`.
    /// You may only pass in `SExpr`s that were created by this
    /// `Context`. Failure to do so is safe, but may trigger a panic or return
    /// invalid data.
    pub fn get_f64(&self, expr: SExpr) -> Option<f64> {
        self.arena.get_f(expr)
    }

    /// Access "known" atoms.
    ///
    /// This lets you skip the is-it-already-interned-or-not checks and hash map
    /// lookups for certain frequently used atoms.
    pub fn atoms(&self) -> &KnownAtoms {
        &self.atoms
    }
}

/// # Generic and Polymorphic Helpers
///
/// Helpers for constructing s-expressions that are not specific to one sort.
impl Context {
    pub fn par<N, S, D>(&self, symbols: S, decls: D) -> SExpr
    where
        N: Into<String> + AsRef<str>,
        S: IntoIterator<Item = N>,
        D: IntoIterator<Item = SExpr>,
    {
        self.list(vec![
            self.atoms.par,
            self.list(symbols.into_iter().map(|n| self.atom(n)).collect()),
            self.list(decls.into_iter().collect()),
        ])
    }

    pub fn attr(&self, expr: SExpr, name: impl Into<String> + AsRef<str>, val: SExpr) -> SExpr {
        self.list(vec![self.atoms.bang, expr, self.atom(name), val])
    }

    pub fn named(&self, name: impl Into<String> + AsRef<str>, expr: SExpr) -> SExpr {
        self.attr(expr, ":named", self.atom(name))
    }

    /// A let-declaration with a single binding.
    pub fn let_<N: Into<String> + AsRef<str>>(&self, name: N, e: SExpr, body: SExpr) -> SExpr {
        self.list(vec![
            self.atoms.let_,
            self.list(vec![self.list(vec![self.atom(name), e])]),
            body,
        ])
    }

    /// A let-declaration of multiple bindings.
    pub fn let_many<N, I>(&self, bindings: I, body: SExpr) -> SExpr
    where
        I: IntoIterator<Item = (N, SExpr)>,
        N: Into<String> + AsRef<str>,
    {
        self.list(vec![
            self.atoms.let_,
            self.list(Vec::from_iter(
                bindings
                    .into_iter()
                    .map(|(n, v)| self.list(vec![self.atom(n), v])),
            )),
            body,
        ])
    }

    /// Universally quantify sorted variables in an expression.
    pub fn forall<N, I>(&self, vars: I, body: SExpr) -> SExpr
    where
        I: IntoIterator<Item = (N, SExpr)>,
        N: Into<String> + AsRef<str>,
    {
        let vars_iter = vars
            .into_iter()
            .map(|(n, s)| self.list(vec![self.atom(n), s]));
        self.list(vec![
            self.atoms.forall,
            self.list(vars_iter.collect()),
            body,
        ])
    }

    /// Existentially quantify sorted variables in an expression.
    pub fn exists<N, I>(&self, vars: I, body: SExpr) -> SExpr
    where
        I: IntoIterator<Item = (N, SExpr)>,
        N: Into<String> + AsRef<str>,
    {
        let vars_iter = vars
            .into_iter()
            .map(|(n, s)| self.list(vec![self.atom(n), s]));
        self.list(vec![
            self.atoms.exists,
            self.list(vars_iter.collect()),
            body,
        ])
    }

    /// Perform pattern matching on values of an algebraic data type.
    pub fn match_<I: IntoIterator<Item = (SExpr, SExpr)>>(&self, term: SExpr, arms: I) -> SExpr {
        let args: Vec<_> = std::iter::once(self.atoms.match_)
            .chain(std::iter::once(term))
            .chain(arms.into_iter().map(|(p, v)| self.list(vec![p, v])))
            .collect();
        assert!(args.len() >= 3);
        self.list(args)
    }

    /// Construct an if-then-else expression.
    pub fn ite(&self, c: SExpr, t: SExpr, e: SExpr) -> SExpr {
        self.list(vec![self.atoms.ite, c, t, e])
    }
}

/// # Bool Helpers
///
/// These methods help you construct s-expressions for various bool operations.
impl Context {
    /// The `Bool` sort.
    pub fn bool_sort(&self) -> SExpr {
        self.atoms.bool
    }

    /// The `true` constant.
    pub fn true_(&self) -> SExpr {
        self.atoms.t
    }

    /// The `false` constant.
    pub fn false_(&self) -> SExpr {
        self.atoms.f
    }

    unary!(not, not);
    right_assoc!(imp, imp_many, imp);
    left_assoc!(and, and_many, and);
    left_assoc!(or, or_many, or);
    left_assoc!(xor, xor_many, xor);
    chainable!(eq, eq_many, eq);
    pairwise!(distinct, distinct_many, distinct);
}

/// # Int Helpers
///
/// These methods help you construct s-expressions for various int operations.
impl Context {
    /// The `Int` sort.
    pub fn int_sort(&self) -> SExpr {
        self.atoms.int
    }

    unary!(negate, minus);
    left_assoc!(sub, sub_many, minus);
    left_assoc!(plus, plus_many, plus);
    left_assoc!(times, times_many, times);
    left_assoc!(div, div_many, div);
    left_assoc!(modulo, modulo_many, modulo);
    left_assoc!(rem, rem_many, rem);
    chainable!(lte, lte_many, lte);
    chainable!(lt, lt_many, lt);
    chainable!(gt, gt_many, gt);
    chainable!(gte, gte_many, gte);
}

/// # Real Helpers
///
/// These methods help you construct s-expressions for various real operations.
impl Context {
    /// The `Real` sort.
    pub fn real_sort(&self) -> SExpr {
        self.atoms.real
    }

    left_assoc!(rdiv, rdiv_many, slash);
    unary!(conv_to_real, to_real);
}

/// # Array Helpers
///
/// These methods help you construct s-expressions for various array operations.
impl Context {
    /// Construct the array sort with the given index and element types.
    pub fn array_sort(&self, index: SExpr, element: SExpr) -> SExpr {
        self.list(vec![self.atoms.array, index, element])
    }

    /// Select the element at the given index in the array.
    pub fn select(&self, ary: SExpr, index: SExpr) -> SExpr {
        self.list(vec![self.atoms.select, ary, index])
    }

    /// Store the value into the given index in the array, yielding a new array.
    pub fn store(&self, ary: SExpr, index: SExpr, value: SExpr) -> SExpr {
        self.list(vec![self.atoms.store, ary, index, value])
    }
}

/// # Bit Vector Helpers
///
/// These methods help you construct s-expressions for various bit vector
/// operations.
impl Context {
    /// Construct a BitVec sort with the given width.
    pub fn bit_vec_sort(&self, width: SExpr) -> SExpr {
        self.list(vec![self.atoms.und, self.atoms.bit_vec, width])
    }

    /// Concatenate two bit vectors.
    pub fn concat(&self, lhs: SExpr, rhs: SExpr) -> SExpr {
        self.list(vec![self.atoms.concat, lhs, rhs])
    }

    /// Extract a range from a bit vector.
    pub fn extract(&self, i: i32, j: i32, bv: SExpr) -> SExpr {
        self.list(vec![
            self.list(vec![
                self.atoms.und,
                self.atoms.extract,
                self.numeral(i),
                self.numeral(j),
            ]),
            bv,
        ])
    }

    unary!(bvnot, bvnot);
    left_assoc!(bvor, bvor_many, bvor);
    left_assoc!(bvand, bvand_many, bvand);
    left_assoc!(bvnand, bvnand_many, bvnand);
    left_assoc!(bvxor, bvxor_many, bvxor);
    left_assoc!(bvxnor, bvxnor_many, bvxnor);
    unary!(bvneg, bvneg);
    left_assoc!(bvadd, bvadd_many, bvadd);
    binop!(bvsub, bvsub);
    left_assoc!(bvmul, bvmul_many, bvmul);
    binop!(bvudiv, bvudiv);
    binop!(bvurem, bvurem);
    binop!(bvsdiv, bvsdiv);
    binop!(bvsrem, bvsrem);
    binop!(bvsmod, bvsmod);
    binop!(bvshl, bvshl);
    binop!(bvlshr, bvlshr);
    binop!(bvashr, bvashr);
    binop!(bvule, bvule);
    binop!(bvult, bvult);
    binop!(bvuge, bvuge);
    binop!(bvugt, bvugt);
    binop!(bvsle, bvsle);
    binop!(bvslt, bvslt);
    binop!(bvsge, bvsge);
    binop!(bvsgt, bvsgt);
    binop!(bvcomp, bvcomp);
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Response {
    Sat,
    Unsat,
    Unknown,
}

mod private {
    /// A trait implemented by types that can be used to create numerals.
    pub trait IntoNumeral: IntoNumeralSealed {}
    pub trait IntoNumeralSealed: std::fmt::Display {}

    /// A trait implemented by types that can be used to create binaries.
    pub trait IntoBinary: IntoBinarySealed {}
    pub trait IntoBinarySealed: std::fmt::Binary {}

    impl IntoNumeralSealed for i8 {}
    impl IntoNumeral for i8 {}
    impl IntoBinarySealed for i8 {}
    impl IntoBinary for i8 {}
    impl IntoNumeralSealed for i16 {}
    impl IntoNumeral for i16 {}
    impl IntoBinarySealed for i16 {}
    impl IntoBinary for i16 {}
    impl IntoNumeralSealed for i32 {}
    impl IntoNumeral for i32 {}
    impl IntoBinarySealed for i32 {}
    impl IntoBinary for i32 {}
    impl IntoNumeralSealed for i64 {}
    impl IntoNumeral for i64 {}
    impl IntoBinarySealed for i64 {}
    impl IntoBinary for i64 {}
    impl IntoNumeralSealed for i128 {}
    impl IntoNumeral for i128 {}
    impl IntoBinarySealed for i128 {}
    impl IntoBinary for i128 {}
    impl IntoNumeralSealed for isize {}
    impl IntoNumeral for isize {}
    impl IntoBinarySealed for isize {}
    impl IntoBinary for isize {}
    impl IntoNumeralSealed for u8 {}
    impl IntoNumeral for u8 {}
    impl IntoBinarySealed for u8 {}
    impl IntoBinary for u8 {}
    impl IntoNumeralSealed for u16 {}
    impl IntoNumeral for u16 {}
    impl IntoBinarySealed for u16 {}
    impl IntoBinary for u16 {}
    impl IntoNumeralSealed for u32 {}
    impl IntoNumeral for u32 {}
    impl IntoBinarySealed for u32 {}
    impl IntoBinary for u32 {}
    impl IntoNumeralSealed for u64 {}
    impl IntoNumeral for u64 {}
    impl IntoBinarySealed for u64 {}
    impl IntoBinary for u64 {}
    impl IntoNumeralSealed for u128 {}
    impl IntoNumeral for u128 {}
    impl IntoBinarySealed for u128 {}
    impl IntoBinary for u128 {}
    impl IntoNumeralSealed for usize {}
    impl IntoNumeral for usize {}
    impl IntoBinarySealed for usize {}
    impl IntoBinary for usize {}

    /// A trait implemented by types that can be used to create decimals.
    pub trait IntoDecimal: IntoDecimalSealed {}
    pub trait IntoDecimalSealed: std::fmt::Display {}

    impl IntoDecimal for f32 {}
    impl IntoDecimalSealed for f32 {}
    impl IntoDecimal for f64 {}
    impl IntoDecimalSealed for f64 {}
}
pub use private::{IntoBinary, IntoDecimal, IntoNumeral};

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! check_expr {
        ($ctx:expr, $expr:expr, $expected:expr) => {
            let actual = $ctx.display($expr).to_string();
            assert_eq!(actual, $expected);
        };
    }

    #[test]
    fn test_variadic_ops() {
        let ctx = ContextBuilder::new().build().unwrap();

        // As all variadic operators are generated by the `variadic!` macro above, we really only need
        // to pick one to test.
        check_expr!(ctx, ctx.imp_many([ctx.true_()]), "true");
        check_expr!(
            ctx,
            ctx.imp_many([ctx.true_(), ctx.false_()]),
            "(=> true false)"
        );
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic]
    fn sexpr_with_wrong_context() {
        let ctx1 = ContextBuilder::new().build().unwrap();
        let ctx2 = ContextBuilder::new().build().unwrap();

        let pizza1 = ctx1.atom("pizza");
        let _pizza2 = ctx2.atom("pizza");

        // This should trigger a panic in debug builds.
        let _ = ctx2.get(pizza1);
    }
}
