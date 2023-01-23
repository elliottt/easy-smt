use crate::{
    known_atoms::KnownAtoms,
    sexpr::{Arena, DisplayExpr, SExpr, SExprData},
    solver::Solver,
};
use std::{ffi, io};

macro_rules! variadic {
    ($name:ident, $op:ident) => {
        pub fn $name<I: IntoIterator<Item = SExpr>>(&self, items: I) -> SExpr {
            let args: Vec<_> = std::iter::once(self.atoms.$op).chain(items).collect();
            assert!(args.len() >= 3);
            self.list(args)
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
    solver_program_and_args: Option<(ffi::OsString, Vec<ffi::OsString>)>,
    replay_file: Option<Box<dyn io::Write>>,
}

impl<'a> ContextBuilder {
    /// Construct a new builder with the default configuration.
    pub fn new() -> Self {
        Self::default()
    }

    /// Configure the solver that will be used.
    ///
    /// By default, no solver is configured, and any `Context` created will only
    /// be able to build and display expressions, not assert them or query for
    /// their satisfiability.
    pub fn solver<P, A>(&mut self, program: P, args: A) -> &mut Self
    where
        P: Into<ffi::OsString>,
        A: IntoIterator,
        A::Item: Into<ffi::OsString>,
    {
        self.solver_program_and_args =
            Some((program.into(), args.into_iter().map(|a| a.into()).collect()));
        self
    }

    /// Clear the solver configuration, if any.
    ///
    /// This returns to the default, no-solver configuration, where any
    /// `Context` created will only be able to build and display expressions,
    /// not assert them or query for their satisfiability.
    pub fn without_solver(&mut self) -> &mut Self {
        self.solver_program_and_args = None;
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
        W: 'static + io::Write,
    {
        self.replay_file = replay_file.map(|w| Box::new(w) as _);
        self
    }

    /// Finish configuring the context and build it.
    pub fn build(&mut self) -> io::Result<Context> {
        let arena = Arena::new();
        let atoms = KnownAtoms::new(&arena);

        let solver = if let Some((program, args)) = self.solver_program_and_args.take() {
            Some(Solver::new(
                program,
                args,
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

impl Context {
    /// Access "known" atoms.
    ///
    /// This lets you skip the is-it-already-interned-or-not checks and hash map
    /// lookups for certain frequently used atoms.
    pub fn atoms(&self) -> &KnownAtoms {
        &self.atoms
    }

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

    pub fn check(&mut self) -> io::Result<Response> {
        let solver = self
            .solver
            .as_mut()
            .expect("check requires a running solver");
        solver.send(&self.arena, self.arena.list(vec![self.atoms.check_sat]))?;
        let resp = solver.recv(&mut self.arena)?;
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
            .map(|(n, i)| self.list(vec![self.atom(n), self.i32(i)]))
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

    pub fn declare<S: Into<String> + AsRef<str>>(
        &mut self,
        name: S,
        body: SExpr,
    ) -> io::Result<SExpr> {
        self.declare_fun(name, vec![], body)
    }

    pub fn declare_fun<S: Into<String> + AsRef<str>>(
        &mut self,
        name: S,
        args: Vec<SExpr>,
        body: SExpr,
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
                body,
            ]),
        )?;
        Ok(name)
    }

    pub fn declare_sort<S: Into<String> + AsRef<str>>(
        &mut self,
        symbol: S,
        arity: i32,
    ) -> io::Result<SExpr> {
        let symbol = self.atom(symbol);
        let arity = self.i32(arity);
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

    pub fn get_model(&mut self) -> io::Result<SExpr> {
        let solver = self
            .solver
            .as_mut()
            .expect("get_model requires a running solver");
        solver.send(&self.arena, self.arena.list(vec![self.atoms.get_model]))?;
        solver.recv(&self.arena)
    }

    pub fn get_value(&mut self, vals: Vec<SExpr>) -> io::Result<Vec<(SExpr, SExpr)>> {
        let solver = self
            .solver
            .as_mut()
            .expect("get_value requires a running solver");
        solver.send(
            &self.arena,
            self.arena
                .list(vec![self.atoms.get_value, self.arena.list(vals)]),
        )?;

        let resp = solver.recv(&mut self.arena)?;
        match self.arena.get(resp) {
            SExprData::List(pairs) => {
                let mut res = Vec::with_capacity(pairs.len());
                for expr in pairs {
                    match self.arena.get(*expr) {
                        SExprData::List(pair) => {
                            assert_eq!(2, pair.len());
                            res.push((pair[0].clone(), pair[1].clone()));
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
        solver.recv(&mut self.arena)
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

    pub fn display(&self, expr: SExpr) -> DisplayExpr {
        self.arena.display(expr)
    }

    pub fn atom(&self, name: impl Into<String> + AsRef<str>) -> SExpr {
        self.arena.atom(name)
    }

    pub fn list(&self, list: Vec<SExpr>) -> SExpr {
        self.arena.list(list)
    }

    pub fn get(&self, expr: SExpr) -> SExprData {
        self.arena.get(expr)
    }

    pub fn attr(&self, expr: SExpr, name: impl Into<String> + AsRef<str>, val: SExpr) -> SExpr {
        self.list(vec![self.atoms.bang, expr, self.atom(name), val])
    }

    pub fn named(&self, name: impl Into<String> + AsRef<str>, expr: SExpr) -> SExpr {
        self.attr(expr, ":named", self.atom(name))
    }

    pub fn i32(&self, val: i32) -> SExpr {
        self.arena.atom(val.to_string())
    }

    pub fn i64(&self, val: i64) -> SExpr {
        self.arena.atom(val.to_string())
    }

    /// A let-declaration with a single binding.
    pub fn let_<N: Into<String> + AsRef<str>>(&self, name: N, e: SExpr, body: SExpr) -> SExpr {
        self.list(vec![
            self.atoms.let_,
            self.list(vec![self.atom(name), e]),
            body,
        ])
    }

    /// A let-declaration of multiple bindings.
    pub fn let_many<N, I>(&self, bindings: I, body: SExpr) -> SExpr
    where
        I: IntoIterator<Item = (N, SExpr)>,
        N: Into<String> + AsRef<str>,
    {
        let args: Vec<_> = std::iter::once(self.atoms.let_)
            .chain(
                bindings
                    .into_iter()
                    .map(|(n, v)| self.list(vec![self.atom(n), v])),
            )
            .chain(std::iter::once(body))
            .collect();
        assert!(args.len() >= 3);
        self.list(args)
    }

    /// Universally quantify sorted variables in an expression.
    pub fn forall<N, I>(&self, vars: I, body: SExpr) -> SExpr
    where
        I: IntoIterator<Item = (N, SExpr)>,
        N: Into<String> + AsRef<str>,
    {
        let args: Vec<_> = std::iter::once(self.atoms.forall)
            .chain(
                vars.into_iter()
                    .map(|(n, s)| self.list(vec![self.atom(n), s])),
            )
            .chain(std::iter::once(body))
            .collect();
        assert!(args.len() >= 3);
        self.list(args)
    }

    /// Existentially quantify sorted variables in an expression.
    pub fn exists<N, I>(&self, vars: I, body: SExpr) -> SExpr
    where
        I: IntoIterator<Item = (N, SExpr)>,
        N: Into<String> + AsRef<str>,
    {
        let args: Vec<_> = std::iter::once(self.atoms.exists)
            .chain(
                vars.into_iter()
                    .map(|(n, s)| self.list(vec![self.atom(n), s])),
            )
            .chain(std::iter::once(body))
            .collect();
        assert!(args.len() >= 3);
        self.list(args)
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

    /// Construct an if-then-else expression.
    pub fn ite(&self, c: SExpr, t: SExpr, e: SExpr) -> SExpr {
        self.list(vec![self.atoms.ite, c, t, e])
    }

    /// The `Int` sort.
    pub fn int_sort(&self) -> SExpr {
        self.atoms.int
    }

    unary!(negate, minus);
    left_assoc!(sub, sub_many, minus);
    left_assoc!(plus, plus_many, plus);
    left_assoc!(times, times_many, times);
    chainable!(lte, lte_many, lte);
    chainable!(lt, lt_many, lt);
    chainable!(gt, gt_many, gt);
    chainable!(gte, gte_many, gte);

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
                self.i32(i),
                self.i32(j),
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
    binop!(bvsrem, bvsrem);
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
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Response {
    Sat,
    Unsat,
    Unknown,
}
