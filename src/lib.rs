use std::ffi;
use std::io::{self, BufRead};
use std::process;

mod sexpr;

use sexpr::Arena;
pub use sexpr::{DisplayExpr, SExpr, SExprData};

macro_rules! make_funs {

    ($idx:expr) => {};

    ($idx:expr, $fun:ident $(, $funs:ident)*) => {
        #[inline]
        fn $fun(&self) -> SExpr {
            self.atoms[$idx]
        }

        make_funs!($idx + 1usize $(, $funs)*);
    };
}

macro_rules! known_atoms {
    [$(($funs:ident, $atoms:literal)),* $(,)?] => {
        struct KnownAtoms {
            atoms: Vec<SExpr>,
        }

        impl KnownAtoms {

            make_funs!(0, $($funs),*);

            fn new(arena: &Arena) -> KnownAtoms {
                let mut atoms = Vec::new();

                $(
                    atoms.push(arena.atom($atoms));
                )*

                KnownAtoms{ atoms }
            }

        }
    }
}

known_atoms![
    (check_sat_, "check-sat"),
    (unsat_, "unsat"),
    (sat_, "sat"),
    (unknown_, "unknown"),
    (declare_fun_, "declare-fun"),
    (assert_, "assert"),
    (get_model_, "get-model"),
    (get_value_, "get-value"),
    (get_unsat_core_, "get-unsat-core"),
    (set_logic_, "set-logic"),
    (set_option_, "set-option"),
    (push_, "push"),
    (pop_, "pop"),
    (bool_, "Bool"),
    (bang_, "!"),
    (success_, "success"),
    (t_, "true"),
    (f_, "false"),
    (not_, "not"),
    (imp_, "=>"),
    (and_, "and"),
    (or_, "or"),
    (xor_, "xor"),
    (eq_, "="),
    (distinct_, "distinct"),
    (ite_, "ite"),
    (int_, "Int"),
    (minus_, "-"),
    (plus_, "+"),
    (times_, "*"),
    (lte_, "<="),
    (lt_, "<"),
    (gte_, ">="),
    (gt_, ">"),
    (array_, "Array"),
    (select_, "select"),
    (store_, "store"),
    (let_name_, "let"),
    (forall_, "forall"),
    (exists_, "exists"),
    (match_name_, "match"),
    (und_, "_"),
    (bit_vec_, "BitVec"),
    (concat_, "concat"),
    (extract_, "extract"),
    (bvnot_, "bvnot"),
    (bvor_, "bvor"),
    (bvand_, "bvand"),
    (bvnand_, "bvnand"),
    (bvxor_, "bvxor"),
    (bvxnor_, "bvxnor"),
    (bvneg_, "bvneg"),
    (bvadd_, "bvadd"),
    (bvsub_, "bvsub"),
    (bvmul_, "bvmul"),
    (bvudiv_, "bvudiv"),
    (bvurem_, "bvurem"),
    (bvsrem_, "bvsrem"),
    (bvshl_, "bvshl"),
    (bvlshr_, "bvlshr"),
    (bvashr_, "bvashr"),
    (bvule_, "bvule"),
    (bvult_, "bvult"),
    (bvuge_, "bvuge"),
    (bvugt_, "bvugt"),
    (bvsle_, "bvsle"),
    (bvslt_, "bvslt"),
    (bvsge_, "bvsge"),
    (bvsgt_, "bvsgt"),
];

macro_rules! variadic {
    ($name:ident, $op:ident) => {
        pub fn $name<I: IntoIterator<Item = SExpr>>(&self, items: I) -> SExpr {
            let args: Vec<_> = std::iter::once(self.atoms.$op()).chain(items).collect();
            assert!(args.len() >= 3);
            self.list(args)
        }
    };
}

macro_rules! unary {
    ($name:ident, $op:ident) => {
        pub fn $name(&self, val: SExpr) -> SExpr {
            self.list(vec![self.atoms.$op(), val])
        }
    };
}

macro_rules! binop {
    ($name:ident, $op:ident) => {
        pub fn $name(&self, lhs: SExpr, rhs: SExpr) -> SExpr {
            self.list(vec![self.atoms.$op(), lhs, rhs])
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

pub struct Context {
    solver: Option<Solver>,
    arena: Arena,
    atoms: KnownAtoms,
}

impl Context {
    pub fn new<P, A>(program: P, args: A) -> io::Result<Self>
    where
        P: AsRef<ffi::OsStr>,
        A: IntoIterator,
        A::Item: AsRef<ffi::OsStr>,
    {
        let arena = Arena::new();
        let atoms = KnownAtoms::new(&arena);
        let solver = Solver::new(program, args)?;

        let mut ctx = Context {
            solver: Some(solver),
            arena,
            atoms,
        };

        ctx.set_option(":print-success", ctx.true_())?;
        ctx.set_option(":produce-models", ctx.true_())?;

        Ok(ctx)
    }

    pub fn without_solver() -> Self {
        let arena = Arena::new();
        let atoms = KnownAtoms::new(&arena);
        Context {
            solver: None,
            arena,
            atoms,
        }
    }

    pub fn set_option<K>(&mut self, name: K, value: SExpr) -> io::Result<()>
    where
        K: Into<String> + AsRef<str>,
    {
        let solver = self
            .solver
            .as_mut()
            .expect("ack_command requires a running solver");
        solver.ack_command(
            &self.arena,
            self.atoms.success_(),
            self.arena.list(vec![self.atoms.set_option_(), self.arena.atom(name), value]),
        )
    }

    pub fn declare<S: Into<String> + AsRef<str>>(
        &mut self,
        name: S,
        body: SExpr,
    ) -> io::Result<SExpr> {
        self.declare_fun(name, vec![], body)
    }

    pub fn check(&mut self) -> io::Result<Response> {
        let solver = self
            .solver
            .as_mut()
            .expect("ack_command requires a running solver");
        solver.send(&self.arena, self.arena.list(vec![self.atoms.check_sat_()]))?;
        let resp = solver.recv(&mut self.arena)?;
        if resp == self.atoms.sat_() {
            Ok(Response::Sat)
        } else if resp == self.atoms.unsat_() {
            Ok(Response::Unsat)
        } else if resp == self.atoms.unknown_() {
            Ok(Response::Unknown)
        } else {
            Err(io::Error::new(
                io::ErrorKind::Other,
                format!("Unexpected result from solver: {}", self.display(resp)),
            ))
        }
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
            .expect("ack_command requires a running solver");
        solver.ack_command(
            &self.arena,
            self.atoms.success_(),
            self.arena.list(vec![
                self.atoms.declare_fun_(),
                name,
                self.arena.list(args),
                body,
            ]),
        )?;
        Ok(name)
    }

    pub fn assert(&mut self, expr: SExpr) -> io::Result<()> {
        let solver = self
            .solver
            .as_mut()
            .expect("ack_command requires a running solver");
        solver.ack_command(
            &self.arena,
            self.atoms.success_(),
            self.arena.list(vec![self.atoms.assert_(), expr]),
        )
    }

    pub fn get_model(&mut self) -> io::Result<SExpr> {
        let solver = self
            .solver
            .as_mut()
            .expect("ack_command requires a running solver");
        solver.send(&self.arena, self.arena.list(vec![self.atoms.get_model_()]))?;
        solver.recv(&self.arena)
    }

    pub fn get_value(&mut self, vals: Vec<SExpr>) -> io::Result<Vec<(SExpr, SExpr)>> {
        let solver = self
            .solver
            .as_mut()
            .expect("ack_command requires a running solver");
        solver.send(
            &self.arena,
            self.arena.list(vec![self.atoms.get_value_(), self.arena.list(vals)]),
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

            _ => Err(std::io::Error::new(
                std::io::ErrorKind::Other,
                "Failed to parse solver output",
            )),
        }
    }

    /// Returns the names of the formulas involved in a contradiction.
    pub fn get_unsat_core(&mut self) -> io::Result<SExpr> {
        let solver = self
            .solver
            .as_mut()
            .expect("ack_command requires a running solver");
        solver.send(&self.arena, self.arena.list(vec![self.atoms.get_unsat_core_()]))?;
        solver.recv(&mut self.arena)
    }

    pub fn set_logic<L: Into<String> + AsRef<str>>(&mut self, logic: L) -> io::Result<()> {
        let solver = self
            .solver
            .as_mut()
            .expect("ack_command requires a running solver");
        solver.ack_command(
            &self.arena,
            self.atoms.success_(),
            self.arena.list(vec![self.atoms.set_logic_(), self.arena.atom(logic)]),
        )
    }

    pub fn push(&mut self) -> io::Result<()> {
        let solver = self
            .solver
            .as_mut()
            .expect("ack_command requires a running solver");
        solver.ack_command(
            &self.arena,
            self.atoms.success_(),
            self.arena.list(vec![self.atoms.push_()]),
        )
    }

    pub fn push_many(&mut self, n: usize) -> io::Result<()> {
        let solver = self
            .solver
            .as_mut()
            .expect("ack_command requires a running solver");
        solver.ack_command(
            &self.arena,
            self.atoms.success_(),
            self.arena.list(vec![self.atoms.push_(), self.arena.atom(n.to_string())]),
        )
    }

    pub fn pop(&mut self) -> io::Result<()> {
        let solver = self
            .solver
            .as_mut()
            .expect("ack_command requires a running solver");
        solver.ack_command(
            &self.arena,
            self.atoms.success_(),
            self.arena.list(vec![self.atoms.pop_()]),
        )
    }

    pub fn pop_many(&mut self, n: usize) -> io::Result<()> {
        let solver = self
            .solver
            .as_mut()
            .expect("ack_command requires a running solver");
        solver.ack_command(
            &self.arena,
            self.atoms.success_(),
            self.arena.list(vec![self.atoms.pop_(), self.arena.atom(n.to_string())]),
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
        self.list(vec![self.atoms.bang_(), expr, self.atom(name), val])
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
            self.atoms.let_name_(),
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
        let args: Vec<_> = std::iter::once(self.atoms.let_name_())
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
        let args: Vec<_> = std::iter::once(self.atoms.forall_())
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
        let args: Vec<_> = std::iter::once(self.atoms.exists_())
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
        let args: Vec<_> = std::iter::once(self.atoms.match_name_())
            .chain(std::iter::once(term))
            .chain(arms.into_iter().map(|(p, v)| self.list(vec![p, v])))
            .collect();
        assert!(args.len() >= 3);
        self.list(args)
    }

    /// The `Bool` sort.
    pub fn bool_sort(&self) -> SExpr {
        self.atoms.bool_()
    }

    /// The `true` constant.
    pub fn true_(&self) -> SExpr {
        self.atoms.t_()
    }

    /// The `false` constant.
    pub fn false_(&self) -> SExpr {
        self.atoms.f_()
    }

    unary!(not, not_);
    right_assoc!(imp, imp_many, imp_);
    left_assoc!(and, and_many, and_);
    left_assoc!(or, or_many, or_);
    left_assoc!(xor, xor_many, xor_);
    chainable!(eq, eq_many, eq_);
    pairwise!(distinct, distinct_many, distinct_);

    /// Construct an if-then-else expression.
    pub fn ite(&self, c: SExpr, t: SExpr, e: SExpr) -> SExpr {
        self.list(vec![self.atoms.ite_(), c, t, e])
    }

    /// The `Int` sort.
    pub fn int_sort(&self) -> SExpr {
        self.atoms.int_()
    }

    unary!(negate, minus_);
    left_assoc!(sub, sub_many, minus_);
    left_assoc!(plus, plus_many, plus_);
    left_assoc!(times, times_many, times_);
    chainable!(lte, lte_many, lte_);
    chainable!(lt, lt_many, lt_);
    chainable!(gt, gt_many, gt_);
    chainable!(gte, gte_many, gte_);

    /// Construct the array sort with the given index and element types.
    pub fn array_sort(&self, index: SExpr, element: SExpr) -> SExpr {
        self.list(vec![self.atoms.array_(), index, element])
    }

    /// Select the element at the given index in the array.
    pub fn select(&self, ary: SExpr, index: SExpr) -> SExpr {
        self.list(vec![self.atoms.select_(), ary, index])
    }

    /// Store the value into the given index in the array, yielding a new array.
    pub fn store(&self, ary: SExpr, index: SExpr, value: SExpr) -> SExpr {
        self.list(vec![self.atoms.store_(), ary, index, value])
    }

    /// Construct a BitVec sort with the given width.
    pub fn bit_vec_sort(&self, width: SExpr) -> SExpr {
        self.list(vec![self.atoms.und_(), self.atoms.bit_vec_(), width])
    }

    /// Concatenate two bit vectors.
    pub fn concat(&self, lhs: SExpr, rhs: SExpr) -> SExpr {
        self.list(vec![self.atoms.concat_(), lhs, rhs])
    }

    /// Extract a range from a bit vector.
    pub fn extract(&self, i: i32, j: i32, bv: SExpr) -> SExpr {
        self.list(vec![
            self.list(vec![
                self.atoms.und_(),
                self.atoms.extract_(),
                self.i32(i),
                self.i32(j),
            ]),
            bv,
        ])
    }

    unary!(bvnot, bvnot_);
    left_assoc!(bvor, bvor_many, bvor_);
    left_assoc!(bvand, bvand_many, bvand_);
    left_assoc!(bvnand, bvnand_many, bvnand_);
    left_assoc!(bvxor, bvxor_many, bvxor_);
    left_assoc!(bvxnor, bvxnor_many, bvxnor_);
    unary!(bvneg, bvneg_);
    left_assoc!(bvadd, bvadd_many, bvadd_);
    binop!(bvsub, bvsub_);
    left_assoc!(bvmul, bvmul_many, bvmul_);
    binop!(bvudiv, bvudiv_);
    binop!(bvurem, bvurem_);
    binop!(bvsrem, bvsrem_);
    binop!(bvshl, bvshl_);
    binop!(bvlshr, bvlshr_);
    binop!(bvashr, bvashr_);
    binop!(bvule, bvule_);
    binop!(bvult, bvult_);
    binop!(bvuge, bvuge_);
    binop!(bvugt, bvugt_);
    binop!(bvsle, bvsle_);
    binop!(bvslt, bvslt_);
    binop!(bvsge, bvsge_);
    binop!(bvsgt, bvsgt_);
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Response {
    Sat,
    Unsat,
    Unknown,
}

pub(crate) struct Solver {
    _handle: process::Child,
    stdin: process::ChildStdin,
    stdout: io::Lines<io::BufReader<process::ChildStdout>>,
    parser: sexpr::Parser,
}

impl Solver {
    pub fn new<P, A>(program: P, args: A) -> io::Result<Self>
    where
        P: AsRef<ffi::OsStr>,
        A: IntoIterator,
        A::Item: AsRef<ffi::OsStr>,
    {
        let mut handle = process::Command::new(program)
            .args(args)
            .stdin(process::Stdio::piped())
            .stdout(process::Stdio::piped())
            .spawn()?;
        let stdin = handle.stdin.take().unwrap();
        let stdout = handle.stdout.take().unwrap();

        Ok(Self {
            _handle: handle,
            stdin,
            stdout: io::BufReader::new(stdout).lines(),
            parser: sexpr::Parser::new(),
        })
    }

    fn send(&mut self, arena: &Arena, expr: SExpr) -> io::Result<()> {
        use io::Write;
        write!(self.stdin, "{}\n", arena.display(expr))
    }

    fn recv(&mut self, arena: &Arena) -> io::Result<SExpr> {
        self.parser.reset();

        while let Some(line) = self.stdout.next() {
            if let Some(res) = self.parser.parse(arena, &line?) {
                return Ok(res);
            }
        }

        Err(std::io::Error::new(
            std::io::ErrorKind::Other,
            "Failed to parse solver output",
        ))
    }

    fn ack_command(&mut self, arena: &Arena, success: SExpr, c: SExpr) -> io::Result<()> {
        self.send(arena, c)?;
        let resp = self.recv(arena)?;
        if resp == success {
            Ok(())
        } else {
            Err(io::Error::new(
                io::ErrorKind::Other,
                format!("Unexpected result from solver: {}", arena.display(resp)),
            ))
        }
    }
}
