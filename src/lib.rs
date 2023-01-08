use std::ffi;
use std::io::{self, BufRead};
use std::process;

mod sexpr;

use sexpr::Arena;
pub use sexpr::{DisplayExpr, SExpr, SExprData};

pub struct Context {
    solver: Option<Solver>,
    arena: Arena,
    known_atoms: Vec<SExpr>,
}

macro_rules! make_funs {

    ($idx:expr) => {};

    ($idx:expr, $fun:ident $(, $funs:ident)*) => {
        #[inline]
        fn $fun(&self) -> SExpr {
            self.known_atoms[$idx]
        }

        make_funs!($idx + 1usize $(, $funs)*);
    };
}

macro_rules! known_atoms {
    [$(($funs:ident, $atoms:literal)),* $(,)?] => {

        make_funs!(0, $($funs),*);

        fn init_known_atoms(arena: &Arena) -> Vec<SExpr> {
            let mut atoms = Vec::new();

            $(
                atoms.push(arena.atom($atoms));
            )*

            atoms
        }
    }
}

macro_rules! variadic {
    ($name:ident, $op:ident) => {
        pub fn $name<I: IntoIterator<Item = SExpr>>(&self, items: I) -> SExpr {
            let mut args = vec![self.$op()];
            args.extend(items);
            assert!(args.len() >= 3);
            self.list(args)
        }
    };
}

macro_rules! unary {
    ($name:ident, $op:ident) => {
        pub fn $name(&self, val: SExpr) -> SExpr {
            self.list(vec![self.$op(), val])
        }
    };
}

macro_rules! binop {
    ($name:ident, $op:ident) => {
        pub fn $name(&self, lhs: SExpr, rhs: SExpr) -> SExpr {
            self.list(vec![self.$op(), lhs, rhs])
        }
    };
}

macro_rules! right_assoc {
    ($name:ident, $many:ident, $op:ident) => {
        binop!($name, $op);
        variadic!($many, $op);
    }
}

macro_rules! left_assoc {
    ($name:ident, $many:ident, $op:ident) => {
        binop!($name, $op);
        variadic!($many, $op);
    }
}

macro_rules! chainable {
    ($name:ident, $many:ident, $op:ident) => {
        binop!($name, $op);
        variadic!($many, $op);
    }
}

macro_rules! pairwise {
    ($name:ident, $many:ident, $op:ident) => {
        binop!($name, $op);
        variadic!($many, $op);
    }
}

impl Context {
    pub fn new<P, A>(program: P, args: A) -> io::Result<Self>
    where
        P: AsRef<ffi::OsStr>,
        A: IntoIterator,
        A::Item: AsRef<ffi::OsStr>,
    {
        let arena = Arena::new();
        let known_atoms = Self::init_known_atoms(&arena);
        let solver = Solver::new(program, args)?;

        let mut ctx = Context {
            solver: Some(solver),
            arena,
            known_atoms,
        };

        ctx.set_option(":print-success", ctx.true_())?;
        ctx.set_option(":produce-models", ctx.true_())?;

        Ok(ctx)
    }

    known_atoms![
        (declare_fun_, "declare-fun"),
        (bool_, "Bool"),
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
    ];

    pub fn without_solver() -> Self {
        let arena = Arena::new();
        let known_atoms = Self::init_known_atoms(&arena);
        Context {
            solver: None,
            arena,
            known_atoms,
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
        solver.set_option(&self.arena, name, value)
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
        let cmd = self.arena.list(vec![self.arena.atom("check-sat")]);
        solver.send(&self.arena, cmd)?;
        let resp = solver.recv(&mut self.arena)?;
        if resp == self.arena.atom("sat") {
            Ok(Response::Sat)
        } else if resp == self.arena.atom("unsat") {
            Ok(Response::Unsat)
        } else if resp == self.arena.atom("unknown") {
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
        let name = self.arena.atom(name);
        let expr = self
            .arena
            .list(vec![self.declare_fun_(), name, self.arena.list(args), body]);
        let solver = self
            .solver
            .as_mut()
            .expect("ack_command requires a running solver");
        solver.ack_command(&mut self.arena, expr)?;
        Ok(name)
    }

    pub fn assert(&mut self, expr: SExpr) -> io::Result<()> {
        let cmd = self.arena.list(vec![self.arena.atom("assert"), expr]);
        let solver = self
            .solver
            .as_mut()
            .expect("ack_command requires a running solver");
        solver.ack_command(&mut self.arena, cmd)
    }

    pub fn get_value(&mut self, vals: Vec<SExpr>) -> io::Result<Vec<(SExpr, SExpr)>> {
        let cmd = self
            .arena
            .list(vec![self.arena.atom("get-value"), self.arena.list(vals)]);

        let solver = self
            .solver
            .as_mut()
            .expect("ack_command requires a running solver");
        solver.send(&self.arena, cmd)?;

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
        let cmd = self.arena.list(vec![self.arena.atom("get-unsat-core")]);
        let solver = self
            .solver
            .as_mut()
            .expect("ack_command requires a running solver");
        solver.send(&self.arena, cmd)?;
        solver.recv(&mut self.arena)
    }

    pub fn set_logic<L: Into<String> + AsRef<str>>(&mut self, logic: L) -> io::Result<()> {
        let solver = self
            .solver
            .as_mut()
            .expect("ack_command requires a running solver");
        solver.ack_command(
            &self.arena,
            self.arena
                .list(vec![self.arena.atom("set-logic"), self.arena.atom(logic)]),
        )
    }

    pub fn push(&mut self) -> io::Result<()> {
        let solver = self
            .solver
            .as_mut()
            .expect("ack_command requires a running solver");
        solver.ack_command(&self.arena, self.arena.list(vec![self.arena.atom("push")]))
    }

    pub fn push_many(&mut self, n: usize) -> io::Result<()> {
        let solver = self
            .solver
            .as_mut()
            .expect("ack_command requires a running solver");
        solver.ack_command(
            &self.arena,
            self.arena.list(vec![
                self.arena.atom("push"),
                self.arena.atom(n.to_string()),
            ]),
        )
    }

    pub fn pop(&mut self) -> io::Result<()> {
        let solver = self
            .solver
            .as_mut()
            .expect("ack_command requires a running solver");
        solver.ack_command(&self.arena, self.arena.list(vec![self.arena.atom("pop")]))
    }

    pub fn pop_many(&mut self, n: usize) -> io::Result<()> {
        let solver = self
            .solver
            .as_mut()
            .expect("ack_command requires a running solver");
        solver.ack_command(
            &self.arena,
            self.arena
                .list(vec![self.arena.atom("pop"), self.arena.atom(n.to_string())]),
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
        self.list(vec![self.atom("!"), expr, self.atom(name), val])
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

    /// The `Bool` sort.
    pub fn bool_sort(&self) -> SExpr {
        self.bool_()
    }

    /// The `true` constant.
    pub fn true_(&self) -> SExpr {
        self.t_()
    }

    /// The `false` constant.
    pub fn false_(&self) -> SExpr {
        self.f_()
    }

    unary!(not, not_);
    right_assoc!(imp, imp_many, imp_);
    left_assoc!(and, and_many, and_);
    left_assoc!(or, or_many, or_);
    left_assoc!(xor, xor_many, xor_);
    chainable!(eq, eq_many, eq_);
    pairwise!(distinct, distinct_many, distinct_);
    binop!(ite, ite_);

    /// The `Int` sort.
    pub fn int_sort(&self) -> SExpr {
        self.int_()
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
        self.list(vec![self.array_(), index, element])
    }

    /// Select the element at the given index in the array.
    pub fn select(&self, ary: SExpr, index: SExpr) -> SExpr {
        self.list(vec![self.select_(), ary, index])
    }

    /// Store the value into the given index in the array, yielding a new array.
    pub fn store(&self, ary: SExpr, index: SExpr, value: SExpr) -> SExpr {
        self.list(vec![self.store_(), ary, index, value])
    }
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

    pub fn set_option<K>(&mut self, arena: &Arena, name: K, value: SExpr) -> io::Result<()>
    where
        K: Into<String> + AsRef<str>,
    {
        self.ack_command(
            arena,
            arena.list(vec![arena.atom("set-option"), arena.atom(name), value]),
        )
    }

    fn ack_command(&mut self, arena: &Arena, c: SExpr) -> io::Result<()> {
        self.send(arena, c)?;
        let resp = self.recv(arena)?;
        if resp == arena.atom("success") {
            Ok(())
        } else {
            Err(io::Error::new(
                io::ErrorKind::Other,
                format!("Unexpected result from solver: {}", arena.display(resp)),
            ))
        }
    }
}
