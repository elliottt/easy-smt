use std::ffi;
use std::io::{self, BufRead};
use std::process;

mod sexpr;

use sexpr::Arena;
pub use sexpr::{DisplayExpr, SExpr, SExprData};

pub struct Context {
    solver: Option<Solver>,
    arena: Arena,
}

impl Context {
    pub fn new<P, A>(program: P, args: A) -> io::Result<Self>
    where
        P: AsRef<ffi::OsStr>,
        A: IntoIterator,
        A::Item: AsRef<ffi::OsStr>,
    {
        let arena = Arena::new();
        Ok(Context {
            solver: Some(Solver::new(&arena, program, args)?),
            arena,
        })
    }

    pub fn without_solver() -> Self {
        Context {
            solver: None,
            arena: Arena::new(),
        }
    }

    pub fn set_option<K, V>(&mut self, name: K, value: V) -> io::Result<()>
    where
        K: Into<String> + AsRef<str>,
        V: Into<String> + AsRef<str>,
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
        let expr = self.arena.list(vec![
            self.arena.atom("declare-fun"),
            name,
            self.arena.list(args),
            body,
        ]);
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

    pub fn and<I: IntoIterator<Item = SExpr>>(&self, items: I) -> SExpr {
        let mut args = vec![self.atom("and")];
        args.extend(items);
        self.list(args)
    }

    pub fn i32(&self, val: i32) -> SExpr {
        self.arena.atom(val.to_string())
    }

    pub fn not(&self, val: SExpr) -> SExpr {
        self.arena.list(vec![self.atom("not"), val])
    }

    pub fn eq(&self, lhs: SExpr, rhs: SExpr) -> SExpr {
        self.arena.list(vec![self.arena.atom("="), lhs, rhs])
    }

    pub fn gt(&self, lhs: SExpr, rhs: SExpr) -> SExpr {
        self.arena.list(vec![self.arena.atom(">"), lhs, rhs])
    }

    pub fn lte(&self, lhs: SExpr, rhs: SExpr) -> SExpr {
        self.arena.list(vec![self.arena.atom("<="), lhs, rhs])
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
    pub fn new<P, A>(arena: &Arena, program: P, args: A) -> io::Result<Self>
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

        let mut solver = Self {
            _handle: handle,
            stdin,
            stdout: io::BufReader::new(stdout).lines(),
            parser: sexpr::Parser::new(),
        };

        solver.set_option(arena, ":print-success", "true")?;
        solver.set_option(arena, ":produce-models", "true")?;

        Ok(solver)
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

    pub fn set_option<K, V>(&mut self, arena: &Arena, name: K, value: V) -> io::Result<()>
    where
        K: Into<String> + AsRef<str>,
        V: Into<String> + AsRef<str>,
    {
        self.ack_command(
            arena,
            arena.list(vec![
                arena.atom("set-option"),
                arena.atom(name),
                arena.atom(value),
            ]),
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
