use std::ffi;
use std::io::{self, BufRead};
use std::process;

mod sexpr;

pub use sexpr::{Arena, SExpr};

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
        Ok(Context {
            solver: Some(Solver::new(program, args)?),
            arena: Arena::new(),
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
        let cmd = self.arena.list(vec![
            self.arena.atom("set-option"),
            self.arena.atom(name),
            self.arena.atom(value),
        ]);
        self.ack_command(cmd)
    }

    fn ack_command(&mut self, c: SExpr) -> io::Result<()> {
        let solver = self
            .solver
            .as_mut()
            .expect("ack_command requires a running solver");
        solver.send(&self.arena, c)?;
        let resp = solver.recv(&mut self.arena)?;
        if resp == self.arena.atom("success") {
            Ok(())
        } else {
            Err(io::Error::new(
                io::ErrorKind::Other,
                format!("Unexpected result from solver: {:?}", resp),
            ))
        }
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
                format!("Unexpected result from solver: {:?}", resp),
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
        self.ack_command(expr)?;
        Ok(name)
    }

    pub fn assert(&mut self, expr: SExpr) -> io::Result<()> {
        let cmd = self.arena.list(vec![self.arena.atom("assert"), expr]);
        self.ack_command(cmd)
    }

    pub fn get_value(&mut self, vals: Vec<SExpr>) -> io::Result<Vec<(SExpr, SExpr)>> {
        let cmd = self.arena.list
        self.send(SExpr::list(vec![
            SExpr::atom("get-value"),
            SExpr::list(vals),
        ]))?;

        let resp = self.recv()?;
        match resp.as_ref() {
            SExprInner::List(pairs) => {
                let mut res = Vec::with_capacity(pairs.len());
                for expr in pairs {
                    match expr.as_ref() {
                        SExprInner::List(pair) => {
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
        self.send(SExpr::list(vec![SExpr::atom("get-unsat-core")]))?;
        self.recv()
    }

    pub fn set_logic<L: AsRef<str>>(&mut self, logic: L) -> io::Result<()> {
        self.ack_command(SExpr::list(vec![
            SExpr::atom("set-logic"),
            SExpr::atom(logic),
        ]))
    }

    pub fn push(&mut self) -> io::Result<()> {
        self.ack_command(SExpr::list(vec![SExpr::atom("push")]))
    }

    pub fn push_many(&mut self, n: usize) -> io::Result<()> {
        self.ack_command(SExpr::list(vec![SExpr::atom("push"), SExpr::from(n)]))
    }

    pub fn pop(&mut self) -> io::Result<()> {
        self.ack_command(SExpr::list(vec![SExpr::atom("pop")]))
    }

    pub fn pop_many(&mut self, n: usize) -> io::Result<()> {
        self.ack_command(SExpr::list(vec![SExpr::atom("pop"), SExpr::from(n)]))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Response {
    Sat,
    Unsat,
    Unknown,
}

pub struct Solver {
    _handle: process::Child,
    stdin: process::ChildStdin,
    stdout: io::Lines<io::BufReader<process::ChildStdout>>,
    // parser: sexpr::Parser,
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

        let mut solver = Self {
            _handle: handle,
            stdin,
            stdout: io::BufReader::new(stdout).lines(),
            // parser: sexpr::Parser::new(),
        };

        solver.set_option(":print-success", "true")?;
        solver.set_option(":produce-models", "true")?;

        Ok(solver)
    }

    fn send(&mut self, arena: &Arena, expr: SExpr) -> io::Result<()> {
        use io::Write;
        write!(self.stdin, "{}\n", arena.display(expr))
    }

    fn recv(&mut self, arena: &mut Arena) -> io::Result<SExpr> {
        todo!()
        // self.parser.reset();
        //
        // while let Some(line) = self.stdout.next() {
        //     if let Some(res) = self.parser.parse(&line?) {
        //         return Ok(res);
        //     }
        // }
        //
        // Err(std::io::Error::new(
        //     std::io::ErrorKind::Other,
        //     "Failed to parse solver output",
        // ))
    }
}
