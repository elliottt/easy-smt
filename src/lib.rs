use std::ffi;
use std::io::{self, BufRead};
use std::process;

mod sexpr;

pub use sexpr::SExpr;

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

        let mut solver = Self {
            _handle: handle,
            stdin,
            stdout: io::BufReader::new(stdout).lines(),
            parser: sexpr::Parser::new(),
        };

        solver.set_option(":print-success", "true")?;
        solver.set_option(":produce-models", "true")?;

        Ok(solver)
    }

    fn send(&mut self, expr: SExpr) -> io::Result<()> {
        use io::Write;
        write!(self.stdin, "{}\n", expr)
    }

    fn recv(&mut self) -> io::Result<SExpr> {
        self.parser.reset();

        while let Some(line) = self.stdout.next() {
            if let Some(res) = self.parser.parse(&line?) {
                return Ok(res)
            }
        }

        Err(std::io::Error::new(
            std::io::ErrorKind::Other,
            "Failed to parse solver output",
        ))
    }

    pub fn set_option<K, V>(&mut self, name: K, value: V) -> io::Result<()>
    where
        K: AsRef<str>,
        V: AsRef<str>,
    {
        self.ack_command(SExpr::list(vec![
            SExpr::atom("set-option"),
            SExpr::atom(name),
            SExpr::atom(value),
        ]))
    }

    fn ack_command(&mut self, c: SExpr) -> io::Result<()> {
        self.send(c)?;
        let resp = self.recv()?;
        match resp {
            SExpr::Atom(sym) if sym == "success" => Ok(()),
            _ => Err(io::Error::new(
                io::ErrorKind::Other,
                format!("Unexpected result from solver: {:?}", resp),
            )),
        }
    }

    pub fn declare<S: AsRef<str>>(&mut self, name: S, body: SExpr) -> io::Result<SExpr> {
        self.declare_fun(name, vec![], body)
    }

    pub fn check(&mut self) -> io::Result<Response> {
        self.send(SExpr::list(vec![SExpr::atom("check-sat")]))?;
        let resp = self.recv()?;
        match resp {
            SExpr::Atom(atom) => match atom.as_ref() {
                "sat" => return Ok(Response::Sat),
                "unsat" => return Ok(Response::Unsat),
                "unknown" => return Ok(Response::Unknown),
                _ => unreachable!(),
            },

            _ => unreachable!(),
        }
    }

    pub fn declare_fun<S: AsRef<str>>(
        &mut self,
        name: S,
        args: Vec<SExpr>,
        body: SExpr,
    ) -> io::Result<SExpr> {
        let name = SExpr::atom(name);
        let expr = SExpr::App(vec![
            SExpr::atom("declare-fun"),
            name.clone(),
            SExpr::list(args),
            body,
        ]);
        self.ack_command(expr)?;
        Ok(name)
    }

    pub fn assert(&mut self, expr: SExpr) -> io::Result<()> {
        self.ack_command(SExpr::list(vec![SExpr::atom("assert"), expr]))
    }

    pub fn get_value(&mut self, vals: Vec<SExpr>) -> io::Result<Vec<(SExpr, SExpr)>> {
        self.send(SExpr::list(vec![
            SExpr::atom("get-value"),
            SExpr::list(vals),
        ]))?;

        let resp = self.recv()?;
        match resp {
            SExpr::App(pairs) => {
                let mut res = Vec::with_capacity(pairs.len());
                for expr in pairs {
                    match expr {
                        SExpr::App(mut pair) => {
                            assert_eq!(2, pair.len());
                            let val = pair.pop().unwrap();
                            let key = pair.pop().unwrap();
                            res.push((key, val));
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

impl TryInto<u64> for SExpr {
    type Error = std::num::ParseIntError;

    fn try_into(self) -> Result<u64, Self::Error> {
        match self {
            SExpr::Atom(str) => str.parse(),
            _ => todo!(),
        }
    }
}

impl From<usize> for SExpr {
    fn from(val: usize) -> SExpr {
        SExpr::Atom(format!("{}", val))
    }
}
