use std::ffi;
use std::io::{self, BufRead};
use std::process;

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
    context: Vec<Vec<SExpr>>,
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
            context: Vec::new(),
        };

        solver.set_option(":print-success", "true")?;
        solver.set_option(":produce-models", "true")?;

        Ok(solver)
    }

    fn send(&mut self, expr: SExpr) -> io::Result<()> {
        use io::Write;
        write!(self.stdin, "{}\n", expr)
    }

    fn atom(&mut self, sym: String) -> Option<SExpr> {
        let expr = SExpr::Atom(sym);
        if let Some(outer) = self.context.last_mut() {
            outer.push(expr);
            None
        } else {
            Some(expr)
        }
    }

    fn app(&mut self) -> Option<SExpr> {
        if let Some(args) = self.context.pop() {
            let expr = SExpr::App(args);
            if let Some(outer) = self.context.last_mut() {
                outer.push(expr);
            } else {
                return Some(expr);
            }
        }
        None
    }

    fn recv(&mut self) -> io::Result<SExpr> {
        self.context.clear();

        while let Some(line) = self.stdout.next() {
            let line = line?;

            for token in Lexer::new(&line) {
                match token {
                    Token::Symbol(sym) => {
                        if let Some(res) = self.atom(sym) {
                            return Ok(res);
                        }
                    }

                    Token::LParen => self.context.push(Vec::new()),

                    Token::RParen => {
                        if let Some(res) = self.app() {
                            return Ok(res);
                        }
                    }
                }
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

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum SExpr {
    Atom(String),
    App(Vec<SExpr>),
}

impl std::fmt::Display for SExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            SExpr::Atom(str) => write!(f, "{}", str),
            SExpr::App(nodes) => {
                write!(f, "(")?;
                let mut sep = "";
                for node in nodes.into_iter() {
                    write!(f, "{}", sep)?;
                    node.fmt(f)?;
                    sep = " ";
                }
                write!(f, ")")
            }
        }
    }
}

impl SExpr {
    pub fn list(args: Vec<Self>) -> Self {
        SExpr::App(args)
    }

    pub fn atom<S: AsRef<str>>(sym: S) -> Self {
        SExpr::Atom(String::from(sym.as_ref()))
    }

    pub fn binop<Op: AsRef<str>>(op: Op, lhs: Self, rhs: Self) -> Self {
        SExpr::list(vec![Self::atom(op), lhs, rhs])
    }

    pub fn unary<Op: AsRef<str>>(op: Op, body: Self) -> Self {
        SExpr::list(vec![Self::atom(op), body])
    }

    pub fn equal(self, other: Self) -> Self {
        Self::binop("=", self, other)
    }

    pub fn not(other: Self) -> Self {
        Self::unary("not", other)
    }

    pub fn and<I: IntoIterator<Item = Self>>(items: I) -> Self {
        let mut parts = vec![SExpr::atom("and")];
        parts.extend(items);
        SExpr::list(parts)
    }

    pub fn lt(self, other: Self) -> Self {
        Self::binop("<", self, other)
    }

    pub fn lte(self, other: Self) -> Self {
        Self::binop("<=", self, other)
    }

    pub fn gt(self, other: Self) -> Self {
        Self::binop(">", self, other)
    }

    pub fn gte(self, other: Self) -> Self {
        Self::binop(">=", self, other)
    }

    pub fn named<N: AsRef<str>>(self, name: N) -> Self {
        Self::list(vec![Self::atom("!"), self, Self::atom(":named"), Self::atom(name)])
    }
}

#[derive(Debug)]
enum Token {
    LParen,
    RParen,
    Symbol(String),
}

struct Lexer<'a> {
    chars: std::iter::Peekable<std::str::Chars<'a>>,
}

impl<'a> Lexer<'a> {
    fn new(bytes: &'a str) -> Self {
        Self {
            chars: bytes.chars().peekable(),
        }
    }

    fn scan_eol(&mut self) {
        while let Some(c) = self.chars.next() {
            if c == '\n' {
                break;
            }
        }
    }

    fn scan_symbol(&mut self, c: char) -> String {
        let mut buf = String::from(c);

        while let Some(c) = self.chars.peek() {
            if c.is_alphabetic() || c.is_numeric() || "~!@$%^&*_-+=<>.?/".contains(*c) {
                buf.push(*c);
                self.chars.next();
            } else {
                break;
            }
        }

        buf
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(c) = self.chars.next() {
            match c {
                '(' => {
                    return Some(Token::LParen);
                }

                ')' => {
                    return Some(Token::RParen);
                }

                ';' => self.scan_eol(),

                c if c.is_whitespace() => {}

                c => return Some(Token::Symbol(self.scan_symbol(c))),
            }
        }

        None
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
