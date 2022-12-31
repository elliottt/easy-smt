use std::rc::Rc;

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct SExpr(Rc<SExprInner>);

impl SExpr {
    pub fn new(inner: SExprInner) -> Self {
        SExpr(Rc::new(inner))
    }

    pub fn list(args: Vec<SExpr>) -> SExpr {
        SExpr::new(SExprInner::List(args))
    }

    pub fn atom<S: AsRef<str>>(sym: S) -> SExpr {
        SExpr::new(SExprInner::Atom(String::from(sym.as_ref())))
    }

    fn binop<Op: AsRef<str>>(self, op: Op, rhs: SExpr) -> SExpr {
        SExpr::list(vec![SExpr::atom(op), self, rhs])
    }

    fn unary<Op: AsRef<str>>(self, op: Op) -> SExpr {
        SExpr::list(vec![SExpr::atom(op), self])
    }

    pub fn equal(self, rhs: SExpr) -> SExpr {
        self.binop("=", rhs)
    }

    pub fn not(self) -> SExpr {
        self.unary("not")
    }

    pub fn and<I: IntoIterator<Item = SExpr>>(items: I) -> SExpr {
        let mut parts = vec![SExpr::atom("and")];
        parts.extend(items);
        SExpr::list(parts)
    }

    pub fn lt(self, rhs: SExpr) -> SExpr {
        self.binop("<", rhs)
    }

    pub fn lte(self, rhs: SExpr) -> SExpr {
        self.binop("<=", rhs)
    }

    pub fn gt(self, rhs: SExpr) -> SExpr {
        self.binop(">", rhs)
    }

    pub fn gte(self, rhs: SExpr) -> SExpr {
        self.binop(">=", rhs)
    }

    pub fn named<N: AsRef<str>>(self, name: N) -> SExpr {
        SExpr::list(vec![
            SExpr::atom("!"),
            self,
            SExpr::atom(":named"),
            SExpr::atom(name),
        ])
    }
}

impl std::fmt::Display for SExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl AsRef<SExprInner> for SExpr {
    fn as_ref(&self) -> &SExprInner {
        self.0.as_ref()
    }
}

impl TryInto<u64> for SExpr {
    type Error = std::num::ParseIntError;

    fn try_into(self) -> Result<u64, Self::Error> {
        match self.as_ref() {
            SExprInner::Atom(str) => str.parse(),
            _ => todo!(),
        }
    }
}

impl From<usize> for SExpr {
    fn from(val: usize) -> Self {
        SExpr::atom(&format!("{}", val))
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum SExprInner {
    Atom(String),
    List(Vec<SExpr>),
}

impl std::fmt::Display for SExprInner {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            SExprInner::Atom(str) => write!(f, "{}", str),
            SExprInner::List(nodes) => {
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

impl SExprInner {}

pub(crate) struct Parser {
    context: Vec<Vec<SExpr>>,
}

impl Parser {
    pub(crate) fn new() -> Self {
        Self {
            context: Vec::new(),
        }
    }

    pub(crate) fn reset(&mut self) {
        self.context.clear();
    }

    fn atom(&mut self, sym: String) -> Option<SExpr> {
        let expr = SExpr::atom(sym);
        if let Some(outer) = self.context.last_mut() {
            outer.push(expr);
            None
        } else {
            Some(expr)
        }
    }

    fn app(&mut self) -> Option<SExpr> {
        if let Some(args) = self.context.pop() {
            let expr = SExpr::list(args);
            if let Some(outer) = self.context.last_mut() {
                outer.push(expr);
            } else {
                return Some(expr);
            }
        }
        None
    }

    pub(crate) fn parse(&mut self, bytes: &str) -> Option<SExpr> {
        let mut lexer = Lexer::new(bytes);
        while let Some(token) = lexer.next() {
            match token {
                Token::Symbol(sym) => {
                    let res = self.atom(sym);
                    if res.is_some() {
                        return res;
                    }
                }

                Token::LParen => self.context.push(Vec::new()),

                Token::RParen => {
                    let res = self.app();
                    if res.is_some() {
                        return res;
                    }
                }
            }
        }

        None
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
