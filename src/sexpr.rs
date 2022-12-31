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
        Self::list(vec![
            Self::atom("!"),
            self,
            Self::atom(":named"),
            Self::atom(name),
        ])
    }
}

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
