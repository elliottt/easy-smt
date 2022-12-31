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

    fn atom<S: AsRef<str>>(&mut self, sym: S) -> Option<SExpr> {
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
enum Token<'a> {
    LParen,
    RParen,
    Symbol(&'a str),
}

struct Lexer<'a> {
    chars: &'a str,
    indices: std::iter::Peekable<std::str::CharIndices<'a>>,
}

impl<'a> Lexer<'a> {
    fn new(chars: &'a str) -> Self {
        Self {
            chars,
            indices: chars.char_indices().peekable(),
        }
    }

    fn scan_symbol(&mut self, start: usize) -> &'a str {
        let mut end;
        loop {
            if let Some((ix, c)) = self.indices.peek() {
                end = *ix;
                if c.is_alphabetic() || c.is_numeric() || "~!@$%^&*_-+=<>.?/".contains(*c) {
                    self.indices.next();
                    continue;
                }
            } else {
                end = self.chars.len();
            }

            break;
        }

        &self.chars[start..end]
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Token<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some((start, c)) = self.indices.next() {
            match c {
                '(' => {
                    return Some(Token::LParen);
                }

                ')' => {
                    return Some(Token::RParen);
                }

                // this is a bit of a hack, but if we encounter a comment we clear out the indices
                // iterator as the parser is line oriented.
                ';' => self.indices = self.chars[0..0].char_indices().peekable(),

                c if c.is_whitespace() => {}

                _ => return Some(Token::Symbol(self.scan_symbol(start))),
            }
        }

        None
    }
}
