use std::{cell::RefCell, collections::HashMap};

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct SExpr(u32);

impl SExpr {
    pub fn is_atom(&self) -> bool {
        self.0 & (1 << 31) == 0
    }

    fn atom(ix: u32) -> Self {
        assert!(ix < u32::MAX);
        SExpr(ix)
    }

    fn list(ix: u32) -> Self {
        assert!(ix < u32::MAX);
        SExpr(ix | (1 << 31))
    }

    fn index(&self) -> usize {
        (self.0 & !(1 << 31)) as usize
    }
}

impl std::fmt::Debug for SExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple(if self.is_atom() {
            "SExpr::Atom"
        } else {
            "SExpr::List"
        })
        .field(&self.index())
        .finish()
    }
}

#[derive(Default)]
struct ArenaInner {
    /// Interned strings.
    atoms: Vec<String>,

    /// Backwards lookup for string data.
    atom_map: HashMap<&'static str, SExpr>,

    /// Interned lists.
    lists: Vec<Vec<SExpr>>,

    /// Backwards lookup for interned lists.
    list_map: HashMap<&'static [SExpr], SExpr>,
}

pub(crate) struct Arena(RefCell<ArenaInner>);

impl Arena {
    pub fn new() -> Self {
        Self(RefCell::new(ArenaInner {
            atoms: Vec::new(),
            atom_map: HashMap::new(),
            lists: Vec::new(),
            list_map: HashMap::new(),
        }))
    }

    pub fn atom(&self, name: impl Into<String> + AsRef<str>) -> SExpr {
        let mut inner = self.0.borrow_mut();
        if let Some(sexpr) = inner.atom_map.get(name.as_ref()) {
            *sexpr
        } else {
            let ix = inner.atoms.len();
            let sexpr = SExpr::atom(ix as u32);

            let name: String = name.into();

            // Safety argument: the name will live as long as the context as it is inserted into
            // the vector below and never removed or resized.
            let name_ref: &'static str = unsafe { std::mem::transmute(name.as_str()) };
            inner.atom_map.insert(name_ref, sexpr);
            inner.atoms.push(name);

            sexpr
        }
    }

    pub fn list(&self, list: Vec<SExpr>) -> SExpr {
        let mut inner = self.0.borrow_mut();
        if let Some(sexpr) = inner.list_map.get(&list.as_slice()) {
            *sexpr
        } else {
            let ix = inner.lists.len();
            let sexpr = SExpr::list(ix as u32);

            // Safety argument: the name will live as long as the context as it is inserted into
            // the vector below and never removed or resized.
            let list_ref: &'static [SExpr] = unsafe { std::mem::transmute(list.as_slice()) };
            inner.list_map.insert(list_ref, sexpr);
            inner.lists.push(list);

            sexpr
        }
    }

    pub fn display(&self, sexpr: SExpr) -> DisplayExpr {
        DisplayExpr { arena: self, sexpr }
    }

    pub fn get(&self, expr: SExpr) -> SExprData<'_> {
        let inner = self.0.borrow();
        if expr.is_atom() {
            // Safety argument: the data will live as long as the containing context, and is
            // immutable once it's inserted, so using the lifteime of the Arena is acceptable.
            let data = unsafe { std::mem::transmute(inner.atoms[expr.index()].as_str()) };
            SExprData::Atom(data)
        } else {
            // Safety argument: the data will live as long as the containing context, and is
            // immutable once it's inserted, so using the lifteime of the Arena is acceptable.
            let data = unsafe { std::mem::transmute(inner.lists[expr.index()].as_slice()) };
            SExprData::List(data)
        }
    }
}

pub enum SExprData<'a> {
    Atom(&'a str),
    List(&'a [SExpr]),
}

pub struct DisplayExpr<'a> {
    arena: &'a Arena,
    sexpr: SExpr,
}

impl<'a> std::fmt::Display for DisplayExpr<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        return fmt_sexpr(f, self.arena, self.sexpr);

        fn fmt_sexpr(f: &mut std::fmt::Formatter, arena: &Arena, sexpr: SExpr) -> std::fmt::Result {
            match arena.get(sexpr) {
                SExprData::Atom(data) => std::fmt::Display::fmt(data, f),
                SExprData::List(data) => {
                    write!(f, "(")?;
                    let mut sep = "";
                    for s in data {
                        std::fmt::Display::fmt(sep, f)?;
                        fmt_sexpr(f, arena, *s)?;
                        sep = " ";
                    }
                    write!(f, ")")
                }
            }
        }
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

    fn atom(&mut self, arena: &Arena, sym: &str) -> Option<SExpr> {
        let expr = arena.atom(sym);
        if let Some(outer) = self.context.last_mut() {
            outer.push(expr);
            None
        } else {
            Some(expr)
        }
    }

    fn app(&mut self, arena: &Arena) -> Option<SExpr> {
        if let Some(args) = self.context.pop() {
            let expr = arena.list(args);
            if let Some(outer) = self.context.last_mut() {
                outer.push(expr);
            } else {
                return Some(expr);
            }
        }
        None
    }

    pub(crate) fn parse(&mut self, arena: &Arena, bytes: &str) -> Option<SExpr> {
        let mut lexer = Lexer::new(bytes);
        while let Some(token) = lexer.next() {
            match token {
                Token::Symbol(sym) => {
                    let res = self.atom(arena, sym);
                    if res.is_some() {
                        return res;
                    }
                }

                Token::LParen => self.context.push(Vec::new()),

                Token::RParen => {
                    let res = self.app(arena);
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
