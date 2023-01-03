use std::collections::HashMap;
use std::rc::Rc;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SExpr {
    /// TODO: explain the bit layout here
    index: u32,
}

impl SExpr {
    pub fn is_atom(&self) -> bool {
        self.index & (1 << 31) == 0
    }

    fn atom(ix: u32) -> Self {
        assert!(ix < u32::MAX);
        SExpr { index: ix }
    }

    fn list(ix: u32) -> Self {
        assert!(ix < u32::MAX);
        SExpr {
            index: ix | (1 << 31),
        }
    }
}

#[derive(Default)]
pub struct Arena {
    /// Interned strings.
    atoms: Vec<String>,

    /// Backwards lookup for string data.
    atom_map: HashMap<&'static str, SExpr>,

    /// Interned lists.
    lists: Vec<Vec<SExpr>>,

    /// Backwards lookup for interned lists.
    list_map: HashMap<&'static [SExpr], SExpr>,
}

impl Arena {
    pub fn new() -> Self {
        Self {
            atoms: Vec::new(),
            atom_map: HashMap::new(),
            lists: Vec::new(),
            list_map: HashMap::new(),
        }
    }

    pub fn atom(&mut self, name: impl Into<String> + AsRef<str>) -> SExpr {
        if let Some(sexpr) = self.atom_map.get(name.as_ref()) {
            *sexpr
        } else {
            let ix = self.atoms.len();
            let sexpr = SExpr::atom(ix as u32);

            let name: String = name.into();

            // Safety argument: the name will live as long as the context as it is inserted into
            // the vector below and never removed or resized.
            let name_ref: &'static str = unsafe { std::mem::transmute(name.as_str()) };
            self.atom_map.insert(name_ref, sexpr);
            self.atoms.push(name);

            sexpr
        }
    }

    pub fn list(&mut self, list: Vec<SExpr>) -> SExpr {
        if let Some(sexpr) = self.list_map.get(&list.as_slice()) {
            *sexpr
        } else {
            let ix = self.lists.len();
            let sexpr = SExpr::list(ix as u32);

            // Safety argument: the name will live as long as the context as it is inserted into
            // the vector below and never removed or resized.
            let list_ref: &'static [SExpr] = unsafe { std::mem::transmute(list.as_slice()) };
            self.list_map.insert(list_ref, sexpr);
            self.lists.push(list);

            sexpr
        }
    }

    pub fn display(&self, sexpr: SExpr) -> Display {
        Display {
            context: self,
            sexpr,
        }
    }
}

pub struct Display<'a> {
    context: &'a Arena,
    sexpr: SExpr,
}

impl<'a> std::fmt::Display for Display<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        todo!();
    }
}

/*

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
*/
