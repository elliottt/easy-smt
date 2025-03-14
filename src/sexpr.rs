use std::{cell::RefCell, collections::HashMap};

#[cfg(debug_assertions)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct ArenaId(u32);

#[cfg(not(debug_assertions))]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct ArenaId;

impl ArenaId {
    fn new() -> ArenaId {
        #[cfg(debug_assertions)]
        {
            use std::sync::atomic::{AtomicU32, Ordering};
            static ARENA_ID_COUNTER: AtomicU32 = AtomicU32::new(0);
            let id = ARENA_ID_COUNTER.fetch_add(1, Ordering::SeqCst);
            ArenaId(id)
        }
        #[cfg(not(debug_assertions))]
        {
            ArenaId
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct SExpr {
    // The index of this `SExpr`'s data within `ArenaInner::atoms` or
    // `ArenaInner::lists`. The top two bits are reserved to tag this as either
    // an atom, a list, or a string literal.
    index: u32,

    // The ID of the arena that this `SExpr` is associated with. Used for debug
    // assertions.
    arena_id: ArenaId,
}

impl SExpr {
    const TAG_MASK: u32 = 0b11 << 30;

    const TAG_ATOM: u32 = 0b00;
    const TAG_LIST: u32 = 0b01;
    const TAG_STRING: u32 = 0b10;

    fn tag(&self) -> u32 {
        self.index >> 30
    }

    /// Is this `SExpr` an atom?
    pub fn is_atom(&self) -> bool {
        self.tag() == Self::TAG_ATOM
    }

    /// Is this `SExpr` a list?
    pub fn is_list(&self) -> bool {
        self.tag() == Self::TAG_LIST
    }

    /// Is this `SExpr` a string literal?
    pub fn is_string(&self) -> bool {
        self.tag() == Self::TAG_STRING
    }

    fn atom(index: u32, arena_id: ArenaId) -> Self {
        assert_eq!(index & Self::TAG_MASK, 0);
        SExpr { index, arena_id }
    }

    fn list(index: u32, arena_id: ArenaId) -> Self {
        assert_eq!(index & Self::TAG_MASK, 0);
        let index = index | (Self::TAG_LIST << 30);
        SExpr { index, arena_id }
    }

    fn string(index: u32, arena_id: ArenaId) -> Self {
        assert_eq!(index & Self::TAG_MASK, 0);
        let index = index | (Self::TAG_STRING << 30);
        SExpr { index, arena_id }
    }

    fn index(&self) -> usize {
        (self.index & !Self::TAG_MASK) as usize
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

struct ArenaInner {
    /// The ID of this Arena. Used for debug asserts that any given `SExpr`
    /// belongs to this arena.
    id: ArenaId,

    /// Interned strings.
    strings: Vec<String>,

    /// Backwards lookup for interned strings.
    string_map: HashMap<&'static str, u32>,

    /// Interned lists.
    lists: Vec<Vec<SExpr>>,

    /// Backwards lookup for interned lists.
    list_map: HashMap<&'static [SExpr], SExpr>,
}

impl ArenaInner {
    pub fn intern_string(&mut self, s: impl Into<String>) -> u32 {
        let ix = self.strings.len() as u32;

        let s: String = s.into();

        // Safety argument: the name will live as long as the context as it is inserted into
        // the vector below and never removed or resized.
        let s_ref: &'static str = unsafe { std::mem::transmute(s.as_str()) };
        self.strings.push(s);
        self.string_map.insert(s_ref, ix);

        ix
    }
}

pub(crate) struct Arena(RefCell<ArenaInner>);

impl Arena {
    pub fn new() -> Self {
        Self(RefCell::new(ArenaInner {
            id: ArenaId::new(),
            strings: Vec::new(),
            string_map: HashMap::new(),
            lists: Vec::new(),
            list_map: HashMap::new(),
        }))
    }

    pub fn atom(&self, name: impl Into<String> + AsRef<str>) -> SExpr {
        let mut inner = self.0.borrow_mut();
        let ix = if let Some(ix) = inner.string_map.get(name.as_ref()) {
            *ix
        } else {
            inner.intern_string(name)
        };
        SExpr::atom(ix as u32, inner.id)
    }

    fn string(&self, s: &str) -> SExpr {
        let mut inner = self.0.borrow_mut();
        let ix = if let Some(ix) = inner.string_map.get(s) {
            *ix
        } else {
            inner.intern_string(s)
        };
        SExpr::string(ix, inner.id)
    }

    pub fn list(&self, list: Vec<SExpr>) -> SExpr {
        let mut inner = self.0.borrow_mut();
        if let Some(sexpr) = inner.list_map.get(&list.as_slice()) {
            *sexpr
        } else {
            let ix = inner.lists.len();
            let sexpr = SExpr::list(ix as u32, inner.id);

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

        debug_assert_eq!(
            inner.id, expr.arena_id,
            "Use of an `SExpr` with the wrong `Context`! An `SExpr` may only be \
             used with the `Context` from which it was created!"
        );

        if expr.is_atom() {
            // Safety argument: the data will live as long as the containing context, and is
            // immutable once it's inserted, so using the lifetime of the Arena is acceptable.
            let data = unsafe { std::mem::transmute(inner.strings[expr.index()].as_str()) };
            SExprData::Atom(data)
        } else if expr.is_list() {
            // Safety argument: the data will live as long as the containing context, and is
            // immutable once it's inserted, so using the lifetime of the Arena is acceptable.
            let data: &[SExpr] =
                unsafe { std::mem::transmute(inner.lists[expr.index()].as_slice()) };

            if data.len() == 2 && data.iter().all(|e| e.is_atom()) {
                // Safety argument: the data will live as long as the containing context, and is
                // immutable once it's inserted, so using the lifetime of the Arena is acceptable.
                let l_data =
                    unsafe { std::mem::transmute(inner.strings[data[0].index()].as_str()) };

                if !"+-".contains(l_data) {
                    return SExprData::List(data);
                }

                let r_data =
                    unsafe { std::mem::transmute(inner.strings[data[1].index()].as_str()) };
                return SExprData::TwoAtomList(l_data, r_data);
            }

            SExprData::List(data)
        } else if expr.is_string() {
            // Safety argument: the data will live as long as the containing context, and is
            // immutable once it's inserted, so using the lifetime of the Arena is acceptable.
            let data = unsafe { std::mem::transmute(inner.strings[expr.index()].as_str()) };
            SExprData::String(data)
        } else {
            unreachable!()
        }
    }
}

/// The data contents of an [`SExpr`][crate::SExpr].
///
/// ## Converting `SExprData` to an Integer
///
/// There are `TryFrom<SExprData>` implementations for common integer types that
/// you can use:
///
/// ```
/// let mut ctx = easy_smt::ContextBuilder::new().build().unwrap();
///
/// let neg_one = ctx.binary(8, -1_i8);
/// assert_eq!(ctx.display(neg_one).to_string(), "#b11111111");
///
/// let x = u8::try_from(ctx.get(neg_one)).unwrap();
/// assert_eq!(x, 0xff);
/// ```
#[derive(Debug)]
pub enum SExprData<'a> {
    Atom(&'a str),
    String(&'a str),
    List(&'a [SExpr]),
    TwoAtomList(&'a str, &'a str),
}

/// An error which can be returned when trying to interpret an s-expr as an
/// integer.
#[derive(Debug)]
#[non_exhaustive]
pub enum IntFromSExprError {
    /// The s-expr is a list, not an atom, and therefore cannot be converted to
    /// an integer.
    NotAnAtom,

    /// There was an error parsing the atom as an integer.
    ParseIntError(std::num::ParseIntError),
}

impl std::fmt::Display for IntFromSExprError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IntFromSExprError::NotAnAtom => write!(
                f,
                "The s-expr is a list, not an atom, and \
                 therefore cannot be converted to an integer."
            ),
            IntFromSExprError::ParseIntError(_) => {
                write!(f, "There was an error parsing the atom as an integer.")
            }
        }
    }
}

impl std::error::Error for IntFromSExprError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            IntFromSExprError::NotAnAtom => None,
            IntFromSExprError::ParseIntError(inner) => Some(inner as _),
        }
    }
}

impl From<std::num::ParseIntError> for IntFromSExprError {
    fn from(e: std::num::ParseIntError) -> Self {
        IntFromSExprError::ParseIntError(e)
    }
}

macro_rules! impl_try_from_int {
    ( $( $ty:ty )* ) => {
        $(
            impl TryFrom<SExprData<'_>> for $ty {
                type Error = IntFromSExprError;

                fn try_from(value: SExprData<'_>) -> Result<Self, Self::Error> {
                    match value {
                        SExprData::Atom(a) => {
                            if let Some(a) = a.strip_prefix("#x") {
                                let x = <$ty>::from_str_radix(a, 16)?;
                                return Ok(x);
                            }

                            if let Some(a) = a.strip_prefix("#b") {
                                let x = <$ty>::from_str_radix(a, 2)?;
                                return Ok(x);
                            }

                            let x = a.parse::<$ty>()?;
                            Ok(x)
                        }
                        SExprData::TwoAtomList(l, r) => {
                            let j = l.to_owned() + r;
                            let x = j.parse::<$ty>()?;
                            Ok(x)
                        },
                        SExprData::List(_) |
                        SExprData::String(_)  => Err(IntFromSExprError::NotAnAtom),
                    }
                }
            }
        )*
    };
}

impl_try_from_int!(u8 u16 u32 u64 u128 usize i8 i16 i32 i64);

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
                SExprData::String(data) => std::fmt::Debug::fmt(data, f),
                SExprData::TwoAtomList(l_data, r_data) => {
                    write!(f, "(")?;
                    std::fmt::Display::fmt(l_data, f)?;
                    write!(f, " ")?;
                    std::fmt::Display::fmt(r_data, f)?;
                    write!(f, ")")
                }
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

#[derive(Debug)]
pub(crate) enum ParseError {
    /// Parsing failed.
    Message(String),

    /// More input is needed to finish parsing.
    More,
}

#[cfg(test)]
impl ParseError {
    fn expect_message(self) -> String {
        match self {
            ParseError::Message(msg) => msg,
            ParseError::More => panic!("Expected a ParseError::Message"),
        }
    }

    fn expect_more(self) {
        match self {
            ParseError::Message(_) => panic!("Expected a ParseError::More"),
            ParseError::More => (),
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

    fn string(&mut self, arena: &Arena, sym: &str) -> Option<SExpr> {
        let expr = arena.string(sym);
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

    pub(crate) fn parse(&mut self, arena: &Arena, bytes: &str) -> Result<SExpr, ParseError> {
        let lexer = Lexer::new(bytes);
        for token in lexer {
            match token {
                Token::Symbol(sym) => {
                    let res = self.atom(arena, sym);
                    if let Some(res) = res {
                        return Ok(res);
                    }
                }

                Token::String(lit) => {
                    let res = self.string(arena, lit);
                    if let Some(res) = res {
                        return Ok(res);
                    }
                }

                Token::LParen => self.context.push(Vec::new()),

                Token::RParen => {
                    let res = self.app(arena);
                    if let Some(res) = res {
                        return Ok(res);
                    }
                }

                Token::Error(msg) => {
                    return Err(ParseError::Message(msg));
                }
            }
        }

        Err(ParseError::More)
    }
}

#[derive(Debug)]
enum Token<'a> {
    LParen,
    RParen,
    Symbol(&'a str),
    String(&'a str),
    Error(String),
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

    /// Scan the current symbol and return the complete lexed string.
    fn scan_symbol(&mut self, start: usize, is_quote: bool) -> Token<'a> {
        // Are we within a || pair?
        let mut quoted = is_quote;
        let mut end;

        loop {
            if let Some((ix, c)) = self.indices.peek() {
                end = *ix;
                if quoted && *c != '|' {
                    // If we're in a quoted context, treat this as one identifier.
                    self.indices.next();
                    continue;
                } else if *c == '|' {
                    // If we see a quote, toggle the quoted flag.
                    quoted = !quoted;
                    self.indices.next();
                    continue;
                } else if c.is_alphabetic() || c.is_numeric() || "~!@$%^&*_-+=<>.?/".contains(*c) {
                    self.indices.next();
                    continue;
                }
            } else {
                end = self.chars.len();
            }

            break;
        }

        if quoted {
            return Token::Error(format!("Unterminated `|` in symbol starting at {start}"));
        }

        Token::Symbol(&self.chars[start..end])
    }

    /// Scan a string literal. `start` is expected to be the offset of the opening `"`. The scanned
    /// string excludes both the start and end quotes.
    fn scan_string(&mut self, start: usize) -> Token<'a> {
        while let Some((ix, c)) = self.indices.next() {
            if c == '\\' {
                self.indices.next();
                continue;
            }

            if c == '"' {
                return Token::String(&self.chars[start + 1..ix]);
            }
        }

        Token::Error(format!(
            "Failed to find terminator for string literal at offset {start}"
        ))
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

                '"' => {
                    return Some(self.scan_string(start));
                }

                // this is a bit of a hack, but if we encounter a comment we clear out the indices
                // iterator as the parser is line oriented.
                ';' => self.indices = self.chars[0..0].char_indices().peekable(),

                c if c.is_whitespace() => {}

                c => return Some(self.scan_symbol(start, c == '|')),
            }
        }

        None
    }
}

#[cfg(test)]
mod tests {
    use super::{Arena, Parser, SExprData};
    use crate::ContextBuilder;

    #[test]
    fn is_atom() {
        let ctx = ContextBuilder::new().build().unwrap();
        let pizza = ctx.atom("pizza");
        assert!(pizza.is_atom());
        assert!(!pizza.is_list());
    }

    #[test]
    fn is_list() {
        let ctx = ContextBuilder::new().build().unwrap();
        let toppings = ctx.list(vec![
            ctx.atom("tomato-sauce"),
            ctx.atom("mozzarella"),
            ctx.atom("basil"),
        ]);
        assert!(toppings.is_list());
        assert!(!toppings.is_atom());
    }

    #[test]
    fn parses_string_lit() {
        let arena = Arena::new();
        let mut p = Parser::new();

        let expr = p.parse(&arena, "(error \"line 3 column 16: Parsing function declaration. Expecting sort list '(' got :a\")").expect("Parsing a list with a string literal");

        assert!(expr.is_list());

        let SExprData::List(es) = arena.get(expr) else {
            panic!("Failed to parse a list");
        };

        assert_eq!(es.len(), 2);

        assert!(es[0].is_atom());
        assert!(es[1].is_string());

        match arena.get(es[1]) {
            SExprData::String(text) => assert_eq!(
                text,
                "line 3 column 16: Parsing function declaration. Expecting sort list '(' got :a"
            ),
            _ => unreachable!(),
        };

        let expr = p
            .parse(&arena, "\"\"")
            .expect("Parsing the empty string literal");

        assert!(expr.is_string());
        match arena.get(expr) {
            SExprData::String(text) => assert!(text.is_empty()),
            _ => unreachable!(),
        }
    }

    #[test]
    fn parse_error() {
        let arena = Arena::new();
        let mut p = Parser::new();

        let err = p
            .parse(&arena, "(error \"line)")
            .expect_err("Unterminated string literal should fail to parse")
            .expect_message();

        assert_eq!(
            err,
            "Failed to find terminator for string literal at offset 7"
        );
    }

    #[test]
    fn parse_multi_line() {
        let arena = Arena::new();
        let mut p = Parser::new();

        p.parse(&arena, "(open (extra \"sequence\")")
            .expect_err("Open list should expect more")
            .expect_more();

        p.parse(&arena, "b")
            .expect_err("Single atom doesn't close a list")
            .expect_more();

        let expr = p
            .parse(&arena, ")")
            .expect("Closing paren should finish the parse");

        let SExprData::List(es) = arena.get(expr) else {
            panic!("Failed to parse a list");
        };

        assert_eq!(es.len(), 3);
        assert!(es[0].is_atom());
        assert!(es[1].is_list());
        assert!(es[2].is_atom());
    }
}
