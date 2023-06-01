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
    // `ArenaInner::lists`. If the high bit is set, this is a list, if it is
    // unset it is an atom.
    index: u32,

    // The ID of the arena that this `SExpr` is associated with. Used for debug
    // assertions.
    arena_id: ArenaId,
}

impl SExpr {
    /// Is this `SExpr` an atom?
    pub fn is_atom(&self) -> bool {
        self.index & (1 << 31) == 0
    }

    /// Is this `SExpr` a list?
    pub fn is_list(&self) -> bool {
        self.index & (1 << 31) == 1
    }

    fn atom(index: u32, arena_id: ArenaId) -> Self {
        assert!(index < u32::MAX);
        SExpr { index, arena_id }
    }

    fn list(index: u32, arena_id: ArenaId) -> Self {
        assert!(index < u32::MAX);
        let index = index | (1 << 31);
        SExpr { index, arena_id }
    }

    fn index(&self) -> usize {
        (self.index & !(1 << 31)) as usize
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
            id: ArenaId::new(),
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
            let sexpr = SExpr::atom(ix as u32, inner.id);

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
pub enum SExprData<'a> {
    Atom(&'a str),
    List(&'a [SExpr]),
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
                write!(f, "There wasn an error parsing the atom as an integer.")
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
                            if a.starts_with("#x") {
                                let a = &a[2..];
                                let x = <$ty>::from_str_radix(a, 16)?;
                                return Ok(x);
                            }

                            if a.starts_with("#b") {
                                let a = &a[2..];
                                let x = <$ty>::from_str_radix(a, 2)?;
                                return Ok(x);
                            }

                            let x = <$ty>::from_str_radix(a, 10)?;
                            Ok(x)
                        }
                        SExprData::List(_) => Err(IntFromSExprError::NotAnAtom),
                    }
                }
            }
        )*
    };
}

impl_try_from_int!(u8 u16 u32 u64 u128 usize);

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
