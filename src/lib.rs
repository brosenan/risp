extern crate pest;
#[macro_use]
extern crate pest_derive;

use pest::error::Error;
use pest::Parser;
use pest::iterators::Pair;
use std::sync::Arc;
use std::collections::{HashMap,HashSet};
use std::ops::Deref;
use std::iter::FromIterator;

#[derive(Parser)]
#[grammar = "risp.pest"]
struct RispParser;

#[derive(Debug,PartialEq,Clone)]
pub enum RispValue {
    Int(i64),
    Float(f64),
    Symbol(String),
    String(String),
    Nil,
    Cons(Arc<RispValue>, Arc<RispValue>),
    Fn(RispFunc),
}

#[derive(Clone)]
pub struct RispFunc {
    func: Arc<Fn(&RispValue)->Result<RispValue, CompilationError>>
}

impl RispFunc {
    pub fn new(func: Arc<Fn(&RispValue)->Result<RispValue, CompilationError>>) -> Self {
        RispFunc{func}
    }
    pub fn call(&self, args: &RispValue) -> Result<RispValue, CompilationError> {
        (self.func)(args)
    }
}

impl std::fmt::Debug for RispFunc {
    fn fmt(&self, foo: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        Ok(())
    }
}

impl PartialEq for RispFunc {
    fn eq(&self, other: &Self) -> bool {
        false
    }
}

/// An iterator for s-expressions. Does not consume the underlying
/// list, and provides immutable references to the items.
pub struct RispRefIter<'a> {
    curr: &'a RispValue,
}

impl<'a> Iterator for RispRefIter<'a> {
    type Item = &'a RispValue;
    fn next(&mut self) -> Option<Self::Item> {
        match self.curr {
            RispValue::Cons(item, next) => {
                self.curr = next;
                Some(item)
            },
            _ => None
        }
    }
}

impl RispValue {
    /// The `iter` method constructs an iterator to traverse an
    /// s-expression. Given a list, it will traverse all items in the
    /// list.
    /// ```
    /// use risp::*;
    /// let sexprs = read("(1 2 3)").unwrap();
    /// let mut i = sexprs[0].iter();
    /// assert_eq!(i.next(), Some(&RispValue::Int(1)));
    /// assert_eq!(i.next(), Some(&RispValue::Int(2)));
    /// assert_eq!(i.next(), Some(&RispValue::Int(3)));
    /// assert_eq!(i.next(), None);
    /// ```
    pub fn iter<'a>(&'a self) -> RispRefIter<'a> {
        RispRefIter{curr: self}
    }

    /// Returns the length of a list.
    /// ```
    /// use risp::*;
    /// let exprs = read("(1 2 3) 4").unwrap();
    /// assert_eq!(exprs[0].len(), 3);
    /// assert_eq!(exprs[1].len(), 0);
    /// ```
    pub fn len(&self) -> usize {
        let mut curr = self;
        let mut i = 0;
        while let RispValue::Cons(_, next) = curr {
            curr = next;
            i += 1;
        }
        i
    }

    /// Returns a vector of the given size if this expression is
    /// exactly the specified length. Otherwise, returns an arity
    /// mismatch error.
    /// ```
    /// use risp::*;
    /// let exprs = read("(1 2 3) (4 5)").unwrap();
    /// assert_eq!(exprs[0].to_vec_of_len(3).unwrap(),
    ///            vec![&RispValue::Int(1), &RispValue::Int(2), &RispValue::Int(3)]);
    /// assert_eq!(exprs[1].to_vec_of_len(3),
    ///            Err(CompilationError::ArityMismatch(3, 2)));
    /// ```
    pub fn to_vec_of_len<'a>(&'a self, expected_len: usize) -> Result<Vec<&'a RispValue>, CompilationError> {
        if self.len() == expected_len {
            Ok(self.iter().collect())
        } else {
            Err(CompilationError::ArityMismatch(expected_len, self.len()))
        }
    }

    /// Returns the first `expected_len` elements as a vector, assuming there are
    /// _at least_ the `expected_len` elements in the list. Otherwise, returns an arity
    /// mismatch error.
    /// ```
    /// use risp::*;
    /// let exprs = read("(1 2 3 4) (5 6)").unwrap();
    /// assert_eq!(exprs[0].to_vec_of_at_least_len(3).unwrap(),
    ///            vec![&RispValue::Int(1), &RispValue::Int(2), &RispValue::Int(3)]);
    /// assert_eq!(exprs[1].to_vec_of_at_least_len(3),
    ///            Err(CompilationError::ArityMismatch(3, 2)));
    /// ```
    pub fn to_vec_of_at_least_len<'a>(&'a self, expected_len: usize) -> Result<Vec<&'a RispValue>, CompilationError> {
        if self.len() >= expected_len {
            Ok(self.iter().take(expected_len).collect())
        } else {
            Err(CompilationError::ArityMismatch(expected_len, self.len()))
        }
    }

    /// Returns whether or not this is a list.
    /// ```
    /// use risp::*;
    /// assert_eq!(RispValue::Int(1).is_list(), false);
    /// assert_eq!(RispValue::Nil.is_list(), true);
    /// assert_eq!(RispValue::Cons(std::sync::Arc::new(RispValue::Int(1)),
    ///                            std::sync::Arc::new(RispValue::Nil)).is_list(), true);
    /// assert_eq!(RispValue::Cons(std::sync::Arc::new(RispValue::Int(1)),
    ///                            std::sync::Arc::new(RispValue::Int(2))).is_list(), false);
    /// ```
    pub fn is_list(&self) -> bool {
        match self {
            RispValue::Nil => true,
            RispValue::Cons(_, next) => next.is_list(),
            _ => false,
        }
    }

    /// Returns a reference to the first element of a list, or `None`
    /// for non-lists or empty lists.
    /// ```
    /// use risp::*;
    /// let l = read("(1 2 3 4)").unwrap()[0].clone();
    /// assert_eq!(l.first(), Some(&RispValue::Int(1)));
    /// ```
    pub fn first(&self) -> Option<&RispValue> {
        match self {
            RispValue::Cons(item, _) => Some(item),
            _ => None,
        }
    }

    /// Returns a reference to the nth element of a list, or `None`
    /// for non-lists or lists with less than n+1 elements.
    /// ```
    /// use risp::*;
    /// let l = read("(1 2 3 4)").unwrap()[0].clone();
    /// assert_eq!(l.nth(2), Some(&RispValue::Int(3)));
    /// ```
    pub fn nth(&self, n: usize) -> Option<&RispValue> {
        self.iter().skip(n).next()
    }

    /// Returns a reference to last element of a list, or `None` for
    /// non-lists or empty lists.
    /// ```
    /// use risp::*;
    /// let l = read("(1 2 3 4)").unwrap()[0].clone();
    /// assert_eq!(l.last(), Some(&RispValue::Int(4)));
    /// ```
    pub fn last(&self) -> Option<&RispValue> {
        let mut curr = self;
        let mut res = None;
        while let RispValue::Cons(item, next) = curr {
            res = Some(item.deref());
            curr = next;
        }
        res
    }

    /// Returns a reference to the underlying string, if this value is
    /// a symbol, or None otherwise.
    /// ```
    /// use risp::*;
    /// assert_eq!(RispValue::Int(2).as_symbol(), None);
    /// assert_eq!(RispValue::Symbol(String::from("foo")).as_symbol(),
    ///            Some(&String::from("foo")));
    /// ```
    pub fn as_symbol(&self) -> Option<&String> {
        if let RispValue::Symbol(s) = self {
            Some(s)
        } else {
            None
        }
    }

    /// Matches this expression against a given pattern. On a
    /// successful match, returns a map of bindings acquired in the
    /// process. On a failed match, returns None.
    ///
    /// Matching against a scalar value returns an empty binding if
    /// the value is equal to the expression.
    /// ```
    /// use risp::*;
    /// use std::collections::*;
    /// assert_eq!(RispValue::Int(2).match_pattern(&RispValue::Int(3)), None);
    /// assert_eq!(RispValue::Int(3).match_pattern(&RispValue::Int(3)),
    ///            Some(HashMap::new()));
    /// ```
    ///
    /// Matching anything against a symbol returns a binding in which
    /// the symbol's undrelying string maps to the expression.
    /// ```
    /// use risp::*;
    /// use std::collections::*;
    /// let mut expected = HashMap::new();
    /// expected.insert(String::from("foo"), RispValue::Int(3));
    /// assert_eq!(RispValue::Int(3).match_pattern(&RispValue::Symbol(String::from("foo"))),
    ///            Some(expected));
    /// ```
    ///
    /// List are recurred into.
    /// ```
    /// use risp::*;
    /// use std::collections::*;
    /// let pattern = read("(a (b c))").unwrap()[0].clone();
    /// let expr1 = read("(1 (2 3))").unwrap()[0].clone();
    ///
    /// let mut expected = HashMap::new();
    /// expected.insert(String::from("a"), RispValue::Int(1));
    /// expected.insert(String::from("b"), RispValue::Int(2));
    /// expected.insert(String::from("c"), RispValue::Int(3));
    /// assert_eq!(expr1.match_pattern(&pattern), Some(expected));
    ///
    /// let expr2 = read("(1 2)").unwrap()[0].clone();
    /// assert_eq!(expr2.match_pattern(&pattern), None);
    ///
    /// // Lists have to be of the exact same size to match the pattern.
    /// let expr3 = read("(1 (2 3) 4)").unwrap()[0].clone();
    /// assert_eq!(expr3.match_pattern(&pattern), None);
    /// ```
    ///
    /// If the list ends with an ellipsis (`...`), the element just
    /// before the ellipsis is matched against the rest of the
    /// list. For example, the pattern `(a b c ...)` will match lists
    /// of length 2 or more, having `c` match a list containing the
    /// rest of the elements in the expression. For example, in the
    /// expression `(1 2 3 4 5)`, `a` will be bound to `1`, `b` will
    /// be bound to `2`, and `c` will be bound to `(3 4 5)`.
    /// ```
    /// use risp::*;
    /// use std::collections::*;
    /// let pattern = read("(a b c ...)").unwrap()[0].clone();
    /// let expr1 = read("(1 2 3 4 5)").unwrap()[0].clone();
    ///
    /// let mut expected = HashMap::new();
    /// expected.insert(String::from("a"), RispValue::Int(1));
    /// expected.insert(String::from("b"), RispValue::Int(2));
    /// expected.insert(String::from("c"), vec![3, 4, 5].iter().map(|x| RispValue::Int(x.clone())).collect());
    /// assert_eq!(expr1.match_pattern(&pattern), Some(expected));
    /// ```
    ///
    /// The special form `quote` matches its content by equality. For
    /// example, the pattern `'a` (or `(quote a)` will only match the symbol
    /// `a`.
    /// ```
    /// use risp::*;
    /// use std::collections::*;
    /// let pattern = read("'a").unwrap()[0].clone();
    /// assert_eq!(RispValue::Symbol(String::from("a")).match_pattern(&pattern),
    ///            Some(HashMap::new()));
    /// ```
    pub fn match_pattern(&self, pattern: &RispValue) -> Option<HashMap<String, RispValue>> {
        if let Some(s) = pattern.as_symbol() {
            let mut res = HashMap::new();
            res.insert(s.clone(), self.clone());
            Some(res)
        } else if pattern.is_list() && self.is_list() && pattern.len() == self.len() {
            self.iter().zip(pattern.iter())
                .map(|(expr, p)| expr.match_pattern(p))
                .fold(Some(HashMap::new()), |acc, res| {
                    match (acc, res) {
                        (None, _) => None,
                        (_, None) => None,
                        (Some(mut acc_bind), Some(res_bind)) => {
                            acc_bind.extend(res_bind);
                            Some(acc_bind)
                        }
                    }
                })
        } else if pattern.is_list() && self.is_list() && pattern.last() == Some(&RispValue::Symbol(String::from("..."))) && self.len() >= pattern.len() - 2 {
            let base_len = pattern.len() - 2;
            let rest: RispValue = self.iter().skip(base_len).map(|x| x.clone()).collect();
            let alt_expr: RispValue = self.iter().take(base_len).map(|x| x.clone()).chain(vec![rest].into_iter()).collect();
            let alt_pat: RispValue = pattern.iter().take(base_len + 1).map(|x| x.clone()).collect();
            alt_expr.match_pattern(&alt_pat)
        } else if pattern.is_list() && pattern.len() == 2 && pattern.first() == Some(&RispValue::Symbol(String::from("quote"))) {
            if self == pattern.nth(1).unwrap() {
                Some(HashMap::new())
            } else {
                None
            }   
        } else if self == pattern {
            Some(HashMap::new())
        } else {
            None
        }
    }

    /// If called on a function value, calls the function with the
    /// given argument list.
    /// ```
    /// use risp::*;
    /// use std::sync::Arc;
    /// let ret = RispValue::Fn(RispFunc::new(Arc::new(|args| {
    ///     if let Some(x) = args.first() {
    ///         Ok(x.clone())
    ///     } else {
    ///         Err(CompilationError::ArityMismatch(1, 0))
    ///     }
    /// }))).call(&vec![RispValue::Int(1)].into_iter().collect());
    /// assert_eq!(ret, Ok(RispValue::Int(1)));
    /// ```
    ///
    /// When not called on a function, `call` returns a `TypeMismatch`
    /// error.
    /// ```
    /// use risp::*;
    /// use std::sync::Arc;
    /// let ret = RispValue::Nil.call(&vec![RispValue::Int(1)].into_iter().collect());
    /// assert_eq!(ret, Err(CompilationError::TypeMismatch(String::from("function"), String::from("Nil"))));
    /// ```
    pub fn call(&self, args: &RispValue) -> Result<RispValue, CompilationError> {
        match self {
            RispValue::Fn(func) => func.call(args),
            _ => Err(CompilationError::TypeMismatch(String::from("function"), format!("{:?}", self))),
        }
    }

    /// Evaluates an expression based on the given variable bindings.
    ///
    /// A symbol is evaluated by looking it up in the bindings.
    /// ```
    /// use risp::*;
    /// use std::collections::HashMap;
    /// let mut b = HashMap::new();
    /// b.insert(String::from("foo"), RispValue::Int(2));
    /// let ctx0 = BasicDynamicContext::new();
    /// let ctx = DerivedDynamicContext::new(&ctx0, b);
    /// 
    /// assert_eq!(RispValue::Symbol(String::from("foo")).eval(&ctx),
    ///            Ok(RispValue::Int(2)));
    /// ```
    pub fn eval(&self, ctx: &DynamicContext) -> Result<RispValue, CompilationError> {
        match self {
            RispValue::Symbol(s) => ctx.lookup(s)
                .map(|x| x.clone())
                .ok_or(CompilationError::UndefinedSymbol(s.clone())),
            _ => unreachable!()
        }
    }
}

/// `RispValue` implements `FromIterator`, so that containers
/// containing `RispValue`s can be `collect`ed into risp lists.
/// ```
/// use risp::*;
/// let v: Vec<RispValue> =
///     vec![1, 2, 3].into_iter().map(|x| RispValue::Int(x)).collect();
/// let l: RispValue = v.into_iter().collect();
/// assert_eq!(l.len(), 3);
/// ```
impl FromIterator<RispValue> for RispValue {
    fn from_iter<I>(initer: I) -> Self
    where I: IntoIterator<Item = RispValue> {
        let vec : Vec<RispValue> = initer.into_iter().collect();
        vec_to_list(vec)
    }
}

/// This trait represents the state of compilation, defining what
/// symbols (global, local and macros) are defiend, and in the cases
/// of globals and macros, with which values.
pub trait StaticContext {
    /// Get a global value if defined, or `None` if not.
    fn get_global(&self, sym: &String) -> Option<RispValue>;
    /// Is a local symbol defined in this context?
    fn is_local(&self, sym: &String) -> bool;
    /// Get a macro of the given name, if exists. A macro is
    /// represented as a function from `RispValue` containing the
    /// form, and returns a `Result` of type `RispValue` containing
    /// the form to replace it with.
    fn get_macro<'a>(&'a self, sym: &String) -> Option<&'a Fn(RispValue) -> Result<RispValue, CompilationError>>;
}

/// A static context that defines globals and macros. It contains no locals.
/// ```
/// use risp::*;
/// let mut ctx = BasicStaticContext::new();
/// ctx.define_global(String::from("foo"), RispValue::Int(2));
/// ctx.define_macro(String::from("m"), Box::new(|x| Ok(x)));
/// assert_eq!(ctx.get_global(&String::from("foo")),
///            Some(RispValue::Int(2)));
/// assert_eq!(ctx.is_local(&String::from("foo")), false);
/// let m = ctx.get_macro(&String::from("m")).unwrap();
/// ```
pub struct BasicStaticContext {
    globals: HashMap<String, RispValue>,
    macros: HashMap<String, Box<Fn(RispValue) -> Result<RispValue, CompilationError>>>,
}

impl BasicStaticContext {
    /// Construct an empty global context.
    pub fn new() -> Self {
        Self {
            globals: HashMap::new(),
            macros: HashMap::new(),
        }
    }
    /// Add a global symbol to the global context. For example:
    pub fn define_global(&mut self, sym: String, value: RispValue) {
        self.globals.insert(sym, value);
    }

    /// Define a macro.
    pub fn define_macro(&mut self, sym: String, macro_fun: Box<Fn(RispValue) -> Result<RispValue, CompilationError>>) {
        self.macros.insert(sym, macro_fun);
    }
}

impl StaticContext for BasicStaticContext {
    fn is_local(&self, _sym: &String) -> bool {
        false
    }
    fn get_global(&self, sym: &String) -> Option<RispValue> {
        match self.globals.get(sym) {
            None => None,
            Some(val) => Some(val.clone())
        }
    }
    fn get_macro<'a>(&'a self, sym: &String) -> Option<&'a Fn(RispValue) -> Result<RispValue, CompilationError>> {
        match self.macros.get(sym) {
            None => None,
            Some(m) => Some(m.deref()),
        }
    }
}
/// A derived static context extends a base context, and possibly adds
/// new local symbols. Its lifetime parameter means its base context
/// must outlive it.
/// ```
/// use risp::*;
/// let mut base = BasicStaticContext::new();
/// base.define_global(String::from("foo"), RispValue::Int(2));
/// base.define_macro(String::from("m"), Box::new(|x| Ok(x)));
/// let mut derived = DerivedStaticContext::new(&base);
/// derived.add_local(String::from("bar"));
/// assert_eq!(derived.get_global(&String::from("foo")).unwrap(),
///            RispValue::Int(2));
/// let m = derived.get_macro(&String::from("m")).unwrap();
/// assert_eq!(derived.is_local(&String::from("bar")), true);
/// assert_eq!(derived.is_local(&String::from("baz")), false);
/// ```
pub struct DerivedStaticContext<'a> {
    base: &'a StaticContext,
    locals: HashSet<String>,
}
impl<'a> DerivedStaticContext<'a> {
    pub fn new(base: &'a StaticContext) -> Self {
        Self{base, locals: HashSet::new()}
    }
    pub fn add_local(&mut self, sym: String) {
        self.locals.insert(sym);
    }
}
impl<'a> StaticContext for DerivedStaticContext<'a> {
    fn is_local(&self, sym: &String) -> bool {
        self.locals.contains(sym) || self.base.is_local(sym)
    }
    fn get_global(&self, sym: &String) -> Option<RispValue> {
        self.base.get_global(sym)
    }
    fn get_macro<'b>(&'b self, sym: &String) -> Option<&'b Fn(RispValue) -> Result<RispValue, CompilationError>> {
        self.base.get_macro(sym)
    }
}

/// The context of an evaluation
pub trait DynamicContext {
    /// Lookup the value assiciated with a symbol.
    fn lookup(&self, symbol: &String) -> Option<&RispValue>;
}

/// A dynamic context with no symbols defined
pub struct BasicDynamicContext {}

impl BasicDynamicContext {
    pub fn new() -> Self {
        BasicDynamicContext{}
    }
}

impl DynamicContext for BasicDynamicContext {
    /// `BasicDynamicContext` has no symbols to look-up.
    /// ```
    /// use risp::*;
    /// let ctx = BasicDynamicContext::new();
    /// assert_eq!(ctx.lookup(&String::from("foo")), None);
    /// ```
    fn lookup(&self, symbol: &String) -> Option<&RispValue> {
        None
    }
}

/// A derived dynamic context, adds bindings in a `HashMap` to an
/// existing `DynamicContext`.
pub struct DerivedDynamicContext<'a> {
    base: &'a DynamicContext,
    bindings: HashMap<String, RispValue>,
}

impl<'a> DerivedDynamicContext<'a> {
    pub fn new(base: &'a DynamicContext, bindings: HashMap<String, RispValue>) -> Self {
        DerivedDynamicContext{base, bindings}
    }
}

impl<'a> DynamicContext for DerivedDynamicContext<'a> {
    /// Lookup works according to the following priorities:
    /// 1. The given `HashMap`.
    /// 2. The base context.
    /// 3. Returns `None`.
    /// ```
    /// use risp::*;
    /// use std::collections::HashMap;
    /// let ctx0 = BasicDynamicContext::new();
    ///
    /// let mut m1 = HashMap::new();
    /// m1.insert(String::from("foo"), RispValue::Int(1));
    /// m1.insert(String::from("bar"), RispValue::Int(2));
    /// let ctx1 = DerivedDynamicContext::new(&ctx0, m1);
    ///
    /// let mut m2 = HashMap::new();
    /// m2.insert(String::from("foo"), RispValue::Int(3));
    /// let ctx2 = DerivedDynamicContext::new(&ctx1, m2);
    ///
    /// // foo is found in both ctx1 and ctx2, but the value in ctx2
    /// // is preferred.
    /// assert_eq!(ctx2.lookup(&String::from("foo")), Some(&RispValue::Int(3)));
    ///
    /// // bar is only found in the base context. It is searched as a fallback.
    /// assert_eq!(ctx2.lookup(&String::from("bar")), Some(&RispValue::Int(2)));
    /// ```
    fn lookup(&self, symbol: &String) -> Option<&RispValue> {
        self.bindings.get(symbol).or_else(|| self.base.lookup(symbol))
    }
}

#[derive(Debug,PartialEq)]
pub enum CompilationError {
    UndefinedSymbol(String),
    ArityMismatch(usize, usize),
    TypeMismatch(String, String),
}

fn unescape_char(c: char) -> char {
    match c {
        'n' => '\n',
        'r' => '\r',
        't' => '\t',
        _ => c
    }
}

fn unescape(inp: &str) -> String {
    let mut out = String::new();
    let mut esc = false;
    for c in inp.chars() {
        if esc {
            out.push(unescape_char(c));
            esc = false;
        } else {
            if c == '\\' {
                esc = true
            } else {
                out.push(c);
            }
        }
    }
    out
}

fn vec_to_list(vec: Vec<RispValue>) -> RispValue {
    let mut elems = vec;
    elems.reverse();
    let mut list = RispValue::Nil;
    for elem in elems {
        list = RispValue::Cons(Arc::new(elem), Arc::new(list));
    }
    list
}

fn transform_tree(pair: Pair<Rule>) -> RispValue {
    match pair.as_rule() {
        Rule::int => RispValue::Int(pair.as_str().parse().unwrap()),
        Rule::float => RispValue::Float(pair.as_str().parse().unwrap()),
        Rule::symbol => RispValue::Symbol(String::from(pair.as_str())),
        Rule::string => RispValue::String(unescape(pair.into_inner().next().unwrap().as_str())),
        Rule::list => {
            let mut elems : Vec<RispValue> = pair.into_inner().map(transform_tree).collect();
            vec_to_list(elems)
        },
        Rule::pair => {
            let mut elems = pair.into_inner().map(transform_tree);
            RispValue::Cons(Arc::new(elems.next().unwrap()), Arc::new(elems.next().unwrap()))
        },
        Rule::quoted => RispValue::Cons(Arc::new(RispValue::Symbol(String::from("quote"))),
                                        Arc::new(RispValue::Cons(Arc::new(transform_tree(pair.into_inner().next().unwrap())),
                                                                 Arc::new(RispValue::Nil)))),
        Rule::decimal | Rule::symbol_start_char | Rule::chars | Rule::char | Rule::WHITESPACE
            | Rule::sexpr | Rule::sexprs => unreachable!(),
    }
}

/// # Reader
/// The function `read` implements a _reader_, converting a string into an s-expression, represented by `risp::RispValue`.
///
/// Decimal integers are read as risp::RispValue::Int(...)
/// ```
/// assert_eq!(risp::read("123").unwrap()[0], risp::RispValue::Int(123));
/// ```
/// Numbers with decimal points are considered risp::RispValue::Float(...)
/// ```
/// assert_eq!(risp::read("3.14").unwrap()[0], risp::RispValue::Float(3.14));
/// ```
/// Symbols use a variety of characters, but they cannot start with a digit.
/// ```
/// assert_eq!(risp::read("foo-BAR123?<>!@$%^&*").unwrap()[0],
///            risp::RispValue::Symbol(String::from("foo-BAR123?<>!@$%^&*")));
/// ```
/// String literals begin and end with quotation marks (").
/// ```
/// assert_eq!(risp::read("\"foo\"").unwrap()[0],
///            risp::RispValue::String(String::from("foo")));
/// ```
/// Escaping is handled for ", \, n, r, and t.
/// ```
/// assert_eq!(risp::read("\"\\\"\\\\\\n\\r\\t\"").unwrap()[0], risp::RispValue::String(String::from("\"\\\n\r\t")));
/// ```
/// An empty list is parsed as Nil
/// ```
/// assert_eq!(risp::read("()").unwrap()[0], risp::RispValue::Nil);
/// ```
/// A list of elemens is a linked list of Cons
/// ```
/// assert_eq!(risp::read("(1 2)").unwrap()[0],
///            risp::RispValue::Cons(
///                std::sync::Arc::new(risp::RispValue::Int(1)),
///                std::sync::Arc::new(risp::RispValue::Cons(std::sync::Arc::new(risp::RispValue::Int(2)),
///                                         std::sync::Arc::new(risp::RispValue::Nil)))));
/// ```
/// Brackes enclose a Cons pair
/// ```
/// assert_eq!(risp::read("[1 2]").unwrap()[0],
///            risp::RispValue::Cons(std::sync::Arc::new(risp::RispValue::Int(1)),
///                                  std::sync::Arc::new(risp::RispValue::Int(2))));
/// ```
/// A single quote (`'`) prefixing an s-expressions constructs a `quote` special form.
/// ```
/// use risp::*;
/// use std::sync::Arc;
/// assert_eq!(read("'(a b c)").unwrap()[0],
///            read("(quote (a b c))").unwrap()[0]);
/// ```
///
/// Whitespace includes spaces, tabs and line-ends (LF and CR).
/// ```
/// risp::read("(fn foo (x y)\n\r\t(+ x y))").unwrap();
/// ```
/// risp::read() returns a vector containing all s-expressions in the input
/// ```
/// assert_eq!(risp::read("1 two \"three\"").unwrap(), vec![risp::RispValue::Int(1),
///                                                               risp::RispValue::Symbol(String::from("two")),
///                                                               risp::RispValue::String(String::from("three"))]);
/// ```

pub fn read<'a>(text: &'a str) -> Result<Vec<RispValue>, Error<Rule>> {
    let parse_result = RispParser::parse(Rule::sexprs, text)?.next().unwrap();
    Ok(parse_result.into_inner().map(transform_tree).collect())
}

/// # Compiler
///
/// The compiler (`compile` function) takes an s-expression and
/// compiles it into a _compiled_ s-expression.
///
/// Scalars are left unchaged.
/// ```
/// let mut ctx = risp::BasicStaticContext::new();
/// let se1 = risp::read("123").unwrap();
/// assert_eq!(risp::compile(se1[0].clone(), &ctx).unwrap(), se1[0]);
/// let se2 = risp::read("123.456").unwrap();
/// assert_eq!(risp::compile(se2[0].clone(), &ctx).unwrap(), se2[0]);
/// let se3 = risp::read("\"123\"").unwrap();
/// assert_eq!(risp::compile(se3[0].clone(), &ctx).unwrap(), se3[0]);
/// ```
///
/// Global symbols are replaced with their underlying values.
/// ```
/// let se = risp::read("foo").unwrap();
/// let mut ctx = risp::BasicStaticContext::new();
/// ctx.define_global(String::from("foo"), risp::RispValue::Int(2));
/// assert_eq!(risp::compile(se[0].clone(), &ctx).unwrap(), risp::RispValue::Int(2));
/// ```
/// However, if the symbol exists as a local symbol, it is left as-is.
/// ```
/// let se = risp::read("foo").unwrap();
/// let mut ctx = risp::BasicStaticContext::new();
/// ctx.define_global(String::from("foo"), risp::RispValue::Int(2));
/// let mut ctx2 = risp::DerivedStaticContext::new(&ctx);
/// ctx2.add_local(String::from("foo"));
/// assert_eq!(risp::compile(se[0].clone(), &ctx2).unwrap(), se[0]);
/// ```
/// If a symbol does not exist, a compilation error is returned.
/// ```
/// let se = risp::read("foo").unwrap();
/// let mut ctx = risp::BasicStaticContext::new();
/// assert_eq!(risp::compile(se[0].clone(), &ctx),
///            Err(risp::CompilationError::UndefinedSymbol(String::from("foo"))));
/// ```
///
/// ## Macros and Special Forms
///
/// Macros are functions that operate during compilation. They take
/// the form (`RispValue`) to be process, a value that is always a
/// list in which the macro name is the first element, and return
/// another RispValue, typically a form to be executed at runtime. The
/// form that is returned by a macro is then compiled again, so that
/// if it contains macros, they are expanded.
///
/// Consider a hypothetical macro `annotate`, which takes at least one
/// argument, and returns that one argument. This macro can be useful
/// for annotating things, e.g., using the rest of the form as a
/// comment.
///
/// For this macro to be available, we need to register it with the
/// basic context. Then, when compiling an s-expression that contains
/// this macro, it should be applied.
/// ```
/// use risp::*;
/// let mut ctx = BasicStaticContext::new();
/// ctx.define_macro(String::from("annotate"), Box::new(|expr| {
///     let form = expr.to_vec_of_at_least_len(2)?; // The macro name and the first argument
///     Ok(form[1].clone())
/// }));
/// let program = read("(annotate 1 2 3 4)").unwrap();
/// assert_eq!(compile(program[0].clone(), &ctx).unwrap(), RispValue::Int(1));
/// ```
///
/// ## Other Forms
///
/// Forms (lists) that are not macros are processed recursively.
/// ```
/// use risp::*;
/// let program1 = read("(a (b c))").unwrap();
/// let program2 = read("(1 (2 3))").unwrap();
/// let mut ctx = BasicStaticContext::new();
/// ctx.define_global(String::from("a"), RispValue::Int(1));
/// ctx.define_global(String::from("b"), RispValue::Int(2));
/// ctx.define_global(String::from("c"), RispValue::Int(3));
///
/// assert_eq!(compile(program1[0].clone(), &ctx).unwrap(), program2[0]);
/// ```
pub fn compile(sexpr: RispValue, ctx: &StaticContext) -> Result<RispValue, CompilationError> {
    if sexpr.is_list() {
        if let Some(s) = get_initial_symbol(&sexpr)? {
            if let Some(m) = ctx.get_macro(&s) {
                m(sexpr)
            } else {
                let mut result_vec : Vec<RispValue> = vec![];
                for x in sexpr.iter() {
                    result_vec.push(compile(x.clone(), ctx)?);
                }
                Ok(result_vec.into_iter().collect())
            }
        } else {
            unreachable!()
        }
    } else {
        match sexpr {
            RispValue::Symbol(s) => {
                if ctx.is_local(&s) {
                    Ok(RispValue::Symbol(s))
                } else {
                    match ctx.get_global(&s) {
                        Some(val) => Ok(val.clone()),
                        None => Err(CompilationError::UndefinedSymbol(s)),
                    }
                }
            },
            _ => Ok(sexpr),
        }
    }
}

fn get_initial_symbol(sexpr: &RispValue) -> Result<Option<String>, CompilationError> {
    if let [RispValue::Symbol(s)] = sexpr.to_vec_of_at_least_len(1)?.as_slice() {
        Ok(Some(s.to_string()))
    } else {
        Ok(None)
    }
}

pub mod builtins;
