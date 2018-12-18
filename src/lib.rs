extern crate pest;
#[macro_use]
extern crate pest_derive;

//use pest::{Parser};
use pest::error::Error;
use pest::Parser;
use pest::iterators::Pair;
use std::sync::Arc;
use std::collections::{HashMap,HashSet};
use std::ops::Deref;

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
}

/// An iterator for s-expressions.
pub struct RispIter<'a> {
    curr: &'a RispValue,
}

impl<'a> Iterator for RispIter<'a> {
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
    pub fn iter<'a>(&'a self) -> RispIter<'a> {
        RispIter{curr: self}
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

#[derive(Debug,PartialEq)]
pub enum CompilationError {
    UndefinedSymbol(String),
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

fn transform_tree(pair: Pair<Rule>) -> RispValue {
    match pair.as_rule() {
        Rule::int => RispValue::Int(pair.as_str().parse().unwrap()),
        Rule::float => RispValue::Float(pair.as_str().parse().unwrap()),
        Rule::symbol => RispValue::Symbol(String::from(pair.as_str())),
        Rule::string => RispValue::String(unescape(pair.into_inner().next().unwrap().as_str())),
        Rule::list => {
            let mut elems : Vec<RispValue> = pair.into_inner().map(transform_tree).collect();
            elems.reverse();
            let mut list = RispValue::Nil;
            for elem in elems {
                list = RispValue::Cons(Arc::new(elem), Arc::new(list));
            }
            list
        },
        Rule::pair => {
            let mut elems = pair.into_inner().map(transform_tree);
            RispValue::Cons(Arc::new(elems.next().unwrap()), Arc::new(elems.next().unwrap()))
        },
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
/// assert_eq!(risp::compile(se1[0].clone(), &mut ctx).unwrap(), se1[0]);
/// let se2 = risp::read("123.456").unwrap();
/// assert_eq!(risp::compile(se2[0].clone(), &mut ctx).unwrap(), se2[0]);
/// let se3 = risp::read("\"123\"").unwrap();
/// assert_eq!(risp::compile(se3[0].clone(), &mut ctx).unwrap(), se3[0]);
/// ```
///
/// Global symbols are replaced with their underlying values.
/// ```
/// let se = risp::read("foo").unwrap();
/// let mut ctx = risp::BasicStaticContext::new();
/// ctx.define_global(String::from("foo"), risp::RispValue::Int(2));
/// assert_eq!(risp::compile(se[0].clone(), &mut ctx).unwrap(), risp::RispValue::Int(2));
/// ```
/// However, if the symbol exists in the `locals` set, it is left as-is.
/// ```
/// let se = risp::read("foo").unwrap();
/// let mut ctx = risp::BasicStaticContext::new();
/// ctx.define_global(String::from("foo"), risp::RispValue::Int(2));
/// let mut ctx2 = risp::DerivedStaticContext::new(&ctx);
/// ctx2.add_local(String::from("foo"));
/// assert_eq!(risp::compile(se[0].clone(), &mut ctx2).unwrap(), se[0]);
/// ```
/// If a symbol does not exist, a compilation error is returned.
/// ```
/// let se = risp::read("foo").unwrap();
/// let mut ctx = risp::BasicStaticContext::new();
/// assert_eq!(risp::compile(se[0].clone(), &mut ctx),
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
/// argument, and returns that one argument.
pub fn compile(sexpr: RispValue, ctx: &mut StaticContext) -> Result<RispValue, CompilationError> {
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

