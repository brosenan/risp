extern crate pest;
#[macro_use]
extern crate pest_derive;

//use pest::{Parser};
use pest::error::Error;
use pest::Parser;
use pest::iterators::Pair;
use std::sync::Arc;
use std::collections::{HashMap,HashSet};

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

pub struct StaticContext {
    pub globals: HashMap<String, RispValue>,
    pub locals: HashSet<String>,
}

#[derive(Debug,PartialEq)]
pub enum CompilationError {
    UndefinedSymbol(String),
}

impl StaticContext {
    pub fn new() -> Self {
        Self {
            globals: HashMap::new(),
            locals: HashSet::new(),
        }
    }
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
/// The function `read_risp` implements a _reader_, converting a string into an s-expression, represented by `risp::RispValue`.
///
/// Decimal integers are read as risp::RispValue::Int(...)
/// ```
/// assert_eq!(risp::read_risp("123").unwrap()[0], risp::RispValue::Int(123));
/// ```
/// Numbers with decimal points are considered risp::RispValue::Float(...)
/// ```
/// assert_eq!(risp::read_risp("3.14").unwrap()[0], risp::RispValue::Float(3.14));
/// ```
/// Symbols use a variety of characters, but they cannot start with a digit.
/// ```
/// assert_eq!(risp::read_risp("foo-BAR123?<>!@$%^&*").unwrap()[0],
///            risp::RispValue::Symbol(String::from("foo-BAR123?<>!@$%^&*")));
/// ```
/// String literals begin and end with quotation marks (").
/// ```
/// assert_eq!(risp::read_risp("\"foo\"").unwrap()[0],
///            risp::RispValue::String(String::from("foo")));
/// ```
/// Escaping is handled for ", \, n, r, and t.
/// ```
/// assert_eq!(risp::read_risp("\"\\\"\\\\\\n\\r\\t\"").unwrap()[0], risp::RispValue::String(String::from("\"\\\n\r\t")));
/// ```
/// An empty list is parsed as Nil
/// ```
/// assert_eq!(risp::read_risp("()").unwrap()[0], risp::RispValue::Nil);
/// ```
/// A list of elemens is a linked list of Cons
/// ```
/// assert_eq!(risp::read_risp("(1 2)").unwrap()[0],
///            risp::RispValue::Cons(
///                std::sync::Arc::new(risp::RispValue::Int(1)),
///                std::sync::Arc::new(risp::RispValue::Cons(std::sync::Arc::new(risp::RispValue::Int(2)),
///                                         std::sync::Arc::new(risp::RispValue::Nil)))));
/// ```
/// Brackes enclose a Cons pair
/// ```
/// assert_eq!(risp::read_risp("[1 2]").unwrap()[0],
///            risp::RispValue::Cons(std::sync::Arc::new(risp::RispValue::Int(1)),
///                                  std::sync::Arc::new(risp::RispValue::Int(2))));
/// ```
/// Whitespace includes spaces, tabs and line-ends (LF and CR).
/// ```
/// risp::read_risp("(fn foo (x y)\n\r\t(+ x y))").unwrap();
/// ```
/// risp::read_risp() returns a vector containing all s-expressions in the input
/// ```
/// assert_eq!(risp::read_risp("1 two \"three\"").unwrap(), vec![risp::RispValue::Int(1),
///                                                               risp::RispValue::Symbol(String::from("two")),
///                                                               risp::RispValue::String(String::from("three"))]);
/// ```
pub fn read_risp<'a>(text: &'a str) -> Result<Vec<RispValue>, Error<Rule>> {
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
/// let mut ctx = risp::StaticContext::new();
/// let se1 = risp::read_risp("123").unwrap();
/// assert_eq!(risp::compile(se1[0].clone(), &mut ctx).unwrap(), se1[0]);
/// let se2 = risp::read_risp("123.456").unwrap();
/// assert_eq!(risp::compile(se2[0].clone(), &mut ctx).unwrap(), se2[0]);
/// let se3 = risp::read_risp("\"123\"").unwrap();
/// assert_eq!(risp::compile(se3[0].clone(), &mut ctx).unwrap(), se3[0]);
/// ```
///
/// Global symbols are replaced with their underlying values.
/// ```
/// let se = risp::read_risp("foo").unwrap();
/// let mut ctx = risp::StaticContext::new();
/// ctx.globals.insert(String::from("foo"), risp::RispValue::Int(2));
/// assert_eq!(risp::compile(se[0].clone(), &mut ctx).unwrap(), risp::RispValue::Int(2));
/// ```
/// However, if the symbol exists in the `locals` set, it is left as-is.
/// ```
/// let se = risp::read_risp("foo").unwrap();
/// let mut ctx = risp::StaticContext::new();
/// ctx.globals.insert(String::from("foo"), risp::RispValue::Int(2));
/// ctx.locals.insert(String::from("foo"));
/// assert_eq!(risp::compile(se[0].clone(), &mut ctx).unwrap(), se[0]);
/// ```
/// If a symbol does not exist, a compilation error is returned.
/// ```
/// let se = risp::read_risp("foo").unwrap();
/// let mut ctx = risp::StaticContext::new();
/// assert_eq!(risp::compile(se[0].clone(), &mut ctx), Err(risp::CompilationError::UndefinedSymbol(String::from("foo"))));
/// ```
pub fn compile(sexpr: RispValue, ctx: &mut StaticContext) -> Result<RispValue, CompilationError> {
    match sexpr {
        RispValue::Symbol(s) => {
            if ctx.locals.contains(&s) {
                Ok(RispValue::Symbol(s))
            } else {
                match ctx.globals.get(&s) {
                    Some(val) => Ok(val.clone()),
                    None => Err(CompilationError::UndefinedSymbol(s)),
                }
            }
        },
        _ => Ok(sexpr),
    }
}
