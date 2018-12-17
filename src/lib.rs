extern crate pest;
#[macro_use]
extern crate pest_derive;

//use pest::{Parser};
use pest::error::Error;
use pest::Parser;
use pest::iterators::Pair;
use std::sync::Arc;

#[derive(Parser)]
#[grammar = "risp.pest"]
struct RispParser;

#[derive(Debug,PartialEq)]
pub enum RispValue {
    Int(i64),
    Float(f64),
    Symbol(String),
    String(String),
    Nil,
    Cons(Arc<RispValue>, Arc<RispValue>),
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

pub fn read_risp<'a>(text: &'a str) -> Result<Vec<RispValue>, Error<Rule>> {
    let parse_result = RispParser::parse(Rule::sexprs, text)?.next().unwrap();
    Ok(parse_result.into_inner().map(transform_tree).collect())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn reader_tests() {
        // Decimal integers are read as RispValue::Int(...)
        assert_eq!(read_risp("123").unwrap()[0], RispValue::Int(123));
        // Numbers with decimal points are considered RispValue::Float(...)
        assert_eq!(read_risp("3.14").unwrap()[0], RispValue::Float(3.14));
        // Symbols use a variety of characters, but they cannot start with a digit.
        assert_eq!(read_risp("foo-BAR123?<>!@$%^&*").unwrap()[0], RispValue::Symbol(String::from("foo-BAR123?<>!@$%^&*")));
        // String literals begin and end with quotation marks (").
        assert_eq!(read_risp("\"foo\"").unwrap()[0], RispValue::String(String::from("foo")));
        // Escaping is handled for ", \, n, r, and t.
        assert_eq!(read_risp("\"\\\"\\\\\\n\\r\\t\"").unwrap()[0], RispValue::String(String::from("\"\\\n\r\t")));
        // An empty list is parsed as Nil
        assert_eq!(read_risp("()").unwrap()[0], RispValue::Nil);
        // A list of elemens is a linked list of Cons
        assert_eq!(read_risp("(1 2)").unwrap()[0],
                   RispValue::Cons(
                       Arc::new(RispValue::Int(1)),
                       Arc::new(RispValue::Cons(Arc::new(RispValue::Int(2)),
                                                Arc::new(RispValue::Nil)))));
        // Brackes enclose a Cons pair
        assert_eq!(read_risp("[1 2]").unwrap()[0], RispValue::Cons(Arc::new(RispValue::Int(1)), Arc::new(RispValue::Int(2))));
        // Whitespace includes spaces, tabs and line-ends (LF and CR).
        read_risp("(fn foo (x y)\n\r\t(+ x y))").unwrap();
        // read_risp() returns a vector containing all sexpressions in the input
        assert_eq!(read_risp("1 two \"three\"").unwrap(), vec![RispValue::Int(1),
                                                               RispValue::Symbol(String::from("two")),
                                                               RispValue::String(String::from("three"))]);
    }
}
