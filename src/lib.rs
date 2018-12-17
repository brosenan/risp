extern crate pest;
#[macro_use]
extern crate pest_derive;

//use pest::{Parser};
use pest::error::Error;
use pest::Parser;
use pest::iterators::Pair;

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
            if(c == '\\') {
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
        Rule::list => RispValue::Nil,
        Rule::EOI
            | Rule::decimal | Rule::symbol_start_char | Rule::chars | Rule::char
            | Rule::sexpr => unreachable!(),
    }
}

pub fn read_risp<'a>(text: &'a str) -> Result<RispValue, Error<Rule>> {
    let parse_result = RispParser::parse(Rule::sexpr, text)?.next().unwrap();
    Ok(transform_tree(parse_result))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn reader_tests() {
        // Decimal integers are read as RispValue::Int(...)
        assert_eq!(read_risp("123").unwrap(), RispValue::Int(123));
        // Numbers with decimal points are considered RispValue::Float(...)
        assert_eq!(read_risp("3.14").unwrap(), RispValue::Float(3.14));
        // Symbols use a variety of characters, but they cannot start with a digit.
        assert_eq!(read_risp("foo-BAR123?<>!@$%^&*").unwrap(), RispValue::Symbol(String::from("foo-BAR123?<>!@$%^&*")));
        // String literals begin and end with quotation marks (").
        assert_eq!(read_risp("\"foo\"").unwrap(), RispValue::String(String::from("foo")));
        // Escaping is handled for ", \, n, r, and t.
        assert_eq!(read_risp("\"\\\"\\\\\\n\\r\\t\"").unwrap(), RispValue::String(String::from("\"\\\n\r\t")));
        // An empty list is parsed as Nil
        assert_eq!(read_risp("()").unwrap(), RispValue::Nil);
    }
}
