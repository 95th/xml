use crate::parser::{ParseResult, Parser};

pub struct LiteralParser {
    expected: &'static str,
}

pub fn literal(expected: &'static str) -> LiteralParser {
    LiteralParser { expected }
}

impl Parser for LiteralParser {
    type Output = ();

    fn parse<'a>(&self, input: &'a str) -> ParseResult<'a, ()> {
        match input.get(0..self.expected.len()) {
            Some(next) if next == self.expected => Ok((&input[next.len()..], ())),
            _ => Err(input),
        }
    }
}
