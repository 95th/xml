use crate::parser::{ParseResult, Parser};

pub struct AnyChar {
    _priv: (),
}

pub fn any_char() -> AnyChar {
    AnyChar { _priv: () }
}

impl Parser for AnyChar {
    type Output = char;

    fn parse<'a>(&self, input: &'a str) -> ParseResult<'a, char> {
        match input.chars().next() {
            Some(next) => Ok((&input[next.len_utf8()..], next)),
            _ => Err(input),
        }
    }
}

pub fn match_char(expected: char) -> impl Parser<Output = char> {
    any_char().pred(move |c| *c == expected)
}

pub fn any_space() -> impl Parser<Output = Vec<char>> {
    whitespace_char().zero_or_more()
}

pub fn one_or_more_space() -> impl Parser<Output = Vec<char>> {
    whitespace_char().one_or_more()
}

fn whitespace_char() -> impl Parser<Output = char> {
    any_char().pred(|c| c.is_whitespace())
}
