use crate::parser::{ParseResult, Parser};

pub struct Identifier {
    _priv: (),
}

pub fn identifier() -> Identifier {
    Identifier { _priv: () }
}

impl Parser for Identifier {
    type Output = String;

    fn parse<'a>(&self, input: &'a str) -> ParseResult<'a, String> {
        let mut matched = String::new();
        let mut chars = input.chars();

        match chars.next() {
            Some(next) if next.is_alphabetic() => matched.push(next),
            _ => return Err(input),
        }

        while let Some(next) = chars.next() {
            if next.is_alphanumeric() || next == '-' {
                matched.push(next);
            } else {
                break;
            }
        }

        let next_idx = matched.len();
        Ok((&input[next_idx..], matched))
    }
}
