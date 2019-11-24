use std::str::FromStr;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Element {
    name: String,
    attrs: Vec<(String, String)>,
    children: Vec<Element>,
}

impl FromStr for Element {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match element().parse(s) {
            Ok((_, elm)) => Ok(elm),
            Err(e) => Err(e.to_string()),
        }
    }
}

type ParseResult<'a, T> = Result<(&'a str, T), &'a str>;

trait Parser<'a, T> {
    fn parse(&self, input: &'a str) -> ParseResult<'a, T>;

    fn map<F, U>(self, f: F) -> BoxedParser<'a, U>
    where
        Self: 'a + Sized,
        F: 'a + Fn(T) -> U,
        T: 'a,
        U: 'a,
    {
        BoxedParser::new(map(self, f))
    }

    fn pred<F>(self, predicate: F) -> BoxedParser<'a, T>
    where
        Self: 'a + Sized,
        T: 'a,
        F: 'a + Fn(&T) -> bool,
    {
        BoxedParser::new(pred(self, predicate))
    }

    fn and_then<P, F, U>(self, f: F) -> BoxedParser<'a, U>
    where
        Self: 'a + Sized,
        T: 'a,
        F: 'a + Fn(T) -> P,
        P: 'a + Parser<'a, U>,
        U: 'a,
    {
        BoxedParser::new(and_then(self, f))
    }
}

pub struct BoxedParser<'a, T> {
    parser: Box<dyn Parser<'a, T> + 'a>,
}

impl<'a, T> BoxedParser<'a, T> {
    fn new<P>(parser: P) -> Self
    where
        P: Parser<'a, T> + 'a,
    {
        Self {
            parser: Box::new(parser),
        }
    }
}

impl<'a, T> Parser<'a, T> for BoxedParser<'a, T> {
    fn parse(&self, input: &'a str) -> ParseResult<'a, T> {
        self.parser.parse(input)
    }
}

impl<'a, F, T> Parser<'a, T> for F
where
    F: Fn(&'a str) -> ParseResult<'a, T>,
{
    fn parse(&self, input: &'a str) -> ParseResult<'a, T> {
        self(input)
    }
}

fn element<'a>() -> impl Parser<'a, Element> {
    whitespace_wrap(either(single_element(), parent_element()))
}

fn parent_element<'a>() -> impl Parser<'a, Element> {
    open_element().and_then(|el| {
        left(zero_or_more(element()), close_element(el.name.clone())).map(move |children| {
            let mut el = el.clone();
            el.children = children;
            el
        })
    })
}

fn single_element<'a>() -> impl Parser<'a, Element> {
    left(element_start(), pair(space0(), match_literal("/>"))).map(|(name, attrs)| Element {
        name,
        attrs,
        children: vec![],
    })
}

fn open_element<'a>() -> impl Parser<'a, Element> {
    left(element_start(), pair(space0(), match_literal(">"))).map(|(name, attrs)| Element {
        name,
        attrs,
        children: vec![],
    })
}

fn close_element<'a>(expected_name: String) -> impl Parser<'a, String> {
    right(match_literal("</"), left(identifier, match_literal(">")))
        .pred(move |name| name == &expected_name)
}

fn element_start<'a>() -> impl Parser<'a, (String, Vec<(String, String)>)> {
    right(match_literal("<"), pair(identifier, attributes()))
}

fn attributes<'a>() -> impl Parser<'a, Vec<(String, String)>> {
    zero_or_more(right(space1(), attribute_pair()))
}

fn attribute_pair<'a>() -> impl Parser<'a, (String, String)> {
    pair(identifier, right(match_literal("="), quoted_string()))
}

fn match_literal<'a>(expected: &'static str) -> impl Parser<'a, ()> {
    move |input: &'a str| match input.get(0..expected.len()) {
        Some(next) if next == expected => Ok((&input[next.len()..], ())),
        _ => Err(input),
    }
}

fn any_char(input: &str) -> ParseResult<char> {
    match input.chars().next() {
        Some(next) => Ok((&input[next.len_utf8()..], next)),
        _ => Err(input),
    }
}

fn whitespace_char<'a>() -> impl Parser<'a, char> {
    pred(any_char, |c| c.is_whitespace())
}

fn space0<'a>() -> impl Parser<'a, Vec<char>> {
    zero_or_more(whitespace_char())
}

fn space1<'a>() -> impl Parser<'a, Vec<char>> {
    one_or_more(whitespace_char())
}

fn quoted_string<'a>() -> impl Parser<'a, String> {
    right(
        match_literal("\""),
        left(
            zero_or_more(any_char.pred(|c| *c != '"')),
            match_literal("\""),
        ),
    )
    .map(|chars| chars.into_iter().collect())
}

fn identifier(input: &str) -> ParseResult<String> {
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

fn either<'a, P1, P2, A>(parser1: P1, parser2: P2) -> impl Parser<'a, A>
where
    P1: Parser<'a, A>,
    P2: Parser<'a, A>,
{
    move |input| parser1.parse(input).or_else(|_| parser2.parse(input))
}

fn pred<'a, P, A, F>(parser: P, predicate: F) -> impl Parser<'a, A>
where
    P: Parser<'a, A>,
    F: Fn(&A) -> bool,
{
    move |input| {
        if let Ok((rest, parsed)) = parser.parse(input) {
            if predicate(&parsed) {
                return Ok((rest, parsed));
            }
        }
        Err(input)
    }
}

fn one_or_more<'a, P, A>(parser: P) -> impl Parser<'a, Vec<A>>
where
    P: Parser<'a, A>,
{
    move |mut input| {
        let mut result = Vec::new();

        let (rest, parsed) = parser.parse(input)?;
        input = rest;
        result.push(parsed);

        while let Ok((rest, parsed)) = parser.parse(input) {
            input = rest;
            result.push(parsed);
        }

        Ok((input, result))
    }
}

fn zero_or_more<'a, P, A>(parser: P) -> impl Parser<'a, Vec<A>>
where
    P: Parser<'a, A>,
{
    move |mut input| {
        let mut result = Vec::new();

        while let Ok((rest, parsed)) = parser.parse(input) {
            input = rest;
            result.push(parsed);
        }

        Ok((input, result))
    }
}

fn pair<'a, P1, P2, R1, R2>(parser_1: P1, parser_2: P2) -> impl Parser<'a, (R1, R2)>
where
    P1: Parser<'a, R1>,
    P2: Parser<'a, R2>,
{
    move |input| {
        let (rest, parsed_1) = parser_1.parse(input)?;
        let (rest, parsed_2) = parser_2.parse(rest)?;
        Ok((rest, (parsed_1, parsed_2)))
    }
}

fn map<'a, P, F, A, B>(parser: P, map_fn: F) -> impl Parser<'a, B>
where
    P: Parser<'a, A>,
    F: Fn(A) -> B,
{
    move |input| {
        parser
            .parse(input)
            .map(|(rest, parsed)| (rest, map_fn(parsed)))
    }
}

fn and_then<'a, P, Q, F, A, B>(parser: P, f: F) -> impl Parser<'a, B>
where
    P: Parser<'a, A>,
    Q: Parser<'a, B>,
    F: Fn(A) -> Q,
{
    move |input| {
        let (rest, parsed) = parser.parse(input)?;
        f(parsed).parse(rest)
    }
}

fn left<'a, P1, P2, R1, R2>(parser_1: P1, parser_2: P2) -> impl Parser<'a, R1>
where
    P1: Parser<'a, R1>,
    P2: Parser<'a, R2>,
{
    map(pair(parser_1, parser_2), |(left, _right)| left)
}

fn right<'a, P1, P2, R1, R2>(parser_1: P1, parser_2: P2) -> impl Parser<'a, R2>
where
    P1: Parser<'a, R1>,
    P2: Parser<'a, R2>,
{
    map(pair(parser_1, parser_2), |(_left, right)| right)
}

fn whitespace_wrap<'a, P, A>(parser: P) -> impl Parser<'a, A>
where
    P: Parser<'a, A>,
{
    right(space0(), left(parser, space0()))
}

#[test]
fn literal_parser() {
    let parse_joe = match_literal("Hello joe!");

    assert_eq!(Ok(("", ())), parse_joe.parse("Hello joe!"));
    assert_eq!(
        Ok((" Hello Robert!", ())),
        parse_joe.parse("Hello joe! Hello Robert!")
    );
    assert_eq!(Err("Hello Mike!"), parse_joe.parse("Hello Mike!"));
}

#[test]
fn identifier_parser() {
    assert_eq!(
        Ok(("", "i-am-an-identifier".to_string())),
        identifier("i-am-an-identifier")
    );
    assert_eq!(
        Ok((" entirely an identifier", "not".to_string())),
        identifier("not entirely an identifier")
    );
    assert_eq!(
        Err("!not at all an identifier"),
        identifier("!not at all an identifier")
    );
}

#[test]
fn pair_combinator() {
    let tag_opener = right(match_literal("<"), identifier);
    assert_eq!(
        Ok(("/>", "my-first-element".to_string())),
        tag_opener.parse("<my-first-element/>")
    );
    assert_eq!(Err("oops"), tag_opener.parse("oops"));
    assert_eq!(Err("!oops"), tag_opener.parse("<!oops"));
}

#[test]
fn one_or_more_combinator() {
    let parser = one_or_more(match_literal("ha"));
    assert_eq!(Ok(("", vec![(), (), ()])), parser.parse("hahaha"));
    assert_eq!(Err("ahah"), parser.parse("ahah"));
    assert_eq!(Err(""), parser.parse(""));
}

#[test]
fn zero_or_more_combinator() {
    let parser = zero_or_more(match_literal("ha"));
    assert_eq!(Ok(("", vec![(), (), ()])), parser.parse("hahaha"));
    assert_eq!(Ok(("ahah", vec![])), parser.parse("ahah"));
    assert_eq!(Ok(("", vec![])), parser.parse(""));
}

#[test]
fn predicate_combinator() {
    let parser = pred(any_char, |c| *c == 'o');
    assert_eq!(Ok(("mg", 'o')), parser.parse("omg"));
    assert_eq!(Err("lol"), parser.parse("lol"));
}

#[test]
fn quoted_string_parser() {
    assert_eq!(
        Ok(("", "Hello Joe!".to_string())),
        quoted_string().parse("\"Hello Joe!\"")
    );
}

#[test]
fn attribute_parser() {
    assert_eq!(
        Ok((
            "",
            vec![
                ("one".to_string(), "1".to_string()),
                ("two".to_string(), "2".to_string())
            ]
        )),
        attributes().parse("    one=\"1\" two=\"2\"")
    );
}

#[test]
fn single_element_parser() {
    assert_eq!(
        Ok((
            "",
            Element {
                name: "div".to_string(),
                attrs: vec![("class".to_string(), "float".to_string())],
                children: vec![]
            }
        )),
        single_element().parse("<div class=\"float\"/>")
    );
    assert_eq!(
        Ok((
            "",
            Element {
                name: "div".to_string(),
                attrs: vec![("class".to_string(), "float".to_string())],
                children: vec![]
            }
        )),
        single_element().parse("<div class=\"float\" />")
    );
}

#[test]
fn xml_parser() {
    let doc = r#"
        <top label="Top">
            <semi-bottom label="Bottom"/>
            <middle>
                <bottom label="Another bottom"/>
            </middle>
        </top>"#;
    let parsed_doc = Element {
        name: "top".to_string(),
        attrs: vec![("label".to_string(), "Top".to_string())],
        children: vec![
            Element {
                name: "semi-bottom".to_string(),
                attrs: vec![("label".to_string(), "Bottom".to_string())],
                children: vec![],
            },
            Element {
                name: "middle".to_string(),
                attrs: vec![],
                children: vec![Element {
                    name: "bottom".to_string(),
                    attrs: vec![("label".to_string(), "Another bottom".to_string())],
                    children: vec![],
                }],
            },
        ],
    };
    assert_eq!(Ok(("", parsed_doc)), element().parse(doc));
}

#[test]
fn mismatched_closing_tag() {
    let doc = r#"
        <top>
            <bottom/>
        </middle>"#;
    assert_eq!(Err("</middle>"), element().parse(doc));
}
