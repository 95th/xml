use std::marker::PhantomData;
use std::str::FromStr;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Node {
    Element(Element),
    Text(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Element {
    name: String,
    attrs: Vec<(String, String)>,
    children: Vec<Node>,
}

impl FromStr for Node {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match element().parse(s) {
            Ok(("", elm)) => Ok(elm),
            Ok((e, _)) => Err(format!("Unable to parse: {}", e)),
            Err(e) => Err(format!("Unable to parse: {}", e)),
        }
    }
}

type ParseResult<'a, T> = Result<(&'a str, T), &'a str>;

struct Map<P, T, F> {
    parser: P,
    f: F,
    marker: PhantomData<T>,
}

impl<'a, P, F, T, U> Parser<'a, U> for Map<P, T, F>
where
    P: Parser<'a, T>,
    F: Fn(T) -> U,
{
    fn parse(&self, input: &'a str) -> ParseResult<'a, U> {
        self.parser
            .parse(input)
            .map(|(rest, parsed)| (rest, (self.f)(parsed)))
    }
}

struct Predicate<P, F> {
    parser: P,
    predicate: F,
}

impl<'a, P, F, T> Parser<'a, T> for Predicate<P, F>
where
    P: Parser<'a, T>,
    F: Fn(&T) -> bool,
{
    fn parse(&self, input: &'a str) -> ParseResult<'a, T> {
        if let Ok((rest, parsed)) = self.parser.parse(input) {
            if (self.predicate)(&parsed) {
                return Ok((rest, parsed));
            }
        }
        Err(input)
    }
}

struct AndThen<P, T, F> {
    parser: P,
    f: F,
    marker: PhantomData<T>,
}

impl<'a, P, Q, F, T, U> Parser<'a, U> for AndThen<P, T, F>
where
    P: Parser<'a, T>,
    Q: Parser<'a, U>,
    F: Fn(T) -> Q,
{
    fn parse(&self, input: &'a str) -> ParseResult<'a, U> {
        let (rest, parsed) = self.parser.parse(input)?;
        (self.f)(parsed).parse(rest)
    }
}

trait Parser<'a, T> {
    fn parse(&self, input: &'a str) -> ParseResult<'a, T>;

    fn map<F, U>(self, f: F) -> Map<Self, T, F>
    where
        Self: Sized,
        F: Fn(T) -> U,
    {
        Map {
            parser: self,
            f,
            marker: PhantomData,
        }
    }

    fn pred<F>(self, predicate: F) -> Predicate<Self, F>
    where
        Self: Sized,
        F: Fn(&T) -> bool,
    {
        Predicate {
            parser: self,
            predicate,
        }
    }

    fn and_then<P, F, U>(self, f: F) -> AndThen<Self, T, F>
    where
        Self: Sized,
        F: Fn(T) -> P,
        P: Parser<'a, U>,
    {
        AndThen {
            parser: self,
            f,
            marker: PhantomData,
        }
    }
}

impl<'a, T, P: Parser<'a, T>> Parser<'a, T> for Box<P> {
    fn parse(&self, input: &'a str) -> ParseResult<'a, T> {
        (&**self).parse(input)
    }
}

struct Either<P, Q> {
    first: P,
    second: Q,
}

impl<P, Q> Either<P, Q> {
    fn new(first: P, second: Q) -> Self {
        Self { first, second }
    }
}

impl<'a, P, Q, T> Parser<'a, T> for Either<P, Q>
where
    P: Parser<'a, T>,
    Q: Parser<'a, T>,
{
    fn parse(&self, input: &'a str) -> ParseResult<'a, T> {
        self.first
            .parse(input)
            .or_else(|_| self.second.parse(input))
    }
}

struct ElementParser<'a> {
    parser: Box<dyn 'a + Parser<'a, Node>>,
}

impl ElementParser<'_> {
    fn new() -> Self {
        Self {
            parser: Box::new(whitespace_wrap(Either::new(
                single_element(),
                Either::new(parent_element(), text_node()),
            ))),
        }
    }
}

impl<'a> Parser<'a, Node> for ElementParser<'a> {
    fn parse(&self, input: &'a str) -> ParseResult<'a, Node> {
        self.parser.parse(input)
    }
}

fn element<'a>() -> ElementParser<'a> {
    ElementParser::new()
}

fn text_node<'a>() -> impl Parser<'a, Node> {
    OneOrMore::new(AnyChar.pred(|c| *c != '<')).map(|chars| Node::Text(chars.into_iter().collect()))
}

fn parent_element<'a>() -> impl Parser<'a, Node> {
    open_element().and_then(|el| {
        left(ZeroOrMore::new(element()), close_element(el.name.clone())).map(move |children| {
            let mut el = el.clone();
            el.children = children;
            Node::Element(el)
        })
    })
}

fn single_element<'a>() -> impl Parser<'a, Node> {
    left(
        element_start(),
        Pair::new(space0(), LiteralParser::new("/>")),
    )
    .map(|(name, attrs)| {
        Node::Element(Element {
            name,
            attrs,
            children: vec![],
        })
    })
}

fn open_element<'a>() -> impl Parser<'a, Element> {
    left(
        element_start(),
        Pair::new(space0(), LiteralParser::new(">")),
    )
    .map(|(name, attrs)| Element {
        name,
        attrs,
        children: vec![],
    })
}

fn close_element<'a>(expected_name: String) -> impl Parser<'a, String> {
    right(
        LiteralParser::new("</"),
        left(Identifier, LiteralParser::new(">")),
    )
    .pred(move |name| name == &expected_name)
}

fn element_start<'a>() -> impl Parser<'a, (String, Vec<(String, String)>)> {
    right(LiteralParser::new("<"), Pair::new(Identifier, attributes()))
}

fn attributes<'a>() -> impl Parser<'a, Vec<(String, String)>> {
    ZeroOrMore::new(right(space1(), attribute_pair()))
}

fn attribute_pair<'a>() -> impl Parser<'a, (String, String)> {
    Pair::new(Identifier, right(LiteralParser::new("="), quoted_string()))
}

struct LiteralParser {
    expected: &'static str,
}

impl LiteralParser {
    fn new(expected: &'static str) -> Self {
        Self { expected }
    }
}

impl<'a> Parser<'a, ()> for LiteralParser {
    fn parse(&self, input: &'a str) -> ParseResult<'a, ()> {
        match input.get(0..self.expected.len()) {
            Some(next) if next == self.expected => Ok((&input[next.len()..], ())),
            _ => Err(input),
        }
    }
}

struct AnyChar;

impl<'a> Parser<'a, char> for AnyChar {
    fn parse(&self, input: &'a str) -> ParseResult<'a, char> {
        match input.chars().next() {
            Some(next) => Ok((&input[next.len_utf8()..], next)),
            _ => Err(input),
        }
    }
}

fn match_char<'a>(expected: char) -> impl Parser<'a, char> {
    AnyChar.pred(move |c| *c == expected)
}

fn whitespace_char<'a>() -> impl Parser<'a, char> {
    AnyChar.pred(|c| c.is_whitespace())
}

fn space0<'a>() -> impl Parser<'a, Vec<char>> {
    ZeroOrMore::new(whitespace_char())
}

fn space1<'a>() -> impl Parser<'a, Vec<char>> {
    OneOrMore::new(whitespace_char())
}

fn escaped_char<'a>(quote: char) -> impl Parser<'a, char> {
    match_char('\\').and_then(move |_| Either::new(match_char(quote), match_char('\\')))
}

fn quoted_string<'a>() -> impl Parser<'a, String> {
    Either::new(match_char('"'), match_char('\''))
        .and_then(|opening_char| {
            left(
                ZeroOrMore::new(Either::new(
                    escaped_char(opening_char),
                    AnyChar.pred(move |c| *c != opening_char && *c != '\\'),
                )),
                match_char(opening_char),
            )
        })
        .map(|chars| chars.into_iter().collect())
}

struct Identifier;

impl<'a> Parser<'a, String> for Identifier {
    fn parse(&self, input: &'a str) -> ParseResult<'a, String> {
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

struct OneOrMore<P> {
    parser: P,
}

impl<P> OneOrMore<P> {
    fn new(parser: P) -> Self {
        Self { parser }
    }
}

impl<'a, P, T> Parser<'a, Vec<T>> for OneOrMore<P>
where
    P: Parser<'a, T>,
{
    fn parse(&self, mut input: &'a str) -> ParseResult<'a, Vec<T>> {
        let mut result = Vec::new();

        let (rest, parsed) = self.parser.parse(input)?;
        input = rest;
        result.push(parsed);

        while let Ok((rest, parsed)) = self.parser.parse(input) {
            input = rest;
            result.push(parsed);
        }

        Ok((input, result))
    }
}

struct ZeroOrMore<P> {
    parser: P,
}

impl<P> ZeroOrMore<P> {
    fn new(parser: P) -> Self {
        Self { parser }
    }
}

impl<'a, P, T> Parser<'a, Vec<T>> for ZeroOrMore<P>
where
    P: Parser<'a, T>,
{
    fn parse(&self, mut input: &'a str) -> ParseResult<'a, Vec<T>> {
        let mut result = Vec::new();

        while let Ok((rest, parsed)) = self.parser.parse(input) {
            input = rest;
            result.push(parsed);
        }

        Ok((input, result))
    }
}

struct Pair<P, Q> {
    first: P,
    second: Q,
}

impl<P, Q> Pair<P, Q> {
    fn new(first: P, second: Q) -> Self {
        Self { first, second }
    }
}

impl<'a, P, Q, T, U> Parser<'a, (T, U)> for Pair<P, Q>
where
    P: Parser<'a, T>,
    Q: Parser<'a, U>,
{
    fn parse(&self, input: &'a str) -> ParseResult<'a, (T, U)> {
        let (rest, first) = self.first.parse(input)?;
        let (rest, second) = self.second.parse(rest)?;
        Ok((rest, (first, second)))
    }
}

fn left<'a, P1, P2, R1, R2>(parser_1: P1, parser_2: P2) -> impl Parser<'a, R1>
where
    P1: Parser<'a, R1>,
    P2: Parser<'a, R2>,
{
    Pair::new(parser_1, parser_2).map(|(left, _right)| left)
}

fn right<'a, P1, P2, R1, R2>(parser_1: P1, parser_2: P2) -> impl Parser<'a, R2>
where
    P1: Parser<'a, R1>,
    P2: Parser<'a, R2>,
{
    Pair::new(parser_1, parser_2).map(|(_left, right)| right)
}

fn whitespace_wrap<'a, P, A>(parser: P) -> impl Parser<'a, A>
where
    P: Parser<'a, A>,
{
    right(space0(), left(parser, space0()))
}

#[test]
fn literal_parser() {
    let parse_joe = LiteralParser::new("Hello joe!");

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
        Identifier.parse("i-am-an-identifier")
    );
    assert_eq!(
        Ok((" entirely an identifier", "not".to_string())),
        Identifier.parse("not entirely an identifier")
    );
    assert_eq!(
        Err("!not at all an identifier"),
        Identifier.parse("!not at all an identifier")
    );
}

#[test]
fn pair_combinator() {
    let tag_opener = right(LiteralParser::new("<"), Identifier);
    assert_eq!(
        Ok(("/>", "my-first-element".to_string())),
        tag_opener.parse("<my-first-element/>")
    );
    assert_eq!(Err("oops"), tag_opener.parse("oops"));
    assert_eq!(Err("!oops"), tag_opener.parse("<!oops"));
}

#[test]
fn one_or_more_combinator() {
    let parser = OneOrMore::new(LiteralParser::new("ha"));
    assert_eq!(Ok(("", vec![(), (), ()])), parser.parse("hahaha"));
    assert_eq!(Err("ahah"), parser.parse("ahah"));
    assert_eq!(Err(""), parser.parse(""));
}

#[test]
fn zero_or_more_combinator() {
    let parser = ZeroOrMore::new(LiteralParser::new("ha"));
    assert_eq!(Ok(("", vec![(), (), ()])), parser.parse("hahaha"));
    assert_eq!(Ok(("ahah", vec![])), parser.parse("ahah"));
    assert_eq!(Ok(("", vec![])), parser.parse(""));
}

#[test]
fn predicate_combinator() {
    let parser = AnyChar.pred(|c| *c == 'o');
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
            Node::Element(Element {
                name: "div".to_string(),
                attrs: vec![("class".to_string(), "float".to_string())],
                children: vec![]
            })
        )),
        single_element().parse("<div class=\"float\"/>")
    );
    assert_eq!(
        Ok((
            "",
            Node::Element(Element {
                name: "div".to_string(),
                attrs: vec![("class".to_string(), "float".to_string())],
                children: vec![]
            })
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
    let parsed_doc = Node::Element(Element {
        name: "top".to_string(),
        attrs: vec![("label".to_string(), "Top".to_string())],
        children: vec![
            Node::Element(Element {
                name: "semi-bottom".to_string(),
                attrs: vec![("label".to_string(), "Bottom".to_string())],
                children: vec![],
            }),
            Node::Element(Element {
                name: "middle".to_string(),
                attrs: vec![],
                children: vec![Node::Element(Element {
                    name: "bottom".to_string(),
                    attrs: vec![("label".to_string(), "Another bottom".to_string())],
                    children: vec![],
                })],
            }),
        ],
    });
    assert_eq!(Ok(("", parsed_doc)), element().parse(doc));
}

#[test]
fn mismatched_closing_tag() {
    let doc = r#"<top><bottom/></middle>"#;
    assert_eq!(Err("<top><bottom/></middle>"), element().parse(doc));
}

#[test]
fn single_quoted_string() {
    let doc = r#"<top foo='hello'/>"#;
    let parsed_doc = Node::Element(Element {
        name: "top".to_string(),
        attrs: vec![("foo".to_string(), "hello".to_string())],
        children: vec![],
    });
    assert_eq!(Ok(("", parsed_doc)), element().parse(doc));
}

#[test]
fn mixed_quoted_string() {
    let doc = r#"<top foo="hello' bar='world"/>"#;
    let parsed_doc = Node::Element(Element {
        name: "top".to_string(),
        attrs: vec![("foo".to_string(), "hello' bar='world".to_string())],
        children: vec![],
    });
    assert_eq!(Ok(("", parsed_doc)), element().parse(doc));

    let doc = r#"<top foo='hello" bar="world'/>"#;
    let parsed_doc = Node::Element(Element {
        name: "top".to_string(),
        attrs: vec![("foo".to_string(), r#"hello" bar="world"#.to_string())],
        children: vec![],
    });
    assert_eq!(Ok(("", parsed_doc)), element().parse(doc));
}

#[test]
fn mismatched_quoted_string() {
    let doc = r#"<top foo="hello'/>"#;
    assert_eq!(Err(r#"<top foo="hello'/>"#), element().parse(doc));

    let doc = r#"<top foo='hello"/>"#;
    assert_eq!(Err(r#"<top foo='hello"/>"#), element().parse(doc));
}

#[test]
fn escaped_quoted_string_01() {
    let doc = r#"<top foo="hel\"lo"/>"#;
    let parsed_doc = Node::Element(Element {
        name: "top".to_string(),
        attrs: vec![("foo".to_string(), r#"hel"lo"#.to_string())],
        children: vec![],
    });
    assert_eq!(Ok(("", parsed_doc)), element().parse(doc));
}

#[test]
fn escaped_quoted_string_02() {
    let doc = r#"<top foo='hel\'lo'/>"#;
    let parsed_doc = Node::Element(Element {
        name: "top".to_string(),
        attrs: vec![("foo".to_string(), r#"hel'lo"#.to_string())],
        children: vec![],
    });
    assert_eq!(Ok(("", parsed_doc)), element().parse(doc));
}

#[test]
fn invalid_escaped_quoted_string() {
    let doc = r#"<top foo='hel\lo'/>"#;
    assert_eq!(Err(r#"<top foo='hel\lo'/>"#), element().parse(doc));
}

#[test]
fn escaped_backslash_quoted_string() {
    let doc = r#"<top foo='hel\\lo'/>"#;
    let parsed_doc = Node::Element(Element {
        name: "top".to_string(),
        attrs: vec![("foo".to_string(), r#"hel\lo"#.to_string())],
        children: vec![],
    });
    assert_eq!(Ok(("", parsed_doc)), element().parse(doc));
}

#[test]
fn text_node_test_01() {
    let doc = r#"<greet>welcome</greet>"#;
    let parsed_doc = Node::Element(Element {
        name: "greet".to_string(),
        attrs: vec![],
        children: vec![Node::Text("welcome".to_string())],
    });
    assert_eq!(Ok(("", parsed_doc)), element().parse(doc));
}
#[test]
fn text_node_test_02() {
    let doc = r#"<greet>welcome<foo/><bar></bar></greet>"#;
    let parsed_doc = Node::Element(Element {
        name: "greet".to_string(),
        attrs: vec![],
        children: vec![
            Node::Text("welcome".to_string()),
            Node::Element(Element {
                name: "foo".to_string(),
                attrs: vec![],
                children: vec![],
            }),
            Node::Element(Element {
                name: "bar".to_string(),
                attrs: vec![],
                children: vec![],
            }),
        ],
    });
    assert_eq!(Ok(("", parsed_doc)), element().parse(doc));
}
