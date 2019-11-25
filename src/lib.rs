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

struct Map<P, F> {
    parser: P,
    f: F,
}

impl<P, F, T> Parser for Map<P, F>
where
    P: Parser,
    F: Fn(P::Output) -> T,
{
    type Output = T;

    fn parse<'a>(&self, input: &'a str) -> ParseResult<'a, Self::Output> {
        self.parser
            .parse(input)
            .map(|(rest, parsed)| (rest, (self.f)(parsed)))
    }
}

struct Predicate<P, F> {
    parser: P,
    predicate: F,
}

impl<P, F> Parser for Predicate<P, F>
where
    P: Parser,
    F: Fn(&P::Output) -> bool,
{
    type Output = P::Output;

    fn parse<'a>(&self, input: &'a str) -> ParseResult<'a, Self::Output> {
        if let Ok((rest, parsed)) = self.parser.parse(input) {
            if (self.predicate)(&parsed) {
                return Ok((rest, parsed));
            }
        }
        Err(input)
    }
}

struct AndThen<P, F> {
    parser: P,
    f: F,
}

impl<P, Q, F> Parser for AndThen<P, F>
where
    P: Parser,
    Q: Parser,
    F: Fn(P::Output) -> Q,
{
    type Output = Q::Output;

    fn parse<'a>(&self, input: &'a str) -> ParseResult<'a, Self::Output> {
        let (rest, parsed) = self.parser.parse(input)?;
        (self.f)(parsed).parse(rest)
    }
}

struct Zip<P, Q> {
    first: P,
    second: Q,
}

impl<P, Q> Parser for Zip<P, Q>
where
    P: Parser,
    Q: Parser,
{
    type Output = (P::Output, Q::Output);

    fn parse<'a>(&self, input: &'a str) -> ParseResult<'a, Self::Output> {
        let (rest, first) = self.first.parse(input)?;
        let (rest, second) = self.second.parse(rest)?;
        Ok((rest, (first, second)))
    }
}

trait Parser {
    type Output;

    fn parse<'a>(&self, input: &'a str) -> ParseResult<'a, Self::Output>;

    fn map<F, T>(self, f: F) -> Map<Self, F>
    where
        Self: Sized,
        F: Fn(Self::Output) -> T,
    {
        Map { parser: self, f }
    }

    fn pred<F>(self, predicate: F) -> Predicate<Self, F>
    where
        Self: Sized,
        F: Fn(&Self::Output) -> bool,
    {
        Predicate {
            parser: self,
            predicate,
        }
    }

    fn and_then<P, F>(self, f: F) -> AndThen<Self, F>
    where
        Self: Sized,
        F: Fn(Self::Output) -> P,
        P: Parser,
    {
        AndThen { parser: self, f }
    }

    fn zip<P>(self, other: P) -> Zip<Self, P>
    where
        Self: Sized,
        P: Parser,
    {
        Zip {
            first: self,
            second: other,
        }
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

impl<P, Q> Parser for Either<P, Q>
where
    P: Parser,
    Q: Parser<Output = P::Output>,
{
    type Output = P::Output;

    fn parse<'a>(&self, input: &'a str) -> ParseResult<'a, Self::Output> {
        self.first
            .parse(input)
            .or_else(|_| self.second.parse(input))
    }
}

struct ElementParser {
    parser: Box<dyn Parser<Output = Node>>,
}

impl ElementParser {
    fn new() -> Self {
        Self {
            parser: Box::new(whitespace_wrap(Either::new(
                single_element(),
                Either::new(parent_element(), text_node()),
            ))),
        }
    }
}

impl Parser for ElementParser {
    type Output = Node;

    fn parse<'a>(&self, input: &'a str) -> ParseResult<'a, Node> {
        self.parser.parse(input)
    }
}

fn element() -> ElementParser {
    ElementParser::new()
}

fn text_node() -> impl Parser<Output = Node> {
    OneOrMore::new(AnyChar.pred(|c| *c != '<')).map(|chars| Node::Text(chars.into_iter().collect()))
}

fn parent_element() -> impl Parser<Output = Node> {
    open_element().and_then(|el| {
        first(ZeroOrMore::new(element()), close_element(el.name.clone())).map(move |children| {
            let mut el = el.clone();
            el.children = children;
            Node::Element(el)
        })
    })
}

fn single_element() -> impl Parser<Output = Node> {
    first(element_start(), space0().zip(LiteralParser::new("/>"))).map(|(name, attrs)| {
        Node::Element(Element {
            name,
            attrs,
            children: vec![],
        })
    })
}

fn open_element() -> impl Parser<Output = Element> {
    first(element_start(), space0().zip(LiteralParser::new(">"))).map(|(name, attrs)| Element {
        name,
        attrs,
        children: vec![],
    })
}

fn close_element(expected_name: String) -> impl Parser<Output = String> {
    second(
        LiteralParser::new("</"),
        first(Identifier, LiteralParser::new(">")),
    )
    .pred(move |name| name == &expected_name)
}

fn element_start() -> impl Parser<Output = (String, Vec<(String, String)>)> {
    second(LiteralParser::new("<"), Identifier.zip(attributes()))
}

fn attributes() -> impl Parser<Output = Vec<(String, String)>> {
    ZeroOrMore::new(second(space1(), attribute_pair()))
}

fn attribute_pair() -> impl Parser<Output = (String, String)> {
    Identifier.zip(second(LiteralParser::new("="), quoted_string()))
}

struct LiteralParser {
    expected: &'static str,
}

impl LiteralParser {
    fn new(expected: &'static str) -> Self {
        Self { expected }
    }
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

struct AnyChar;

impl Parser for AnyChar {
    type Output = char;

    fn parse<'a>(&self, input: &'a str) -> ParseResult<'a, char> {
        match input.chars().next() {
            Some(next) => Ok((&input[next.len_utf8()..], next)),
            _ => Err(input),
        }
    }
}

fn match_char(expected: char) -> impl Parser<Output = char> {
    AnyChar.pred(move |c| *c == expected)
}

fn whitespace_char() -> impl Parser<Output = char> {
    AnyChar.pred(|c| c.is_whitespace())
}

fn space0() -> impl Parser<Output = Vec<char>> {
    ZeroOrMore::new(whitespace_char())
}

fn space1() -> impl Parser<Output = Vec<char>> {
    OneOrMore::new(whitespace_char())
}

fn escaped_char(quote: char) -> impl Parser<Output = char> {
    match_char('\\').and_then(move |_| Either::new(match_char(quote), match_char('\\')))
}

fn quoted_string() -> impl Parser<Output = String> {
    Either::new(match_char('"'), match_char('\''))
        .and_then(|opening_char| {
            first(
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

struct OneOrMore<P> {
    parser: P,
}

impl<P> OneOrMore<P> {
    fn new(parser: P) -> Self {
        Self { parser }
    }
}

impl<P: Parser> Parser for OneOrMore<P> {
    type Output = Vec<P::Output>;

    fn parse<'a>(&self, mut input: &'a str) -> ParseResult<'a, Self::Output> {
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

impl<P: Parser> Parser for ZeroOrMore<P> {
    type Output = Vec<P::Output>;

    fn parse<'a>(&self, mut input: &'a str) -> ParseResult<'a, Self::Output> {
        let mut result = Vec::new();

        while let Ok((rest, parsed)) = self.parser.parse(input) {
            input = rest;
            result.push(parsed);
        }

        Ok((input, result))
    }
}

fn first<P, Q>(first: P, second: Q) -> impl Parser<Output = P::Output>
where
    P: Parser,
    Q: Parser,
{
    first.zip(second).map(|(output, _)| output)
}

fn second<P, Q>(first: P, second: Q) -> impl Parser<Output = Q::Output>
where
    P: Parser,
    Q: Parser,
{
    first.zip(second).map(|(_, output)| output)
}

fn whitespace_wrap<P: Parser>(parser: P) -> impl Parser<Output = P::Output> {
    second(space0(), first(parser, space0()))
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
    let tag_opener = second(LiteralParser::new("<"), Identifier);
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
