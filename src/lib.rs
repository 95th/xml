mod chars;
mod ident;
mod lit;
mod parser;

use chars::*;
use ident::identifier;
use lit::literal;
use parser::Parser;

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
            Ok((e, _)) | Err(e) => Err(format!("Unable to parse: {}", e)),
        }
    }
}

fn element() -> impl Parser<Output = Node> {
    whitespace_wrap(single_element().or(parent_element()).or(text_node())).boxed()
}

fn text_node() -> impl Parser<Output = Node> {
    any_char()
        .pred(|c| *c != '<')
        .one_or_more()
        .map(|chars| Node::Text(chars.into_iter().collect()))
}

fn parent_element() -> impl Parser<Output = Node> {
    open_element().and_then(|el| {
        element()
            .zero_or_more()
            .zip(close_element(el.name.clone()))
            .map(move |(children, _)| {
                let mut el = el.clone();
                el.children = children;
                Node::Element(el)
            })
    })
}

fn single_element() -> impl Parser<Output = Node> {
    element_start()
        .zip(any_space())
        .zip(literal("/>"))
        .map(|(((name, attrs), _), _)| {
            Node::Element(Element {
                name,
                attrs,
                children: vec![],
            })
        })
}

fn open_element() -> impl Parser<Output = Element> {
    element_start()
        .zip(any_space().zip(literal(">")))
        .map(|((name, attrs), _)| Element {
            name,
            attrs,
            children: vec![],
        })
}

fn close_element(expected_name: String) -> impl Parser<Output = String> {
    literal("</")
        .zip(identifier())
        .zip(literal(">"))
        .map(|((_, ident), _)| ident)
        .pred(move |name| name == &expected_name)
}

fn element_start() -> impl Parser<Output = (String, Vec<(String, String)>)> {
    literal("<")
        .zip(identifier())
        .zip(attributes())
        .map(|((_, ident), attrs)| (ident, attrs))
}

fn attributes() -> impl Parser<Output = Vec<(String, String)>> {
    one_or_more_space()
        .zip(attribute_pair())
        .map(|(_, attr)| attr)
        .zero_or_more()
}

fn attribute_pair() -> impl Parser<Output = (String, String)> {
    identifier()
        .zip(literal("="))
        .zip(quoted_string())
        .map(|((ident, _), string)| (ident, string))
}

fn escaped_char(quote: char) -> impl Parser<Output = char> {
    match_char('\\').and_then(move |_| match_char(quote).or(match_char('\\')))
}

fn quoted_string() -> impl Parser<Output = String> {
    match_char('"')
        .or(match_char('\''))
        .and_then(|opening_char| {
            escaped_char(opening_char)
                .or(any_char().pred(move |c| *c != opening_char && *c != '\\'))
                .zero_or_more()
                .zip(match_char(opening_char))
        })
        .map(|(chars, _)| chars.into_iter().collect())
}

fn whitespace_wrap<P: Parser>(parser: P) -> impl Parser<Output = P::Output> {
    any_space()
        .zip(parser)
        .zip(any_space())
        .map(|((_, output), _)| output)
}

#[test]
fn literal_parser() {
    let parse_joe = literal("Hello joe!");

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
        identifier().parse("i-am-an-identifier")
    );
    assert_eq!(
        Ok((" entirely an identifier", "not".to_string())),
        identifier().parse("not entirely an identifier")
    );
    assert_eq!(
        Err("!not at all an identifier"),
        identifier().parse("!not at all an identifier")
    );
}

#[test]
fn pair_combinator() {
    let tag_opener = literal("<").zip(identifier()).map(|(_, ident)| ident);
    assert_eq!(
        Ok(("/>", "my-first-element".to_string())),
        tag_opener.parse("<my-first-element/>")
    );
    assert_eq!(Err("oops"), tag_opener.parse("oops"));
    assert_eq!(Err("!oops"), tag_opener.parse("<!oops"));
}

#[test]
fn one_or_more_combinator() {
    let parser = literal("ha").one_or_more();
    assert_eq!(Ok(("", vec![(), (), ()])), parser.parse("hahaha"));
    assert_eq!(Err("ahah"), parser.parse("ahah"));
    assert_eq!(Err(""), parser.parse(""));
}

#[test]
fn zero_or_more_combinator() {
    let parser = literal("ha").zero_or_more();
    assert_eq!(Ok(("", vec![(), (), ()])), parser.parse("hahaha"));
    assert_eq!(Ok(("ahah", vec![])), parser.parse("ahah"));
    assert_eq!(Ok(("", vec![])), parser.parse(""));
}

#[test]
fn predicate_combinator() {
    let parser = any_char().pred(|c| *c == 'o');
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
