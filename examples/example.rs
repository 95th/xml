use xml::Node;

fn main() {
    let e: Node = r#"
        <hello a="b" c="d">
            <foo>Hello world</foo>
        </hello>"#
        .parse()
        .unwrap();
    println!("{:#?}", e);
}
