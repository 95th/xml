use xml::Element;

fn main() {
    let e: Element = r#"<hello a="b" c="d"><foo/><foo></foo><hello a="b" c="d"><hello a="b" c="d"><foo/><foo></foo></hello><foo/><foo></foo><hello a="b" c="d"><foo/><foo></foo></hello></hello></hello>"#.parse().unwrap();
    println!("{:?}", e);
}
