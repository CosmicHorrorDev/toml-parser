fn main() {
    let path = std::env::args().nth(1).unwrap();
    let contents = std::fs::read_to_string(path).unwrap();
    println!("{:#?}", toml_parser::parse(&contents));
}
