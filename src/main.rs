use monkey_rs::repl::Repl;

fn main() {
    let mut reader = std::io::stdin().lock();
    Repl::start(&mut reader);
}
