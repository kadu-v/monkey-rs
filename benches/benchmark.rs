use criterion::{criterion_group, criterion_main, Criterion};
use monkey_rs::error::Result;
use monkey_rs::evaluator::evaluator::*;
use monkey_rs::lexer::lexer::*;
use monkey_rs::object::environment::*;
use monkey_rs::object::object::*;
use monkey_rs::parser::parser::*;

pub fn fib_interp(n: usize) -> Result<Object> {
    let input = format!(
        "let fib = fn(x) {{ 
            if (x == 0) {{ 0 }} 
            else {{ 
                if (x == 1) {{ return 1; }} 
                else {{ fib(x - 1) + fib(x - 2) }} 
                }} 
            }}; 
            fib({})",
        n
    );

    let mut lex = Lexer::new(&input);
    let mut psr = Parser::new(&mut lex);
    let prg = psr.parse_program()?;
    let mut env = Env::new();
    prg.eval(&mut env)
}

fn bench_fib_interp(c: &mut Criterion) {
    c.bench_function("Fib(30)", |b| b.iter(|| fib_interp(10)));
}

criterion_group!(benches, bench_fib_interp);
criterion_main!(benches);
