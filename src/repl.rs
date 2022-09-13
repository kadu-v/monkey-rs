use crate::evaluator::evaluator::Evaluable;
use crate::lexer::lexer::Lexer;
use crate::object::environment::Env;
use crate::parser::parser::Parser;
use std::io;
use std::io::Write;

const PROMPT: &str = "monkey>";

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Repl {}

impl Repl {
    pub fn start() {
        let mut env = Env::new();

        loop {
            print!("{} ", PROMPT);
            io::stdout().flush().unwrap();

            let mut buffer = String::new();
            io::stdin()
                .read_line(&mut buffer)
                .expect("Woops!!, stdin is panic.");

            if buffer == ":q\n".to_string() {
                break;
            }

            let mut lex = Lexer::new(&buffer);
            let mut psr = Parser::new(&mut lex);
            match psr.parse_program() {
                Ok(prg) => match prg.eval(&mut env) {
                    Ok(obj) => {
                        println!("{}", obj)
                    }
                    Err(err) => err.do_error_report(&buffer),
                },
                Err(err) => {
                    err.do_error_report(&buffer);
                }
            };
        }
    }
}
