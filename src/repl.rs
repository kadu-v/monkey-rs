use crate::evaluator::evaluator::Evaluable;
use crate::lexer::lexer::Lexer;
use crate::object::environment::Env;
use crate::object::object::Object;
use crate::parser;
use crate::parser::parser::Parser;
use crate::{error::Error, object};
use std::io::BufRead;

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Repl {}

impl Repl {
    pub fn start(reader: &mut impl BufRead, //, writer: &mut impl BufWrite
    ) {
        let mut env = Env::new();

        loop {
            let mut buffer = String::new();
            let size = reader
                .read_line(&mut buffer)
                .expect("Woops!!, stdin is panic.");

            if buffer == ":q".to_string() {
                break;
            }

            let mut lex = Lexer::new(&buffer);
            let mut psr = Parser::new(&mut lex);
            match psr.parse_program() {
                Ok(prg) => match prg.eval(&mut env) {
                    Ok(obj) => {
                        println!("{:?}", obj)
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
