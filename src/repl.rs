use crate::evaluator::evaluator::Evaluable;
use crate::lexer::lexer::Lexer;
use crate::object::environment::Env;
use crate::parser::parser::Parser;
use crate::{error::Error, object};
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

            // println!("Guess the number!"); // 数を当ててごらん

            // println!("Please input your guess."); // ほら、予想を入力してね
            let mut buffer = String::new();
            io::stdin()
                .read_line(&mut buffer)
                .expect("Woops!!, stdin is panic.");

            // println!("Guess the number!"); // 数を当ててごらん

            // println!("Please input your guess."); // ほら、予想を入力してね

            // let mut guess = String::new();

            // std::io::stdin()
            //     .read_line(&mut guess)
            //     .expect("Failed to read line"); // 行の読み込みに失敗しました

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
