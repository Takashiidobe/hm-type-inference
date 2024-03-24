use std::error::Error;
use std::io;
use std::io::Write;

use hm_inference::inference::*;
use hm_inference::types::*;

// first, tokenize the input
// then parse it into an AST
// then generate the definitions
// create an instance of an interpreter to handle variables

pub enum Token {
    Number(i64),
    Op(TokenOp),
    Keyword(Keyword),
    Bool(bool),
}

pub enum TokenOp {
    Plus,
    Eq,
}

pub enum Keyword {
    If,
    Else,
    Fn,
}

fn main() -> Result<(), Box<dyn Error>> {
    let mut line = String::default();
    loop {
        print!("> ");
        io::stdout().flush()?;

        if let Err(e) = io::stdin().read_line(&mut line) {
            eprintln!("{}", e);
            break Ok(());
        }

        print!("{line}");
        io::stdout().flush()?;
    }
}
