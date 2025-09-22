///Defines the type of assertions we check for witht he analysis
use chumsky::prelude::*;

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Op {
    /// Arithmetic
    Plus,
    Minus,
    Div,
    Mult,
    ///Logical
    LAnd,
    LOr,
    LNot,
    Gt,
    Ge,
    Lt,
    Le,
    Eeq,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Exp {
    Ident(String),
    Const(String),
    Binop(Box<Exp>, Op, Box<Exp>),
    Unop(Box<Exp>),
}

fn converter<'src>(s: &'src str) -> Op {
    match s {
        "+" => Op::Plus,
        "-" => Op::Minus,
        "/" => Op::Div,
        "*" => Op::Mult,
        "&" => Op::LAnd,
        "|" => Op::LOr,
        "~" => Op::LNot,
        "!" => Op::LNot,
        ">" => Op::Gt,
        "<" => Op::Lt,
        ">=" => Op::Ge,
        "<=" => Op::Le,
        "==" => Op::Eeq,
        _ => panic!("Wrong use of Op discovery func on {}", s),
    }
}

fn parse_expr<'src>() -> impl Parser<'src, &'src str, Exp> {
    let ident = text::ascii::ident().map(|s: &str| Exp::Ident(String::from(s)));

    let numbers = text::int(10).map(|s: &str| Exp::Const(String::from(s)));

    let atom = choice((ident, numbers)).padded();

    let op = |c| just(c).padded().map(|s: &str| converter(s));

    let product = atom.foldl(
        choice(((op("*"), op("/")))).then(atom).repeated(),
        |lhs, (op, rhs)| Exp::Binop(Box::new(lhs), op, Box::new(rhs)),
    );

    let sum = product.foldl(
        choice((op("+"), op("-"))).then(product).repeated(),
        |lhs, (op, rhs)| Exp::Binop(Box::new(lhs), op, Box::new(rhs)),
    );

    let logical = sum.foldl(
        choice((op(">"), op(">="), op("<"), op("<="), op("==")))
            .then(sum)
            .repeated(),
        |lhs, (op, rhs)| Exp::Binop(Box::new(lhs), op, Box::new(rhs)),
    );

    logical
}

#[cfg(test)]
mod tests {
    use crate::expressions::exp::*;
    #[test]
    fn test_num() {
        let num = String::from("42");
        match parse_expr().parse(&num).into_result() {
            Ok(ast) => {
                println!("{:?}", ast);
                assert_eq!(Exp::Const(String::from("42")), ast);
            }
            Err(err) => println!("Error : {:?}", err),
        };
    }
}
