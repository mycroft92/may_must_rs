use crate::errors::{ProgError, Result};
use ariadne::{sources, Color, Label, Report, ReportKind};
///Defines the type of assertions we check for witht he analysis
use chumsky::{input::BorrowInput, input::ValueInput, pratt::*, prelude::*};
use std::io::{BufRead, BufReader};
use std::{env, fmt, fs};

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
    Arrow,
    Named,
}

impl fmt::Display for Op {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Op::*;
        match self {
            Plus => write!(f, "+"),
            Minus => write!(f, "-"),
            Div => write!(f, "/"),
            Mult => write!(f, "*"),
            LAnd => write!(f, "&"),
            LOr => write!(f, "|"),
            LNot => write!(f, "!"),
            Gt => write!(f, ">"),
            Ge => write!(f, ">="),
            Lt => write!(f, "<"),
            Le => write!(f, "<="),
            Eeq => write!(f, "=="),
            Arrow => write!(f, "=>"),
            Named => write!(f, "::"),
        }
    }
}

type Spanned<T> = (T, SimpleSpan);

#[derive(Debug, Clone, Eq, PartialEq)]
enum Token<'src> {
    Num(&'src str),
    Ident(&'src str),
    FIdent(&'src str),
    Parens(Vec<Spanned<Self>>),
    //Operator(Op),
    /// Arithmetic
    TPlus,
    TMinus,
    TDiv,
    TMult,
    ///Logical
    TLAnd,
    TLOr,
    TLNot,
    TGt,
    TGe,
    TLt,
    TLe,
    TEeq,
    TArrow,
    TNamed,
}

impl fmt::Display for Token<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Token::*;
        match self {
            Num(x) => write!(f, "{x}"),
            Ident(x) => write!(f, "{x}"),
            FIdent(x) => write!(f, "{x}"),
            //Operator(op) => write!(f, " {op} "),
            Parens(_) => write!(f, "(...)"),
            TPlus => write!(f, "+"),
            TMinus => write!(f, "-"),
            TDiv => write!(f, "/"),
            TMult => write!(f, "*"),
            TLAnd => write!(f, "&"),
            TLOr => write!(f, "|"),
            TLNot => write!(f, "!"),
            TGt => write!(f, ">"),
            TGe => write!(f, ">="),
            TLt => write!(f, "<"),
            TLe => write!(f, "<="),
            TEeq => write!(f, "=="),
            TArrow => write!(f, "=>"),
            TNamed => write!(f, "::"),
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
enum Exp<'src> {
    Ident(&'src str),
    Const(&'src str),
    Binop(Box<Spanned<Exp<'src>>>, Op, Box<Spanned<Exp<'src>>>),
    Unop(Box<Spanned<Exp<'src>>>),
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Expr {
    Ident(String),
    Const(String),
    Binop(Box<Self>, Op, Box<Self>),
    Unop(Box<Self>),
}

#[derive(Debug, Clone, Eq, PartialEq)]
struct Stmt<'src> {
    func: &'src str,
    exp: Spanned<Exp<'src>>,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Statement {
    pub func: String,
    pub exp: Expr,
}

#[derive(Debug, Clone, Eq, PartialEq)]
struct Assert<'src> {
    stmt: Spanned<Stmt<'src>>,
    name: &'src str,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Assertion {
    pub stmt: Statement,
    pub name: String,
}

fn transpose_exp<'src>(s: Exp<'src>) -> Expr {
    match s {
        Exp::Ident(s) => Expr::Ident(String::from(s)),
        Exp::Const(s) => Expr::Const(String::from(s)),
        Exp::Binop(e1_, op, e2_) => {
            let (e1, _) = *e1_;
            let (e2, _) = *e2_;
            Expr::Binop(Box::new(transpose_exp(e1)), op, Box::new(transpose_exp(e2)))
        }
        Exp::Unop(e_) => {
            let (e, _) = *e_;
            Expr::Unop(Box::new(transpose_exp(e)))
        }
    }
}

fn transpose_stmt<'src>(s: Stmt<'src>) -> Statement {
    Statement {
        func: s.func.to_string(),
        exp: transpose_exp(s.exp.0),
    }
}

fn transpose<'src>(s: Assert<'src>) -> Assertion {
    Assertion {
        name: s.name.to_string(),
        stmt: transpose_stmt(s.stmt.0),
    }
}

fn converter<'src>(s: &'src str) -> Token<'_> {
    use Token::*;
    match s {
        "+" => TPlus,
        "-" => TMinus,
        "/" => TDiv,
        "*" => TMult,
        "&" => TLAnd,
        "|" => TLOr,
        "~" => TLNot,
        "!" => TLNot,
        ">" => TGt,
        "<" => TLt,
        ">=" => TGe,
        "<=" => TLe,
        "==" => TEeq,
        "::" => TNamed,
        "=>" => TArrow,
        _ => panic!("Wrong use of Op discovery func on {}", s),
    }
}

fn operator<'src>(
    s: &'src str,
) -> impl Parser<'src, &'src str, Token<'src>, extra::Err<Rich<'src, char, SimpleSpan>>> + Clone {
    just(s).to(converter(s))
}

fn lexer<'src>(
) -> impl Parser<'src, &'src str, Vec<Spanned<Token<'src>>>, extra::Err<Rich<'src, char, SimpleSpan>>>
{
    recursive(|token| {
        choice((
            // Keywords
            just('%')
                .then(text::ident().or(text::int(10)).repeated().at_least(1))
                .to_slice()
                .map(Token::Ident),
            text::ident().map(Token::FIdent),
            // Operators
            operator("=="),
            operator(">="),
            operator("<="),
            operator("+"),
            operator("-"),
            operator("*"),
            operator("/"),
            operator("&"),
            operator("|"),
            operator("!"),
            operator(">"),
            operator("<"),
            operator("=>"),
            operator("::"),
            // Numbers
            text::int(10)
                .then(just('.').then(text::digits(10)).or_not())
                .to_slice()
                .map(|s: &str| Token::Num(s)),
            token
                .repeated()
                .collect()
                .delimited_by(just('('), just(')'))
                .labelled("token tree")
                .as_context()
                .map(Token::Parens),
        ))
        .map_with(|t, e| (t, e.span()))
        .padded()
    })
    .repeated()
    .collect()
}

fn exp_parser<'tokens, 'src: 'tokens, I, M>(
    make_input: M,
) -> impl Parser<'tokens, I, Spanned<Exp<'src>>, extra::Err<Rich<'tokens, Token<'src>, SimpleSpan>>>
       + Clone
where
    I: ValueInput<'tokens, Token = Token<'src>, Span = SimpleSpan>
        + BorrowInput<'tokens, Token = Token<'src>, Span = SimpleSpan>,
    // Because this function is generic over the input type, we need the caller to tell us how to create a new input,
    // `I`, from a nested token tree. This function serves that purpose.
    M: Fn(SimpleSpan, &'tokens [Spanned<Token<'src>>]) -> I + Clone + 'src,
{
    use Exp::*;
    use Op::*;
    use Token::*;
    recursive(|expr| {
        let ident = select_ref! { Token::Ident(x) => Exp::Ident(x)};
        let number = select_ref! { Token::Num(x) => Exp::Const(x) };

        choice((
            ident.map_with(|expr, e| (expr, e.span())),
            number.map_with(|expr, e| (expr, e.span())), // ( x )
            expr.nested_in(select_ref! { Token::Parens(ts) = e => make_input(e.span(), ts) }),
        ))
        .pratt(vec![
            infix(left(10), just(TMult), |x, _, y, e| {
                (Binop(Box::new(x), Mult, Box::new(y)), e.span())
            })
            .boxed(),
            infix(left(10), just(TDiv), |x, _, y, e| {
                (Binop(Box::new(x), Div, Box::new(y)), e.span())
            })
            .boxed(),
            infix(left(9), just(TPlus), |x, _, y, e| {
                (Binop(Box::new(x), Plus, Box::new(y)), e.span())
            })
            .boxed(),
            infix(left(9), just(TMinus), |x, _, y, e| {
                (Binop(Box::new(x), Minus, Box::new(y)), e.span())
            })
            .boxed(),
            infix(left(8), just(TEeq), |x, _, y, e| {
                (Binop(Box::new(x), Eeq, Box::new(y)), e.span())
            })
            .boxed(),
            infix(left(8), just(TGt), |x, _, y, e| {
                (Binop(Box::new(x), Gt, Box::new(y)), e.span())
            })
            .boxed(),
            infix(left(8), just(TLt), |x, _, y, e| {
                (Binop(Box::new(x), Lt, Box::new(y)), e.span())
            })
            .boxed(),
            infix(left(8), just(TGe), |x, _, y, e| {
                (Binop(Box::new(x), Ge, Box::new(y)), e.span())
            })
            .boxed(),
            infix(left(8), just(TLe), |x, _, y, e| {
                (Binop(Box::new(x), Le, Box::new(y)), e.span())
            })
            .boxed(),
            infix(left(8), just(TLAnd), |x, _, y, e| {
                (Binop(Box::new(x), LAnd, Box::new(y)), e.span())
            })
            .boxed(),
            infix(left(8), just(TLOr), |x, _, y, e| {
                (Binop(Box::new(x), LOr, Box::new(y)), e.span())
            })
            .boxed(),
            prefix(7, just(TLNot), |_, x, e| (Unop(Box::new(x)), e.span())).boxed(),
        ])
        .labelled("expression")
        .as_context()
    })
}

fn stmt_parser<'tokens, 'src: 'tokens, I, M>(
    make_input: M,
) -> impl Parser<'tokens, I, Spanned<Stmt<'src>>, extra::Err<Rich<'tokens, Token<'src>, SimpleSpan>>>
where
    I: ValueInput<'tokens, Token = Token<'src>, Span = SimpleSpan>
        + BorrowInput<'tokens, Token = Token<'src>, Span = SimpleSpan>,
    // Because this function is generic over the input type, we need the caller to tell us how to create a new input,
    // `I`, from a nested token tree. This function serves that purpose.
    M: Fn(SimpleSpan, &'tokens [Spanned<Token<'src>>]) -> I + Clone + 'src,
{
    let ident = select! { Token::FIdent(ident) => ident }.labelled("identifier");
    //just(Token::Ident(_))
    ident
        //.map_with(|x, e| (x, e.span()))
        .then_ignore(just(Token::TArrow))
        .then(exp_parser(make_input))
        .map_with(|(func, exp), e| (Stmt { func, exp }, e.span()))
}

fn assert_parser<'tokens, 'src: 'tokens, I, M>(
    make_input: M,
) -> impl Parser<'tokens, I, Spanned<Assert<'src>>, extra::Err<Rich<'tokens, Token<'src>, SimpleSpan>>>
where
    I: ValueInput<'tokens, Token = Token<'src>, Span = SimpleSpan>
        + BorrowInput<'tokens, Token = Token<'src>, Span = SimpleSpan>,
    // Because this function is generic over the input type, we need the caller to tell us how to create a new input,
    // `I`, from a nested token tree. This function serves that purpose.
    M: Fn(SimpleSpan, &'tokens [Spanned<Token<'src>>]) -> I + Clone + 'src,
{
    let ident = select! { Token::FIdent(ident) => ident }.labelled("identifier");
    //just(Token::Ident(_))
    ident
        //.map_with(|x, e| (x, e.span()))
        .then_ignore(just(Token::TNamed))
        .then(stmt_parser(make_input))
        .map_with(|(func, exp), e| {
            (
                Assert {
                    name: func,
                    stmt: exp,
                },
                e.span(),
            )
        })
}

pub fn parse_cmd_line(s: &str) -> Result<Assertion> {
    let contents = "cmdline :: ".to_string() + s;
    let tokens = lexer().parse(&contents).into_result();
    match tokens {
        Err(e) => {
            parse_failure(&e[0], &contents);
            Err(ProgError::ParseError(s.to_string()))
        }
        Ok(toks) => {
            match assert_parser(make_input)
                .parse(make_input((0..contents.len()).into(), &toks))
                .into_result()
            {
                Err(e) => {
                    parse_failure(&e[0], &contents);
                    Err(ProgError::ParseError(s.to_string()))
                }
                Ok(assert) => Ok(transpose(assert.0)),
            }
        }
    }
}

pub fn parse_file(f: &str) -> Result<Vec<Assertion>> {
    let f_handle = fs::File::open(f).map_err(|e| Into::<ProgError>::into(e))?;
    let f_contents = std::io::BufReader::new(f_handle).lines();
    let mut err_cnt = 0;
    let mut results: Vec<Assertion> = vec![];
    for line_res in f_contents {
        let line = line_res?;
        let tokens = lexer().parse(&line).into_result();
        match tokens {
            Err(e) => {
                parse_failure(&e[0], &line);
                err_cnt = err_cnt + 1;
            }

            Ok(tok) => {
                match assert_parser(make_input)
                    .parse(make_input((0..line.len()).into(), &tok))
                    .into_result()
                {
                    Err(e) => {
                        parse_failure(&e[0], &line);
                        err_cnt = err_cnt + 1;
                    }
                    Ok(stmt) => {
                        results.push(transpose(stmt.0));
                    }
                }
            }
        }
    }
    if err_cnt > 0 {
        return Err(ProgError::ParseError(f.to_string()));
    }
    Ok(results)
}

fn failure_noret(
    msg: String,
    label: (String, SimpleSpan),
    extra_labels: impl IntoIterator<Item = (String, SimpleSpan)>,
    src: &str,
    fname: &'static str,
) -> ! {
    //let fname = "example";
    Report::build(ReportKind::Error, (fname, label.1.into_range()))
        .with_config(ariadne::Config::new().with_index_type(ariadne::IndexType::Byte))
        .with_message(&msg)
        .with_label(
            Label::new((fname, label.1.into_range()))
                .with_message(label.0)
                .with_color(Color::Red),
        )
        .with_labels(extra_labels.into_iter().map(|label2| {
            Label::new((fname, label2.1.into_range()))
                .with_message(label2.0)
                .with_color(Color::Yellow)
        }))
        .finish()
        .eprint(sources([(fname, src)]))
        .unwrap();
    std::process::exit(1)
}

fn parse_failure_noret(err: &Rich<impl fmt::Display>, src: &str, fname: &'static str) -> ! {
    failure_noret(
        err.reason().to_string(),
        (
            err.found()
                .map(|c| c.to_string())
                .unwrap_or_else(|| "end of input".to_string()),
            *err.span(),
        ),
        err.contexts()
            .map(|(l, s)| (format!("while parsing this {l}"), *s)),
        src,
        fname,
    )
}

fn failure<'a>(
    msg: String,
    label: (String, SimpleSpan),
    extra_labels: impl IntoIterator<Item = (String, SimpleSpan)>,
    src: &'a str,
) {
    Report::build(ReportKind::Error, ("Error", label.1.into_range()))
        .with_config(ariadne::Config::new().with_index_type(ariadne::IndexType::Byte))
        .with_message(&msg)
        .with_label(
            Label::new(("Error", label.1.into_range()))
                .with_message(label.0)
                .with_color(Color::Red),
        )
        .with_labels(extra_labels.into_iter().map(|label2| {
            Label::new(("Error", label2.1.into_range()))
                .with_message(label2.0)
                .with_color(Color::Yellow)
        }))
        .finish()
        .eprint(sources([("example", src)]))
        .unwrap();
}

fn parse_failure<'a>(err: &Rich<impl fmt::Display>, src: &'a str) {
    failure(
        err.reason().to_string(),
        (
            err.found()
                .map(|c| c.to_string())
                .unwrap_or_else(|| "end of input".to_string()),
            *err.span(),
        ),
        err.contexts()
            .map(|(l, s)| (format!("while parsing this {l}"), *s)),
        src,
    )
}

fn make_input<'src>(
    eoi: SimpleSpan,
    toks: &'src [Spanned<Token<'src>>],
) -> impl ValueInput<'src, Token = Token<'src>, Span = SimpleSpan>
       + BorrowInput<'src, Token = Token<'src>, Span = SimpleSpan> {
    toks.map(eoi, |(t, s)| (t, s))
}

#[cfg(test)]
mod tests {
    use crate::expressions::exp::*;
    #[test]
    fn test_num() {
        let num = String::from("42");
        match lexer().parse(&num).into_result() {
            Ok(ast) => {
                //println!("{:?}", ast);
                assert_eq!(Token::Num("42"), ast.get(0).unwrap().0);
            }
            Err(err) => println!("Error : {:?}", err),
        };
    }

    #[test]
    fn test_num2() {
        let num = String::from("42+5");
        let tokens = lexer()
            .parse(&num)
            .into_result()
            .unwrap_or_else(|errs| parse_failure_noret(&errs[0], &num, "test"));
        match exp_parser(make_input)
            .parse(make_input((0..num.len()).into(), &tokens))
            .into_result()
        {
            Ok(ast) => {
                //println!("{:?}", ast);
                let ast_ = transpose_exp(ast.0);
                assert_eq!(
                    Expr::Binop(
                        Box::new(Expr::Const("42".to_string())),
                        Op::Plus,
                        Box::new(Expr::Const("5".to_string()))
                    ),
                    ast_
                );
            }
            Err(err) => println!("Error : {:?}", err),
        };
    }

    #[test]
    fn test_stmt() {
        let stmt = String::from("func_name => %abcd == 42 & %gcd == 40 +8");
        let tokens = lexer()
            .parse(&stmt)
            .into_result()
            .unwrap_or_else(|errs| parse_failure_noret(&errs[0], &stmt, "test"));
        println!("Tokens: {:?}", tokens);
        match stmt_parser(make_input)
            .parse(make_input((0..stmt.len()).into(), &tokens))
            .into_result()
        {
            Ok(ast) => {
                println!("{:?}", ast);
                //assert_eq!(Exp::Const("42"), ast.0);
            }
            Err(err) => {
                println!("Tokens: {:?}", tokens);
                println!("Error : {:?}", err);
            }
        };
    }
}
