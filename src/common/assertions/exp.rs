#![allow(dead_code)]

//! Small assertion-language parser.
//!
//! The analyzer accepts command-line or file-based assertions independently of
//! LLVM parsing. This module owns that language:
//!
//! ```text
//! name :: function => expression
//! ```
//!
//! `parse_cmd_line` synthesizes the `name ::` prefix for one-off CLI
//! assertions, while `parse_file` expects the full form.
//!
//! Operator precedence (highest to lowest):
//!   `* /`  →  `+ -`  →  `== > >= < <= & && | ||`  →  prefix `!` / `~`

use crate::common::errors::{ProgError, Result};
use std::io::BufRead;
use std::{fmt, fs};

// ── Public AST types ──────────────────────────────────────────────────────────

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Op {
    /// Arithmetic
    Plus,
    Minus,
    Div,
    Mult,
    /// Logical / relational
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

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Expr {
    Ident(String),
    Const(String),
    Binop(Box<Self>, Op, Box<Self>),
    Unop(Box<Self>),
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Statement {
    pub func: String,
    pub exp: Expr,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Assertion {
    pub stmt: Statement,
    pub name: String,
}

// ── Tokens ────────────────────────────────────────────────────────────────────

#[derive(Debug, Clone, PartialEq)]
enum Tok {
    Num(String),
    Ident(String),  // %name  — SSA / variable-style identifiers
    FIdent(String), // plain identifier — function and assertion names
    Plus,
    Minus,
    Star,
    Slash,
    And,
    Or,
    Not,
    Gt,
    Ge,
    Lt,
    Le,
    EqEq,
    Arrow, // =>
    Named, // ::
    LParen,
    RParen,
}

impl fmt::Display for Tok {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Tok::Num(s) | Tok::Ident(s) | Tok::FIdent(s) => write!(f, "{s}"),
            Tok::Plus => write!(f, "+"),
            Tok::Minus => write!(f, "-"),
            Tok::Star => write!(f, "*"),
            Tok::Slash => write!(f, "/"),
            Tok::And => write!(f, "&"),
            Tok::Or => write!(f, "|"),
            Tok::Not => write!(f, "!"),
            Tok::Gt => write!(f, ">"),
            Tok::Ge => write!(f, ">="),
            Tok::Lt => write!(f, "<"),
            Tok::Le => write!(f, "<="),
            Tok::EqEq => write!(f, "=="),
            Tok::Arrow => write!(f, "=>"),
            Tok::Named => write!(f, "::"),
            Tok::LParen => write!(f, "("),
            Tok::RParen => write!(f, ")"),
        }
    }
}

// ── Lexer ─────────────────────────────────────────────────────────────────────

fn lex(src: &str) -> std::result::Result<Vec<Tok>, String> {
    let chars: Vec<char> = src.chars().collect();
    let mut i = 0;
    let mut toks = Vec::new();
    while i < chars.len() {
        let c = chars[i];
        match c {
            _ if c.is_whitespace() => {
                i += 1;
            }
            '+' => {
                toks.push(Tok::Plus);
                i += 1;
            }
            '-' => {
                toks.push(Tok::Minus);
                i += 1;
            }
            '*' => {
                toks.push(Tok::Star);
                i += 1;
            }
            '/' => {
                toks.push(Tok::Slash);
                i += 1;
            }
            '(' => {
                toks.push(Tok::LParen);
                i += 1;
            }
            ')' => {
                toks.push(Tok::RParen);
                i += 1;
            }
            // ! and ~ are both logical negation
            '!' | '~' => {
                toks.push(Tok::Not);
                i += 1;
            }
            // & and && are both logical AND
            '&' => {
                if i + 1 < chars.len() && chars[i + 1] == '&' {
                    i += 2;
                } else {
                    i += 1;
                }
                toks.push(Tok::And);
            }
            // | and || are both logical OR
            '|' => {
                if i + 1 < chars.len() && chars[i + 1] == '|' {
                    i += 2;
                } else {
                    i += 1;
                }
                toks.push(Tok::Or);
            }
            '>' => {
                if i + 1 < chars.len() && chars[i + 1] == '=' {
                    toks.push(Tok::Ge);
                    i += 2;
                } else {
                    toks.push(Tok::Gt);
                    i += 1;
                }
            }
            '<' => {
                if i + 1 < chars.len() && chars[i + 1] == '=' {
                    toks.push(Tok::Le);
                    i += 2;
                } else {
                    toks.push(Tok::Lt);
                    i += 1;
                }
            }
            '=' => {
                if i + 1 < chars.len() && chars[i + 1] == '=' {
                    toks.push(Tok::EqEq);
                    i += 2;
                } else if i + 1 < chars.len() && chars[i + 1] == '>' {
                    toks.push(Tok::Arrow);
                    i += 2;
                } else {
                    return Err(format!("unexpected '=' at position {i}"));
                }
            }
            ':' => {
                if i + 1 < chars.len() && chars[i + 1] == ':' {
                    toks.push(Tok::Named);
                    i += 2;
                } else {
                    return Err(format!("unexpected ':' at position {i}"));
                }
            }
            // %name — SSA/variable-style identifiers
            '%' => {
                i += 1;
                let start = i;
                while i < chars.len() && (chars[i].is_alphanumeric() || chars[i] == '_') {
                    i += 1;
                }
                if i == start {
                    return Err("empty identifier after '%'".to_string());
                }
                let name: String = std::iter::once('%')
                    .chain(chars[start..i].iter().copied())
                    .collect();
                toks.push(Tok::Ident(name));
            }
            // plain identifier
            _ if c.is_alphabetic() || c == '_' => {
                let start = i;
                while i < chars.len() && (chars[i].is_alphanumeric() || chars[i] == '_') {
                    i += 1;
                }
                toks.push(Tok::FIdent(chars[start..i].iter().collect()));
            }
            // numeric literal (integer or decimal)
            _ if c.is_ascii_digit() => {
                let start = i;
                while i < chars.len() && chars[i].is_ascii_digit() {
                    i += 1;
                }
                if i + 1 < chars.len() && chars[i] == '.' && chars[i + 1].is_ascii_digit() {
                    i += 1;
                    while i < chars.len() && chars[i].is_ascii_digit() {
                        i += 1;
                    }
                }
                toks.push(Tok::Num(chars[start..i].iter().collect()));
            }
            _ => return Err(format!("unexpected character '{c}' at position {i}")),
        }
    }
    Ok(toks)
}

// ── Recursive-descent parser ──────────────────────────────────────────────────

struct Parser {
    tokens: Vec<Tok>,
    pos: usize,
}

impl Parser {
    fn new(tokens: Vec<Tok>) -> Self {
        Parser { tokens, pos: 0 }
    }

    fn peek(&self) -> Option<&Tok> {
        self.tokens.get(self.pos)
    }

    fn advance(&mut self) -> Option<Tok> {
        let tok = self.tokens.get(self.pos).cloned();
        if self.pos < self.tokens.len() {
            self.pos += 1;
        }
        tok
    }

    fn expect_fident(&mut self) -> std::result::Result<String, String> {
        match self.advance() {
            Some(Tok::FIdent(s)) => Ok(s),
            Some(t) => Err(format!("expected identifier, got '{t}'")),
            None => Err("expected identifier, got end of input".to_string()),
        }
    }

    fn expect_named(&mut self) -> std::result::Result<(), String> {
        match self.advance() {
            Some(Tok::Named) => Ok(()),
            Some(t) => Err(format!("expected '::', got '{t}'")),
            None => Err("expected '::', got end of input".to_string()),
        }
    }

    fn expect_arrow(&mut self) -> std::result::Result<(), String> {
        match self.advance() {
            Some(Tok::Arrow) => Ok(()),
            Some(t) => Err(format!("expected '=>', got '{t}'")),
            None => Err("expected '=>', got end of input".to_string()),
        }
    }

    fn expect_rparen(&mut self) -> std::result::Result<(), String> {
        match self.advance() {
            Some(Tok::RParen) => Ok(()),
            Some(t) => Err(format!("expected ')', got '{t}'")),
            None => Err("expected ')', got end of input".to_string()),
        }
    }

    fn parse_assertion(&mut self) -> std::result::Result<Assertion, String> {
        let name = self.expect_fident()?;
        self.expect_named()?;
        let stmt = self.parse_stmt()?;
        if let Some(t) = self.peek() {
            return Err(format!("unexpected token '{t}' after expression"));
        }
        Ok(Assertion { name, stmt })
    }

    fn parse_stmt(&mut self) -> std::result::Result<Statement, String> {
        let func = self.expect_fident()?;
        self.expect_arrow()?;
        let exp = self.parse_expr(0)?;
        Ok(Statement { func, exp })
    }

    /// Pratt-style expression parser.
    ///
    /// Binding powers — higher binds tighter:
    ///   `* /` → 10   `+ -` → 9   `== > >= < <= & |` → 8   prefix `!` → right-bp 7
    fn parse_expr(&mut self, min_bp: u8) -> std::result::Result<Expr, String> {
        let mut lhs = self.parse_prefix()?;
        loop {
            let (bp, op) = match self.peek() {
                Some(Tok::Star) => (10u8, Op::Mult),
                Some(Tok::Slash) => (10, Op::Div),
                Some(Tok::Plus) => (9, Op::Plus),
                Some(Tok::Minus) => (9, Op::Minus),
                Some(Tok::EqEq) => (8, Op::Eeq),
                Some(Tok::Gt) => (8, Op::Gt),
                Some(Tok::Ge) => (8, Op::Ge),
                Some(Tok::Lt) => (8, Op::Lt),
                Some(Tok::Le) => (8, Op::Le),
                Some(Tok::And) => (8, Op::LAnd),
                Some(Tok::Or) => (8, Op::LOr),
                _ => break,
            };
            if bp <= min_bp {
                break;
            }
            self.advance();
            let rhs = self.parse_expr(bp)?; // left-associative: same bp stops here next round
            lhs = Expr::Binop(Box::new(lhs), op, Box::new(rhs));
        }
        Ok(lhs)
    }

    fn parse_prefix(&mut self) -> std::result::Result<Expr, String> {
        if matches!(self.peek(), Some(Tok::Not)) {
            self.advance();
            let rhs = self.parse_expr(7)?;
            return Ok(Expr::Unop(Box::new(rhs)));
        }
        self.parse_atom()
    }

    fn parse_atom(&mut self) -> std::result::Result<Expr, String> {
        match self.advance() {
            Some(Tok::Num(s)) => Ok(Expr::Const(s)),
            Some(Tok::Ident(s)) => Ok(Expr::Ident(s)),
            // plain identifiers are accepted as Ident atoms (e.g. bare `true`/`false`)
            Some(Tok::FIdent(s)) => Ok(Expr::Ident(s)),
            Some(Tok::LParen) => {
                let e = self.parse_expr(0)?;
                self.expect_rparen()?;
                Ok(e)
            }
            Some(t) => Err(format!("expected expression atom, got '{t}'")),
            None => Err("unexpected end of input in expression".to_string()),
        }
    }
}

// ── Public parse functions ─────────────────────────────────────────────────────

fn parse_line(line: &str) -> std::result::Result<Assertion, String> {
    let tokens = lex(line)?;
    let mut parser = Parser::new(tokens);
    parser.parse_assertion()
}

pub fn parse_cmd_line(s: &str) -> Result<Assertion> {
    let contents = format!("cmdline :: {s}");
    parse_line(&contents).map_err(|e| ProgError::ParseError(format!("{s}: {e}")))
}

pub fn parse_file(f: &str) -> Result<Vec<Assertion>> {
    let handle = fs::File::open(f).map_err(Into::<ProgError>::into)?;
    let lines = std::io::BufReader::new(handle).lines();
    let mut err_cnt = 0;
    let mut results: Vec<Assertion> = vec![];
    for line_res in lines {
        let line = line_res?;
        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }
        match parse_line(trimmed) {
            Ok(assertion) => results.push(assertion),
            Err(e) => {
                eprintln!("parse error in {f}: {e}");
                err_cnt += 1;
            }
        }
    }
    if err_cnt > 0 {
        return Err(ProgError::ParseError(f.to_string()));
    }
    Ok(results)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_num() {
        let toks = lex("42").unwrap();
        assert_eq!(toks, vec![Tok::Num("42".to_string())]);
    }

    #[test]
    fn test_num2() {
        let toks = lex("42+5").unwrap();
        let mut p = Parser::new(toks);
        let expr = p.parse_expr(0).unwrap();
        assert_eq!(
            expr,
            Expr::Binop(
                Box::new(Expr::Const("42".to_string())),
                Op::Plus,
                Box::new(Expr::Const("5".to_string()))
            )
        );
    }

    #[test]
    fn test_stmt() {
        let stmt = "func_name => %abcd == 42 & %gcd == 40 + 8";
        let toks = lex(stmt).unwrap();
        let mut p = Parser::new(toks);
        assert!(p.parse_stmt().is_ok());
    }

    #[test]
    fn test_parse_cmd_line_roundtrip() {
        let a = parse_cmd_line("main => %x + 1 == 4").unwrap();
        assert_eq!(a.name, "cmdline");
        assert_eq!(a.stmt.func, "main");
        assert_eq!(
            a.stmt.exp,
            Expr::Binop(
                Box::new(Expr::Binop(
                    Box::new(Expr::Ident("%x".to_string())),
                    Op::Plus,
                    Box::new(Expr::Const("1".to_string()))
                )),
                Op::Eeq,
                Box::new(Expr::Const("4".to_string()))
            )
        );
    }

    #[test]
    fn test_negation() {
        let a = parse_cmd_line("main => !%flag").unwrap();
        assert!(matches!(a.stmt.exp, Expr::Unop(_)));
    }

    #[test]
    fn test_parens_precedence() {
        let toks = lex("(1 + 2) * 3").unwrap();
        let mut p = Parser::new(toks);
        let expr = p.parse_expr(0).unwrap();
        assert_eq!(
            expr,
            Expr::Binop(
                Box::new(Expr::Binop(
                    Box::new(Expr::Const("1".to_string())),
                    Op::Plus,
                    Box::new(Expr::Const("2".to_string()))
                )),
                Op::Mult,
                Box::new(Expr::Const("3".to_string()))
            )
        );
    }

    #[test]
    fn test_double_ampersand() {
        // && and & are both accepted and produce the same AST
        let a1 = parse_cmd_line("f => %x == 1 && %y == 2").unwrap();
        let a2 = parse_cmd_line("f => %x == 1 & %y == 2").unwrap();
        assert_eq!(a1.stmt.exp, a2.stmt.exp);
    }

    #[test]
    fn test_double_pipe() {
        let a1 = parse_cmd_line("f => %x == 1 || %y == 2").unwrap();
        let a2 = parse_cmd_line("f => %x == 1 | %y == 2").unwrap();
        assert_eq!(a1.stmt.exp, a2.stmt.exp);
    }
}
