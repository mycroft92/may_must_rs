#![allow(dead_code)]

use crate::common::assertions::exp::parse_cmd_line;
use crate::common::assertions::translation::{translate_assertion, SortSeeds};
use crate::common::formula::{Formula, Sort};
use thiserror::Error;

#[derive(Clone, Debug, Error, Eq, PartialEq)]
pub enum ParseError {
    #[error("syntax error: {0}")]
    Syntax(String),
    #[error("invalid quantifier range {lo}..{hi}")]
    InvalidQuantifierRange { lo: i64, hi: i64 },
    #[error("sort mismatch: {0}")]
    SortMismatch(String),
    #[error("non-boolean context: {0}")]
    NonBooleanContext(String),
}

pub fn parse_invariant(input: &str, seeds: &SortSeeds) -> Result<Formula, ParseError> {
    parse_invariant_seeds(input, seeds)
}

pub fn parse_invariant_seeds(input: &str, seeds: &SortSeeds) -> Result<Formula, ParseError> {
    let trimmed = input.trim();
    if trimmed.eq_ignore_ascii_case("true") {
        return Ok(Formula::True);
    }
    if trimmed.eq_ignore_ascii_case("false") {
        return Ok(Formula::False);
    }
    if let Some(expanded) = expand_quantifier(trimmed, seeds)? {
        return Ok(expanded);
    }

    let normalized = normalize_boolean_syntax(trimmed);
    let assertion = parse_cmd_line(&format!("dummy => {normalized}"))
        .map_err(|error| ParseError::Syntax(error.to_string()))?;
    translate_assertion(&assertion, seeds)
        .map(|translated| translated.stmt.predicate)
        .map_err(|error| ParseError::Syntax(error.to_string()))
}

fn expand_quantifier(input: &str, seeds: &SortSeeds) -> Result<Option<Formula>, ParseError> {
    let Some((quantifier, rest)) = input
        .strip_prefix("forall ")
        .map(|rest| ("forall", rest))
        .or_else(|| input.strip_prefix("exists ").map(|rest| ("exists", rest)))
    else {
        return Ok(None);
    };
    let Some((binder, body)) = rest.split_once('.') else {
        return Err(ParseError::Syntax(input.to_string()));
    };
    let Some((name, range)) = binder.trim().split_once(" in ") else {
        return Err(ParseError::Syntax(input.to_string()));
    };
    let Some((lo, hi)) = range.trim().split_once("..") else {
        return Err(ParseError::Syntax(input.to_string()));
    };
    let lo = lo
        .trim()
        .parse::<i64>()
        .map_err(|_| ParseError::Syntax(input.to_string()))?;
    let hi = hi
        .trim()
        .parse::<i64>()
        .map_err(|_| ParseError::Syntax(input.to_string()))?;
    if hi < lo {
        return Err(ParseError::InvalidQuantifierRange { lo, hi });
    }
    let mut formulas = Vec::new();
    for value in lo..hi {
        let instantiated = body.replace(name.trim(), &value.to_string());
        formulas.push(parse_invariant_seeds(&instantiated, seeds)?);
    }
    Ok(Some(if quantifier == "forall" {
        Formula::and_all(formulas)
    } else {
        Formula::or_all(formulas)
    }))
}

fn normalize_boolean_syntax(input: &str) -> String {
    let normalized = input
        .replace("&&", "&")
        .replace("||", "|")
        .replace("~", "!");
    if let Some((lhs, rhs)) = normalized.split_once("!=") {
        return format!("!({} == {})", lhs.trim(), rhs.trim());
    }
    if let Some((lhs, rhs)) = normalized.split_once("<=>") {
        return format!(
            "(({} => {}) & ({} => {}))",
            lhs.trim(),
            rhs.trim(),
            rhs.trim(),
            lhs.trim()
        );
    }
    normalized
}

pub fn default_bool_seed(name: impl Into<String>) -> (String, Sort) {
    (name.into(), Sort::Bool)
}
