//! Named may/must proof obligations.
//!
//! This module keeps the implementation close to the SMASH paper by giving the
//! summary-applicability obligations explicit names. It intentionally does not
//! own summary storage, worklist execution, LLVM transfer semantics, or raw Z3
//! operations.

#![allow(dead_code)]

use crate::analysis::domain::SummaryKind;
use crate::analysis::predicates::PredicateResult;
use crate::analysis::summary_store::{FunctionSummary, SmtQuery};
use std::fmt;

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum RuleName {
    MustPre,
    MustPost,
    NotMayPre,
    NotMayPost,
    ApplicableMustSummary,
    ApplicableNotMaySummary,
}

impl fmt::Display for RuleName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RuleName::MustPre => write!(f, "MustPre"),
            RuleName::MustPost => write!(f, "MustPost"),
            RuleName::NotMayPre => write!(f, "NotMayPre"),
            RuleName::NotMayPost => write!(f, "NotMayPost"),
            RuleName::ApplicableMustSummary => write!(f, "ApplicableMustSummary"),
            RuleName::ApplicableNotMaySummary => write!(f, "ApplicableNotMaySummary"),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RuleCheck {
    pub rule: RuleName,
    pub holds: bool,
    pub detail: String,
}

impl RuleCheck {
    pub fn holds(rule: RuleName, detail: impl Into<String>) -> Self {
        Self {
            rule,
            holds: true,
            detail: detail.into(),
        }
    }

    pub fn fails(rule: RuleName, detail: impl Into<String>) -> Self {
        Self {
            rule,
            holds: false,
            detail: detail.into(),
        }
    }
}

/// MustPre checks whether a cached must summary's witness precondition is
/// usable under the query's allowed precondition.
///
/// Current obligation:
///
/// ```text
/// summary.pre entails query.pre
/// ```
///
/// This direction mirrors the existing toy implementation and is intentionally
/// still marked for paper-rule review before user-visible SMT results depend on
/// it.
pub fn must_pre(summary: &FunctionSummary, query: &SmtQuery) -> PredicateResult<RuleCheck> {
    let holds = summary.pre.entails_in(&query.pre, &query.function)?;
    Ok(check_from_bool(
        RuleName::MustPre,
        holds,
        "summary.pre entails query.pre",
    ))
}

/// MustPost checks whether a cached must summary's postcondition can overlap
/// the query's requested target postcondition.
///
/// Current obligation:
///
/// ```text
/// summary.post intersects query.post
/// ```
pub fn must_post(summary: &FunctionSummary, query: &SmtQuery) -> PredicateResult<RuleCheck> {
    let holds = summary.post.intersects_in(&query.post, &query.function)?;
    Ok(check_from_bool(
        RuleName::MustPost,
        holds,
        "summary.post intersects query.post",
    ))
}

/// NotMayPre checks whether the query's input region is covered by the cached
/// not-may summary's input region.
///
/// Current obligation:
///
/// ```text
/// query.pre entails summary.pre
/// ```
pub fn not_may_pre(summary: &FunctionSummary, query: &SmtQuery) -> PredicateResult<RuleCheck> {
    let holds = query.pre.entails_in(&summary.pre, &query.function)?;
    Ok(check_from_bool(
        RuleName::NotMayPre,
        holds,
        "query.pre entails summary.pre",
    ))
}

/// NotMayPost checks whether the query's requested target is covered by the
/// cached not-may summary's excluded target.
///
/// Current obligation:
///
/// ```text
/// query.post entails summary.post
/// ```
pub fn not_may_post(summary: &FunctionSummary, query: &SmtQuery) -> PredicateResult<RuleCheck> {
    let holds = query.post.entails_in(&summary.post, &query.function)?;
    Ok(check_from_bool(
        RuleName::NotMayPost,
        holds,
        "query.post entails summary.post",
    ))
}

pub fn applicable_must_summary(
    summary: &FunctionSummary,
    query: &SmtQuery,
) -> PredicateResult<RuleCheck> {
    if !matches!(summary.kind, SummaryKind::Must) {
        return Ok(RuleCheck::fails(
            RuleName::ApplicableMustSummary,
            "summary kind is not Must",
        ));
    }

    if summary.function != query.function {
        return Ok(RuleCheck::fails(
            RuleName::ApplicableMustSummary,
            "summary function does not match query function",
        ));
    }

    if summary.target != query.target {
        return Ok(RuleCheck::fails(
            RuleName::ApplicableMustSummary,
            "summary target does not match query target",
        ));
    }

    let pre = must_pre(summary, query)?;
    if !pre.holds {
        return Ok(RuleCheck::fails(
            RuleName::ApplicableMustSummary,
            format!("{} failed: {}", pre.rule, pre.detail),
        ));
    }

    let post = must_post(summary, query)?;
    if !post.holds {
        return Ok(RuleCheck::fails(
            RuleName::ApplicableMustSummary,
            format!("{} failed: {}", post.rule, post.detail),
        ));
    }

    Ok(RuleCheck::holds(
        RuleName::ApplicableMustSummary,
        "MustPre and MustPost hold",
    ))
}

pub fn applicable_not_may_summary(
    summary: &FunctionSummary,
    query: &SmtQuery,
) -> PredicateResult<RuleCheck> {
    if !matches!(summary.kind, SummaryKind::NotMay) {
        return Ok(RuleCheck::fails(
            RuleName::ApplicableNotMaySummary,
            "summary kind is not NotMay",
        ));
    }

    if summary.function != query.function {
        return Ok(RuleCheck::fails(
            RuleName::ApplicableNotMaySummary,
            "summary function does not match query function",
        ));
    }

    if summary.target != query.target {
        return Ok(RuleCheck::fails(
            RuleName::ApplicableNotMaySummary,
            "summary target does not match query target",
        ));
    }

    let pre = not_may_pre(summary, query)?;
    if !pre.holds {
        return Ok(RuleCheck::fails(
            RuleName::ApplicableNotMaySummary,
            format!("{} failed: {}", pre.rule, pre.detail),
        ));
    }

    let post = not_may_post(summary, query)?;
    if !post.holds {
        return Ok(RuleCheck::fails(
            RuleName::ApplicableNotMaySummary,
            format!("{} failed: {}", post.rule, post.detail),
        ));
    }

    Ok(RuleCheck::holds(
        RuleName::ApplicableNotMaySummary,
        "NotMayPre and NotMayPost hold",
    ))
}

fn check_from_bool(rule: RuleName, holds: bool, detail: &'static str) -> RuleCheck {
    if holds {
        RuleCheck::holds(rule, detail)
    } else {
        RuleCheck::fails(rule, detail)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::predicates::{Formula, IntTerm};
    use crate::analysis::state::SummaryPhase;
    use crate::analysis::summary_store::SummaryTarget;

    fn param0() -> IntTerm {
        IntTerm::summary_param(SummaryPhase::Pre, 0)
    }

    #[test]
    fn must_pre_accepts_summary_pre_inside_query_pre() {
        let target = SummaryTarget::assertion("a0");
        let summary = FunctionSummary::must(
            "main",
            target.clone(),
            Formula::eq(param0(), IntTerm::int(7)),
            Formula::True,
            Formula::True,
            vec!["witness".to_string()],
        );
        let query = SmtQuery::new(
            "main",
            target,
            Formula::gt(param0(), IntTerm::int(0)),
            Formula::True,
        );

        let check = must_pre(&summary, &query).unwrap();
        assert_eq!(check.rule, RuleName::MustPre);
        assert!(check.holds);
    }

    #[test]
    fn must_post_accepts_overlapping_posts() {
        let target = SummaryTarget::Return;
        let ret = IntTerm::summary_return(SummaryPhase::Post);
        let summary = FunctionSummary::must(
            "inc",
            target.clone(),
            Formula::True,
            Formula::gt(ret.clone(), IntTerm::int(0)),
            Formula::True,
            vec!["ret".to_string()],
        );
        let query = SmtQuery::new(
            "inc",
            target,
            Formula::True,
            Formula::eq(ret, IntTerm::int(1)),
        );

        let check = must_post(&summary, &query).unwrap();
        assert_eq!(check.rule, RuleName::MustPost);
        assert!(check.holds);
    }

    #[test]
    fn not_may_pre_accepts_narrower_query_pre() {
        let target = SummaryTarget::assertion("a0");
        let summary = FunctionSummary::not_may(
            "checked",
            target.clone(),
            Formula::gt(param0(), IntTerm::int(0)),
            Formula::True,
            "positive inputs cannot violate a0",
        );
        let query = SmtQuery::new(
            "checked",
            target,
            Formula::gt(param0(), IntTerm::int(10)),
            Formula::True,
        );

        let check = not_may_pre(&summary, &query).unwrap();
        assert_eq!(check.rule, RuleName::NotMayPre);
        assert!(check.holds);
    }

    #[test]
    fn not_may_post_rejects_query_post_outside_summary_post() {
        let target = SummaryTarget::Return;
        let ret = IntTerm::summary_return(SummaryPhase::Post);
        let summary = FunctionSummary::not_may(
            "main",
            target.clone(),
            Formula::True,
            Formula::eq(ret.clone(), IntTerm::int(0)),
            "cannot return zero",
        );
        let query = SmtQuery::new(
            "main",
            target,
            Formula::True,
            Formula::gt(ret, IntTerm::int(0)),
        );

        let check = not_may_post(&summary, &query).unwrap();
        assert_eq!(check.rule, RuleName::NotMayPost);
        assert!(!check.holds);
    }

    #[test]
    fn applicable_must_summary_checks_kind_function_target_pre_and_post() {
        let target = SummaryTarget::assertion("a0");
        let summary = FunctionSummary::must(
            "main",
            target.clone(),
            Formula::True,
            Formula::True,
            Formula::True,
            vec!["witness".to_string()],
        );
        let query = SmtQuery::new("main", target, Formula::True, Formula::True);

        let check = applicable_must_summary(&summary, &query).unwrap();
        assert_eq!(check.rule, RuleName::ApplicableMustSummary);
        assert!(check.holds);
    }

    #[test]
    fn applicable_not_may_summary_rejects_target_mismatch() {
        let summary = FunctionSummary::not_may(
            "main",
            SummaryTarget::assertion("a0"),
            Formula::True,
            Formula::True,
            "safe",
        );
        let query = SmtQuery::new(
            "main",
            SummaryTarget::assertion("a1"),
            Formula::True,
            Formula::True,
        );

        let check = applicable_not_may_summary(&summary, &query).unwrap();
        assert_eq!(check.rule, RuleName::ApplicableNotMaySummary);
        assert!(!check.holds);
    }
}
