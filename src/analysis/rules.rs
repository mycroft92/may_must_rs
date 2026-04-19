//! Explicit SMASH-style rule functions.
//!
//! This module is intentionally named around the paper rules rather than the
//! current executable implementation.  It should remain free of LLVM and Z3
//! details.  Those details enter through `PredicateOracle` and
//! `TransitionOracle`.
//!
//! Paper correspondence:
//!
//! ```text
//! must_post_edge            -> MUST-POST
//! not_may_pre_edge          -> NOTMAY-PRE
//! must_post_use_summary     -> MUST-POST-USE-SUMMARY
//! not_may_pre_use_summary   -> NOTMAY-PRE-USE-SUMMARY
//! applicable_*_summary      -> summary applicability checks
//! ```

use crate::analysis::cfg::PaperEdge;
use crate::analysis::formula::Predicate;
use crate::analysis::oracle::{OracleResult, PredicateOracle, TransitionOracle};
use crate::analysis::summaries::{ProcedureSummary, ReachabilityQuery, SummaryKind};
use crate::analysis::vocabulary::{EdgeId, RegionId};
use std::fmt;

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum RuleName {
    MustPost,
    NotMayPre,
    MustPostUseSummary,
    NotMayPreUseSummary,
    ApplicableMustSummary,
    ApplicableNotMaySummary,
    CreateMustSummary,
    CreateNotMaySummary,
}

impl fmt::Display for RuleName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RuleName::MustPost => write!(f, "MUST-POST"),
            RuleName::NotMayPre => write!(f, "NOTMAY-PRE"),
            RuleName::MustPostUseSummary => write!(f, "MUST-POST-USE-SUMMARY"),
            RuleName::NotMayPreUseSummary => write!(f, "NOTMAY-PRE-USE-SUMMARY"),
            RuleName::ApplicableMustSummary => write!(f, "APPLICABLE-MUST-SUMMARY"),
            RuleName::ApplicableNotMaySummary => write!(f, "APPLICABLE-NOTMAY-SUMMARY"),
            RuleName::CreateMustSummary => write!(f, "CREATE-MUST-SUMMARY"),
            RuleName::CreateNotMaySummary => write!(f, "CREATE-NOTMAY-SUMMARY"),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RuleApplication {
    Applied {
        rule: RuleName,
        conclusion: RuleConclusion,
        detail: String,
    },
    NotApplicable {
        rule: RuleName,
        reason: String,
    },
}

impl RuleApplication {
    pub fn applied(rule: RuleName, conclusion: RuleConclusion, detail: impl Into<String>) -> Self {
        Self::Applied {
            rule,
            conclusion,
            detail: detail.into(),
        }
    }

    pub fn not_applicable(rule: RuleName, reason: impl Into<String>) -> Self {
        Self::NotApplicable {
            rule,
            reason: reason.into(),
        }
    }

    pub fn is_applied(&self) -> bool {
        matches!(self, RuleApplication::Applied { .. })
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RuleConclusion {
    /// Add `theta` to `Omega_n2`.
    AddOmega {
        theta: Predicate,
    },
    /// Refine a source region with `beta` and add the not-may abstract edge.
    RefineAndAddMayEdge {
        beta: Predicate,
        keep_region: Predicate,
        reject_region: Predicate,
    },
    ReuseSummary {
        summary: ProcedureSummary,
    },
    CreateSummary {
        summary: ProcedureSummary,
    },
}

/// Paper `MUST-POST`.
///
/// Inputs correspond to:
///
/// - `edge.gamma` is `Gamma_e`;
/// - `omega_n1` is `Omega_n1`;
/// - `source_region` is `phi1`;
/// - `dest_region` is `phi2`.
pub fn must_post_edge<P, T>(
    predicates: &P,
    transitions: &T,
    edge: &PaperEdge,
    source_region: &Predicate,
    dest_region: &Predicate,
    omega_n1: &Predicate,
    omega_n2: &Predicate,
) -> OracleResult<RuleApplication>
where
    P: PredicateOracle,
    T: TransitionOracle,
{
    let source = Predicate::and([omega_n1.clone(), source_region.clone()]);
    if predicates.is_empty(&source)? {
        return Ok(RuleApplication::not_applicable(
            RuleName::MustPost,
            "Omega_n1 ∩ phi1 is empty",
        ));
    }

    if predicates.intersects(omega_n2, dest_region)? {
        return Ok(RuleApplication::not_applicable(
            RuleName::MustPost,
            "Omega_n2 already intersects phi2",
        ));
    }

    let theta = transitions.post_under_approx(edge, &source)?;
    if !predicates.intersects(dest_region, &theta)? {
        return Ok(RuleApplication::not_applicable(
            RuleName::MustPost,
            "phi2 does not intersect theta",
        ));
    }

    Ok(RuleApplication::applied(
        RuleName::MustPost,
        RuleConclusion::AddOmega { theta },
        "theta subset Post(Gamma_e, Omega_n1 ∩ phi1)",
    ))
}

/// Paper `NOTMAY-PRE`.
pub fn not_may_pre_edge<P, T>(
    predicates: &P,
    transitions: &T,
    edge: &PaperEdge,
    _source_region_id: RegionId,
    _dest_region_id: RegionId,
    source_region: &Predicate,
    dest_region: &Predicate,
    omega_n1: &Predicate,
    omega_n2: &Predicate,
) -> OracleResult<RuleApplication>
where
    P: PredicateOracle,
    T: TransitionOracle,
{
    let source = Predicate::and([omega_n1.clone(), source_region.clone()]);
    if predicates.is_empty(&source)? {
        return Ok(RuleApplication::not_applicable(
            RuleName::NotMayPre,
            "Omega_n1 ∩ phi1 is empty",
        ));
    }

    if predicates.intersects(omega_n2, dest_region)? {
        return Ok(RuleApplication::not_applicable(
            RuleName::NotMayPre,
            "Omega_n2 already intersects phi2",
        ));
    }

    let beta = transitions.pre_over_approx(edge, dest_region)?;
    if predicates.intersects(&beta, omega_n1)? {
        return Ok(RuleApplication::not_applicable(
            RuleName::NotMayPre,
            "beta intersects Omega_n1",
        ));
    }

    let keep_region = Predicate::and([source_region.clone(), beta.clone()]);
    let reject_region = Predicate::and([source_region.clone(), Predicate::not(beta.clone())]);
    Ok(RuleApplication::applied(
        RuleName::NotMayPre,
        RuleConclusion::RefineAndAddMayEdge {
            beta,
            keep_region,
            reject_region,
        },
        "beta over-approximates Pre(Gamma_e, phi2) and excludes Omega_n1",
    ))
}

/// Compositional `MUST-POST-USE-SUMMARY` for call edges.
pub fn must_post_use_summary<P>(
    predicates: &P,
    summary: &ProcedureSummary,
    dest_region: &Predicate,
    omega_n1: &Predicate,
    omega_n2: &Predicate,
) -> OracleResult<RuleApplication>
where
    P: PredicateOracle,
{
    if summary.kind != SummaryKind::Must {
        return Ok(RuleApplication::not_applicable(
            RuleName::MustPostUseSummary,
            "summary is not a must summary",
        ));
    }

    if !predicates.subset(&summary.pre, omega_n1)? {
        return Ok(RuleApplication::not_applicable(
            RuleName::MustPostUseSummary,
            "summary precondition is not covered by Omega_n1",
        ));
    }

    if predicates.intersects(omega_n2, dest_region)? {
        return Ok(RuleApplication::not_applicable(
            RuleName::MustPostUseSummary,
            "Omega_n2 already intersects phi2",
        ));
    }

    if !predicates.intersects(dest_region, &summary.post)? {
        return Ok(RuleApplication::not_applicable(
            RuleName::MustPostUseSummary,
            "summary post does not intersect phi2",
        ));
    }

    Ok(RuleApplication::applied(
        RuleName::MustPostUseSummary,
        RuleConclusion::AddOmega {
            theta: summary.post.clone(),
        },
        "callee must summary supplies theta",
    ))
}

/// Compositional `NOTMAY-PRE-USE-SUMMARY` for call edges.
pub fn not_may_pre_use_summary<P>(
    predicates: &P,
    summary: &ProcedureSummary,
    _edge_id: EdgeId,
    _source_region_id: RegionId,
    _dest_region_id: RegionId,
    source_region: &Predicate,
    dest_region: &Predicate,
    omega_n1: &Predicate,
) -> OracleResult<RuleApplication>
where
    P: PredicateOracle,
{
    if summary.kind != SummaryKind::NotMay {
        return Ok(RuleApplication::not_applicable(
            RuleName::NotMayPreUseSummary,
            "summary is not a not-may summary",
        ));
    }

    if !predicates.subset(dest_region, &summary.post)? {
        return Ok(RuleApplication::not_applicable(
            RuleName::NotMayPreUseSummary,
            "phi2 is not covered by summary postcondition",
        ));
    }

    let theta = summary.pre.clone();
    if !predicates.is_empty(&Predicate::and([
        Predicate::not(theta.clone()),
        omega_n1.clone(),
    ]))? {
        return Ok(RuleApplication::not_applicable(
            RuleName::NotMayPreUseSummary,
            "not theta intersects Omega_n1",
        ));
    }

    Ok(RuleApplication::applied(
        RuleName::NotMayPreUseSummary,
        RuleConclusion::RefineAndAddMayEdge {
            beta: theta.clone(),
            keep_region: Predicate::and([source_region.clone(), theta.clone()]),
            reject_region: Predicate::and([source_region.clone(), Predicate::not(theta)]),
        },
        "not-may summary supplies the preimage-side splitter",
    ))
}

pub fn applicable_must_summary<P>(
    predicates: &P,
    summary: &ProcedureSummary,
    query: &ReachabilityQuery,
) -> OracleResult<RuleApplication>
where
    P: PredicateOracle,
{
    if summary.kind != SummaryKind::Must {
        return Ok(RuleApplication::not_applicable(
            RuleName::ApplicableMustSummary,
            "summary is not must",
        ));
    }
    if summary.procedure != query.procedure {
        return Ok(RuleApplication::not_applicable(
            RuleName::ApplicableMustSummary,
            "procedure mismatch",
        ));
    }
    if !predicates.intersects(&summary.pre, &query.pre)? {
        return Ok(RuleApplication::not_applicable(
            RuleName::ApplicableMustSummary,
            "summary pre does not intersect query pre",
        ));
    }
    if !predicates.intersects(&summary.post, &query.post)? {
        return Ok(RuleApplication::not_applicable(
            RuleName::ApplicableMustSummary,
            "summary post does not intersect query post",
        ));
    }
    Ok(RuleApplication::applied(
        RuleName::ApplicableMustSummary,
        RuleConclusion::ReuseSummary {
            summary: summary.clone(),
        },
        "must summary overlaps query pre/post",
    ))
}

pub fn applicable_not_may_summary<P>(
    predicates: &P,
    summary: &ProcedureSummary,
    query: &ReachabilityQuery,
) -> OracleResult<RuleApplication>
where
    P: PredicateOracle,
{
    if summary.kind != SummaryKind::NotMay {
        return Ok(RuleApplication::not_applicable(
            RuleName::ApplicableNotMaySummary,
            "summary is not not-may",
        ));
    }
    if summary.procedure != query.procedure {
        return Ok(RuleApplication::not_applicable(
            RuleName::ApplicableNotMaySummary,
            "procedure mismatch",
        ));
    }
    if !predicates.subset(&query.pre, &summary.pre)? {
        return Ok(RuleApplication::not_applicable(
            RuleName::ApplicableNotMaySummary,
            "query pre is not covered by summary pre",
        ));
    }
    if !predicates.subset(&query.post, &summary.post)? {
        return Ok(RuleApplication::not_applicable(
            RuleName::ApplicableNotMaySummary,
            "query post is not covered by summary post",
        ));
    }
    Ok(RuleApplication::applied(
        RuleName::ApplicableNotMaySummary,
        RuleConclusion::ReuseSummary {
            summary: summary.clone(),
        },
        "not-may summary covers query pre/post",
    ))
}

pub fn create_must_summary(
    procedure: impl Into<crate::analysis::vocabulary::ProcedureName>,
    pre: Predicate,
    post: Predicate,
    witness: impl Into<String>,
) -> RuleApplication {
    RuleApplication::applied(
        RuleName::CreateMustSummary,
        RuleConclusion::CreateSummary {
            summary: ProcedureSummary::must(procedure, pre, post, witness),
        },
        "must analysis found a witness",
    )
}

pub fn create_not_may_summary(
    procedure: impl Into<crate::analysis::vocabulary::ProcedureName>,
    pre: Predicate,
    post: Predicate,
    proof: impl Into<String>,
) -> RuleApplication {
    RuleApplication::applied(
        RuleName::CreateNotMaySummary,
        RuleConclusion::CreateSummary {
            summary: ProcedureSummary::not_may(procedure, pre, post, proof),
        },
        "may analysis proved no target state is reachable",
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::cfg::PaperEdge;
    use crate::analysis::oracle::SyntacticOracle;
    use crate::analysis::vocabulary::{EdgeId, NodeId};

    #[test]
    fn must_post_uses_gamma_edge_to_produce_theta() {
        let oracle = SyntacticOracle;
        let edge = PaperEdge::local(
            EdgeId(0),
            NodeId(0),
            NodeId(1),
            Predicate::atom("Gamma_e"),
            Some(Predicate::atom("theta")),
            None,
        );

        let result = must_post_edge(
            &oracle,
            &oracle,
            &edge,
            &Predicate::atom("phi1"),
            &Predicate::atom("theta"),
            &Predicate::atom("Omega_n1"),
            &Predicate::False,
        )
        .unwrap();

        assert!(result.is_applied());
        assert!(matches!(
            result,
            RuleApplication::Applied {
                conclusion: RuleConclusion::AddOmega { .. },
                ..
            }
        ));
    }

    #[test]
    fn not_may_summary_covers_narrower_query() {
        let oracle = SyntacticOracle;
        let summary =
            ProcedureSummary::not_may("P", Predicate::True, Predicate::atom("error"), "proof");
        let query =
            ReachabilityQuery::new("P", Predicate::atom("x == 0"), Predicate::atom("error"));

        let result = applicable_not_may_summary(&oracle, &summary, &query).unwrap();

        assert!(result.is_applied());
    }
}
