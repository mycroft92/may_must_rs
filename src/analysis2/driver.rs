//! Thin orchestration skeleton for the paper-shaped rules.
//!
//! This is not wired to the CLI.  It exists to show where the deterministic
//! SMASH loop can live once the individual paper rules are filled in.

use crate::analysis2::oracle::{OracleResult, PredicateOracle};
use crate::analysis2::rules::{
    applicable_must_summary, applicable_not_may_summary, RuleApplication,
};
use crate::analysis2::summaries::{ReachabilityQuery, SummaryTable};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PaperAnswer {
    Must(RuleApplication),
    NotMay(RuleApplication),
    NeedsIntraproceduralAnalysis,
}

#[derive(Clone, Debug, Default)]
pub struct PaperDriver {
    summaries: SummaryTable,
}

impl PaperDriver {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn summaries(&self) -> &SummaryTable {
        &self.summaries
    }

    pub fn summaries_mut(&mut self) -> &mut SummaryTable {
        &mut self.summaries
    }

    /// Deterministic top-level order from the paper discussion:
    ///
    /// 1. reuse an applicable must summary;
    /// 2. reuse an applicable not-may summary;
    /// 3. otherwise run intraprocedural may/must analysis.
    pub fn answer_from_summaries<P>(
        &self,
        predicates: &P,
        query: &ReachabilityQuery,
    ) -> OracleResult<PaperAnswer>
    where
        P: PredicateOracle,
    {
        for summary in self.summaries.for_procedure(&query.procedure) {
            let application = applicable_must_summary(predicates, summary, query)?;
            if application.is_applied() {
                return Ok(PaperAnswer::Must(application));
            }
        }

        for summary in self.summaries.for_procedure(&query.procedure) {
            let application = applicable_not_may_summary(predicates, summary, query)?;
            if application.is_applied() {
                return Ok(PaperAnswer::NotMay(application));
            }
        }

        Ok(PaperAnswer::NeedsIntraproceduralAnalysis)
    }
}
