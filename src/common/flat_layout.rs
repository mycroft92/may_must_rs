/// Flat address layout for `ptrtoint` / `inttoptr` instruction pairs.
///
/// Each named memory region gets a concrete, non-overlapping integer base
/// address.  The stride between consecutive regions is large enough to cover
/// all valid intra-region offsets, preventing false pointer equalities.
///
/// Encoding:
///   `ptrtoint(region, offset)` → `base(region) + offset`   (concrete i64)
///   `inttoptr(v)`              → `(region, v − base(region))`  when v is known
///
/// Regions that can't be resolved at analysis time (e.g., `inttoptr` of a
/// value loaded from memory) are left unbound — conservative, may produce
/// UNKNOWN but never unsound.
use std::collections::HashMap;

/// Number of integer slots reserved per region.  Any single region must fit
/// within this stride; the value is chosen to exceed practical struct/array
/// sizes in the benchmarks we target.
pub const FLAT_STRIDE: i64 = 4096;

/// Maps region names to their flat base addresses and supports inverse lookup.
pub struct FlatLayout {
    /// Ordered list of (region_name, base_address) for range-based lookup.
    ordered: Vec<(String, i64)>,
    /// Fast name → base lookup.
    index: HashMap<String, i64>,
}

impl FlatLayout {
    pub fn new() -> Self {
        Self {
            ordered: Vec::new(),
            index: HashMap::new(),
        }
    }

    /// Register `region` in the layout if not already present.
    /// Regions are assigned consecutive bases in registration order.
    pub fn add_region(&mut self, region: impl Into<String>) {
        let region = region.into();
        if self.index.contains_key(&region) {
            return;
        }
        let base = self.ordered.len() as i64 * FLAT_STRIDE;
        self.index.insert(region.clone(), base);
        self.ordered.push((region, base));
    }

    /// Base address for a known region; `None` if the region was never added.
    pub fn base_of(&self, region: &str) -> Option<i64> {
        self.index.get(region).copied()
    }

    /// Flat integer address for `(region, offset)`; `None` if region unknown.
    pub fn flat_addr(&self, region: &str, offset: i64) -> Option<i64> {
        self.base_of(region).map(|b| b + offset)
    }

    /// Recover `(region_name, intra-region offset)` from a flat address.
    /// Returns `None` if the address falls outside every registered region.
    pub fn region_at(&self, addr: i64) -> Option<(&str, i64)> {
        self.ordered
            .iter()
            .find(|(_, base)| addr >= *base && addr < *base + FLAT_STRIDE)
            .map(|(name, base)| (name.as_str(), addr - base))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn no_false_equality() {
        let mut layout = FlatLayout::new();
        layout.add_region("r0");
        layout.add_region("r1");
        layout.add_region("r2");
        // (r0, 3) and (r2, 1) must not collide
        assert_ne!(layout.flat_addr("r0", 3), layout.flat_addr("r2", 1),);
    }

    #[test]
    fn inverse_lookup() {
        let mut layout = FlatLayout::new();
        layout.add_region("stack0");
        layout.add_region("stack1");
        let addr = layout.flat_addr("stack1", 2).unwrap();
        let (region, offset) = layout.region_at(addr).unwrap();
        assert_eq!(region, "stack1");
        assert_eq!(offset, 2);
    }

    #[test]
    fn idempotent_add() {
        let mut layout = FlatLayout::new();
        layout.add_region("r0");
        layout.add_region("r0"); // second add is a no-op
        layout.add_region("r1");
        assert_eq!(layout.flat_addr("r1", 0), Some(FLAT_STRIDE));
    }

    #[test]
    fn unknown_region_returns_none() {
        let layout = FlatLayout::new();
        assert_eq!(layout.flat_addr("missing", 0), None);
        assert_eq!(layout.region_at(42), None);
    }
}

/// Try to evaluate `term` to a concrete flat address using previously resolved
/// integer variables in `flat_vars`.  Returns `None` when the term contains an
/// unresolved variable or a non-evaluable sub-expression.
pub fn eval_flat_addr(
    term: &crate::common::formula::Term,
    flat_vars: &HashMap<String, i64>,
) -> Option<i64> {
    use crate::common::formula::Term;
    match term {
        Term::Int(n) => Some(*n),
        Term::Var(v) => flat_vars.get(v.name()).copied(),
        Term::Add(a, b) => Some(eval_flat_addr(a, flat_vars)? + eval_flat_addr(b, flat_vars)?),
        Term::Sub(a, b) => Some(eval_flat_addr(a, flat_vars)? - eval_flat_addr(b, flat_vars)?),
        Term::Mul(a, b) => Some(eval_flat_addr(a, flat_vars)? * eval_flat_addr(b, flat_vars)?),
        _ => None,
    }
}
