//! LLVM call-boundary projection helpers for interprocedural queries.
//!
//! This module owns the call-site projection/instantiation transforms used to
//! build callee queries from caller-side obligations. Keeping this in
//! `analysis` (instead of CLI code) makes the behavior reusable and auditable
//! in one place.

use crate::analysis::formula::{
    collect_predicate_symbols, looks_like_memory_symbol, substitute_predicate_symbols, Predicate,
};
use crate::analysis::llvm_adapter::{LlvmEdgeMetadata, LlvmEdgeRegistry};
use crate::analysis::summaries::ReachabilityQuery;
use crate::analysis::vocabulary::{EdgeId, ProcedureName};
use std::collections::{BTreeMap, BTreeSet};

pub fn project_call_query(
    caller: &ProcedureName,
    callee: &ProcedureName,
    call_edge: EdgeId,
    call_metadata: &LlvmEdgeMetadata,
    caller_registry: &LlvmEdgeRegistry,
    callee_parameters: &[String],
    omega_n1: &Predicate,
    source_region: &Predicate,
    dest_region: &Predicate,
) -> ReachabilityQuery {
    let shared = collect_shared_symbols(call_metadata, caller_registry);
    let call_pre = project_predicate(
        &Predicate::and([omega_n1.clone(), source_region.clone()]),
        &shared,
    );
    let projected_post = project_predicate(dest_region, &shared);
    // APPROX_HEAVY: When projection collapses post to `true`, inject a
    // synthetic return-boundary target instead of semantic call/return demand.
    let call_post = if projected_post == Predicate::True {
        fallback_call_return_post(callee)
    } else {
        projected_post
    };
    let (call_pre, call_post) = instantiate_call_query_with_renaming_and_havoc(
        caller,
        call_edge,
        callee,
        call_metadata,
        callee_parameters,
        call_pre,
        call_post,
    );
    ReachabilityQuery::new(callee.clone(), call_pre, call_post)
}

pub fn normalize_projected_query_to_callee_boundary(
    callee: &ProcedureName,
    call_metadata: &LlvmEdgeMetadata,
    callee_parameters: &[String],
    projected: ReachabilityQuery,
) -> ReachabilityQuery {
    // ALPHA_RENAME: Reverse callsite substitutions for persisted summaries:
    // actual -> formal, caller lhs -> callee retval.
    let mut replacements = BTreeMap::new();
    for (index, formal) in callee_parameters.iter().enumerate() {
        let Some(actual) = call_metadata.operands.get(index) else {
            continue;
        };
        if is_boundary_symbol(actual) {
            replacements.insert(actual.clone(), formal.clone());
        }
    }
    if let Some(lhs) = &call_metadata.assignment {
        if is_boundary_symbol(lhs) {
            replacements.insert(lhs.clone(), format!("retval_{callee}"));
        }
    }
    if replacements.is_empty() {
        return projected;
    }
    ReachabilityQuery::new(
        projected.procedure,
        substitute_predicate_symbols(projected.pre, &replacements),
        substitute_predicate_symbols(projected.post, &replacements),
    )
}

fn collect_shared_symbols(
    call_metadata: &LlvmEdgeMetadata,
    caller_registry: &LlvmEdgeRegistry,
) -> BTreeSet<String> {
    let mut shared = BTreeSet::new();
    for operand in &call_metadata.operands {
        shared.insert(operand.clone());
    }
    for metadata in caller_registry.iter() {
        for operand in &metadata.operands {
            if operand.starts_with('@') {
                shared.insert(operand.clone());
            }
        }
    }
    shared
}

fn project_predicate(predicate: &Predicate, shared: &BTreeSet<String>) -> Predicate {
    match predicate {
        Predicate::True => Predicate::True,
        Predicate::False => Predicate::False,
        Predicate::Atom(atom) => {
            // APPROX_HEAVY: Symbol-membership projection keeps/drops atoms
            // syntactically instead of eliminating non-boundary variables
            // through a semantic relation projection.
            if atom_uses_shared_symbol(atom, shared) || !atom_has_symbolic_name(atom) {
                Predicate::atom(atom.clone())
            } else {
                Predicate::True
            }
        }
        Predicate::Not(inner) => Predicate::not(project_predicate(inner, shared)),
        Predicate::And(parts) => {
            Predicate::and(parts.iter().map(|part| project_predicate(part, shared)))
        }
        Predicate::Or(parts) => {
            Predicate::or(parts.iter().map(|part| project_predicate(part, shared)))
        }
    }
}

fn fallback_call_return_post(callee: &ProcedureName) -> Predicate {
    Predicate::atom(format!("retval_{callee} < 0"))
}

fn atom_uses_shared_symbol(atom: &str, shared: &BTreeSet<String>) -> bool {
    shared
        .iter()
        .filter(|token| !token.is_empty())
        .any(|token| atom.contains(token))
}

fn atom_has_symbolic_name(atom: &str) -> bool {
    atom.contains('%') || atom.contains('@')
}

fn instantiate_call_query_with_renaming_and_havoc(
    caller: &ProcedureName,
    call_edge: EdgeId,
    callee: &ProcedureName,
    call_metadata: &LlvmEdgeMetadata,
    callee_parameters: &[String],
    call_pre: Predicate,
    call_post: Predicate,
) -> (Predicate, Predicate) {
    let call_tag = callsite_tag(caller, call_edge);

    // APPROX_HEAVY: Callsite instantiation currently relies on string-symbol
    // rewrites in predicates rather than a first-class relational substitution.
    // Rename call-instance locals/retval to avoid clashes between multiple
    // call instances and recursive summary reuse.
    let mut rename_map = BTreeMap::new();
    for token in collect_predicate_symbols(&call_pre)
        .into_iter()
        .chain(collect_predicate_symbols(&call_post).into_iter())
    {
        if token.starts_with('%') || token.starts_with("retval_") {
            rename_map.insert(token.clone(), format!("{token}__{call_tag}"));
        }
    }
    let mut renamed_pre = substitute_predicate_symbols(call_pre, &rename_map);
    let mut renamed_post = substitute_predicate_symbols(call_post, &rename_map);

    // APPROX_HEAVY: Formal/actual binding is derived from parameter-index
    // pairing, not from a typed call/return relation object.
    // ALPHA_RENAME: bind formals by substitution (renamed formal -> actual)
    // instead of adding extra equality conjuncts.
    let mut formal_substitutions = BTreeMap::new();
    for (index, formal) in callee_parameters.iter().enumerate() {
        let Some(actual) = call_metadata.operands.get(index) else {
            continue;
        };
        let renamed_formal = rename_map
            .get(formal)
            .cloned()
            .unwrap_or_else(|| format!("{formal}__{call_tag}"));
        formal_substitutions.insert(renamed_formal, actual.clone());
    }
    renamed_pre = substitute_predicate_symbols(renamed_pre, &formal_substitutions);
    renamed_post = substitute_predicate_symbols(renamed_post, &formal_substitutions);

    // ALPHA_RENAME: bind callee return boundary by substitution (retval -> lhs)
    // instead of adding extra equality conjuncts.
    if let Some(lhs) = &call_metadata.assignment {
        let retval_name = format!("retval_{callee}");
        let renamed_retval = rename_map
            .get(&retval_name)
            .cloned()
            .unwrap_or_else(|| format!("{retval_name}__{call_tag}"));
        let return_substitutions = BTreeMap::from([(renamed_retval, lhs.to_string())]);
        renamed_post = substitute_predicate_symbols(renamed_post, &return_substitutions);
    }

    // APPROX_HEAVY: Global/memory havoc is syntactic token-based renaming in
    // postconditions (fresh unknown outputs), not a field-sensitive mod-set.
    // Havoc global and memory-shaped symbols on call post boundary.
    let mut havoc_map = BTreeMap::new();
    for token in collect_predicate_symbols(&renamed_post) {
        if token.starts_with('@') || looks_like_memory_symbol(&token) {
            havoc_map.insert(token.clone(), format!("{token}__havoc_{call_tag}"));
        }
    }
    let havoced_post = substitute_predicate_symbols(renamed_post, &havoc_map);

    (renamed_pre, havoced_post)
}

fn callsite_tag(caller: &ProcedureName, call_edge: EdgeId) -> String {
    format!(
        "{}_{}",
        sanitize_symbol_fragment(caller.as_str()),
        sanitize_symbol_fragment(&call_edge.to_string())
    )
}

fn sanitize_symbol_fragment(raw: &str) -> String {
    let sanitized = raw
        .chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
        .collect::<String>();
    if sanitized.is_empty() {
        "x".to_string()
    } else {
        sanitized
    }
}

fn is_boundary_symbol(token: &str) -> bool {
    token.starts_with('%')
        || token.starts_with('@')
        || token.starts_with("retval_")
        || looks_like_memory_symbol(token)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::llvm_adapter::LlvmEdgeMetadata;
    use crate::analysis::vocabulary::NodeId;
    use crate::llvm_utils::llvm_wrap::InstructionOpcode;

    #[test]
    fn fallback_call_return_post_uses_return_boundary_name() {
        let post = fallback_call_return_post(&ProcedureName::new("g"));
        assert_eq!(post, Predicate::atom("retval_g < 0"));
    }

    #[test]
    fn call_query_instantiation_renames_binds_and_havocs() {
        let caller = ProcedureName::new("f");
        let callee = ProcedureName::new("g");
        let metadata = LlvmEdgeMetadata {
            edge_id: EdgeId(9),
            from: NodeId(0),
            to: NodeId(1),
            opcode: InstructionOpcode::Call,
            instruction_text: "%r = call i32 @g(i32 %x, i32 @G)".to_string(),
            assignment: Some("%r".to_string()),
            called_function: Some("g".to_string()),
            operands: vec!["%x".to_string(), "@G".to_string()],
            branch_condition: None,
            successor_index: None,
        };
        let pre = Predicate::and([Predicate::atom("%0 > 0"), Predicate::atom("@G == 1")]);
        let post = Predicate::and([
            Predicate::atom("retval_g > 0"),
            Predicate::atom("%1 = add(%0, 1)"),
            Predicate::atom("@G = 2"),
            Predicate::atom("mem' = store(%p, 1)"),
        ]);

        let (inst_pre, inst_post) = instantiate_call_query_with_renaming_and_havoc(
            &caller,
            EdgeId(9),
            &callee,
            &metadata,
            &["%0".to_string(), "%1".to_string()],
            pre,
            post,
        );

        let pre_text = inst_pre.to_string();
        assert!(pre_text.contains("%x > 0"));
        assert!(pre_text.contains("@G == 1"));

        let post_text = inst_post.to_string();
        assert!(post_text.contains("%r > 0"));
        assert!(post_text.contains("@G__havoc_f_e9 = 2"));
        assert!(post_text.contains("mem'__havoc_f_e9 = store(%p__f_e9, 1)"));
    }

    #[test]
    fn projected_query_normalization_restores_callee_boundary_symbols() {
        let callee = ProcedureName::new("g");
        let metadata = LlvmEdgeMetadata {
            edge_id: EdgeId(10),
            from: NodeId(0),
            to: NodeId(1),
            opcode: InstructionOpcode::Call,
            instruction_text: "%11 = call i32 @g(i32 %10)".to_string(),
            assignment: Some("%11".to_string()),
            called_function: Some("g".to_string()),
            operands: vec!["%10".to_string()],
            branch_condition: None,
            successor_index: None,
        };
        let projected =
            ReachabilityQuery::new("g", Predicate::atom("%10 >= 0"), Predicate::atom("%11 < 0"));

        let normalized = normalize_projected_query_to_callee_boundary(
            &callee,
            &metadata,
            &["%0".to_string()],
            projected,
        );

        assert_eq!(normalized.pre, Predicate::atom("%0 >= 0"));
        assert_eq!(normalized.post, Predicate::atom("retval_g < 0"));
    }
}
