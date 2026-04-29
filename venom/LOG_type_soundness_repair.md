# LOG: Type Soundness Repair

L001: [Assert3] imp_res_tac toplevel_value_typed_for_BaseT in `by` block → FAILED (silent match failure: assumptions have `expr_type e` not `BaseT bt`)
L002: [Assert3] gvs[] before `by` block → TIMEOUT (Assert3 context with guarded IH too rich for gvs)
L003: [Assert3] fs[] to cross-rewrite → doesn't substitute `expr_type e` in `evaluate_type` assumption
L004: [Assert3] ML trick: nested qpat_x_assum → TIMEOUT (nested ML quotations break)
L005: [Assert3] metis_tac[toplevel_value_typed_for_BaseT] → TIMEOUT (too many assumptions)
L006: [Assert3] irule toplevel_value_typed_for_BaseT_expr_type >> simp[] → FAILED (simp can't discharge antecedent subgoals in `by` block)
L007: [Assert3] RULE_ASSUM_TAC(ONCE_REWRITE_RULE[th]) → WORKS for rewriting, but `by` block still fails at line 1117
L008: [helpers] toplevel_value_typed_for_BaseT_expr_type → COMPILED (3-antecedent variant matching IH output shape)
L009: [Assert3] KEY INSIGHT: `by` block is wrong decomposition. Need to inline derivation after RULE_ASSUM_TAC.
