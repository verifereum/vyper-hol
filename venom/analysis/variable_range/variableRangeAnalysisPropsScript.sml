(*
 * Variable Range Analysis — Properties (public API)
 *
 * Re-exports consumer-facing properties from proofs/ via ACCEPT_TAC.
 * Consumers: just `Ancestors variableRangeAnalysisProps` to get defs + properties.
 *
 * TOP-LEVEL PROPERTIES:
 *   range_evaluate_inst_sound — single instruction soundness wrt step_inst
 *   range_run_block_sound     — block execution soundness wrt run_block
 *   range_join_two_sound      — join preserves state soundness
 *   range_widen_states_sound  — widening preserves state soundness
 *   range_apply_iszero_sound  — branch refinement (iszero) soundness
 *   range_apply_eq_sound      — branch refinement (eq) soundness
 *   range_apply_compare_sound — branch refinement (compare) soundness
 *)

Theory variableRangeAnalysisProps
Ancestors
  valueRangeDefs rangeEvalDefs rangeAnalysisDefs
  valueRangeProofs rangeEvalProofs rangeAnalysisProofs

(* ===== Transfer Function Soundness ===== *)

Theorem range_evaluate_inst_sound:
  ∀dfg inst rs s s'.
    in_range_state rs s.vs_vars ∧
    step_inst inst s = OK s' ⇒
    in_range_state (range_evaluate_inst dfg inst rs) s'.vs_vars
Proof ACCEPT_TAC rangeAnalysisProofsTheory.range_evaluate_inst_sound
QED

Theorem range_run_block_sound:
  ∀dfg bb rs imap rs' imap' s s'.
    range_run_block dfg bb.bb_instructions rs imap = (rs', imap') ∧
    in_range_state rs s.vs_vars ∧
    run_block bb s = OK s' ⇒
    in_range_state rs' s'.vs_vars
Proof ACCEPT_TAC rangeAnalysisProofsTheory.range_run_block_sound
QED

(* ===== State Combiner Soundness ===== *)

Theorem range_join_two_sound:
  ∀s1 s2 env.
    in_range_state s1 env ∧ in_range_state s2 env ⇒
    in_range_state (range_join_two s1 s2) env
Proof ACCEPT_TAC rangeAnalysisProofsTheory.range_join_two_sound
QED

Theorem range_widen_states_sound:
  ∀old_st new_st env.
    in_range_state new_st env ⇒
    in_range_state (range_widen_states old_st new_st) env
Proof ACCEPT_TAC rangeAnalysisProofsTheory.range_widen_states_sound
QED

(* ===== Branch Refinement Soundness ===== *)

Theorem range_apply_iszero_sound:
  ∀target is_true rs env.
    in_range_state rs env ∧
    (∀w. FLOOKUP env target = SOME w ⇒
         (is_true ⇒ w = 0w) ∧ (¬is_true ⇒ w ≠ 0w)) ⇒
    in_range_state (range_apply_iszero target is_true rs) env
Proof ACCEPT_TAC rangeAnalysisProofsTheory.range_apply_iszero_sound
QED

Theorem range_apply_eq_sound:
  ∀lhs rhs is_true rs env.
    in_range_state rs env ⇒
    in_range_state (range_apply_eq lhs rhs is_true rs) env
Proof ACCEPT_TAC rangeAnalysisProofsTheory.range_apply_eq_sound
QED

Theorem range_apply_compare_sound:
  ∀op lhs rhs is_true rs env.
    in_range_state rs env ⇒
    in_range_state (range_apply_compare op lhs rhs is_true rs) env
Proof ACCEPT_TAC rangeAnalysisProofsTheory.range_apply_compare_sound
QED
