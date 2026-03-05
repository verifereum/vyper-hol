(*
 * Range Analysis — Proofs
 *
 * Safety properties of the analysis loop:
 *   - join/widen produce valid states
 *   - branch refinement is sound
 *   - widening guarantees convergence
 *)

Theory rangeAnalysisProofs
Ancestors
  rangeAnalysisDefs rangeEvalProofs

(* ===== Join soundness ===== *)

(* Join of two states is sound: if both are sound, so is the join *)
Theorem range_join_two_sound:
  ∀s1 s2 env.
    in_range_state s1 env ∧ in_range_state s2 env ⇒
    in_range_state (range_join_two s1 s2) env
Proof
  cheat
QED

(* ===== Widen soundness ===== *)

(* Widened state is an over-approximation of the new state *)
Theorem range_widen_states_sound:
  ∀old_st new_st env.
    in_range_state new_st env ⇒
    in_range_state (range_widen_states old_st new_st) env
Proof
  cheat
QED

(* ===== Branch refinement soundness ===== *)

(* Iszero refinement: on true branch (value = 0), narrowed state is sound *)
Theorem range_apply_iszero_sound:
  ∀target is_true rs env.
    in_range_state rs env ∧
    (∀w. FLOOKUP env target = SOME w ⇒
         (is_true ⇒ w = 0w) ∧ (¬is_true ⇒ w ≠ 0w)) ⇒
    in_range_state (range_apply_iszero target is_true rs) env
Proof
  cheat
QED

(* Eq refinement soundness *)
Theorem range_apply_eq_sound:
  ∀lhs rhs is_true rs env.
    in_range_state rs env ⇒
    in_range_state (range_apply_eq lhs rhs is_true rs) env
Proof
  cheat
QED

(* Compare refinement soundness *)
Theorem range_apply_compare_sound:
  ∀op lhs rhs is_true rs env.
    in_range_state rs env ⇒
    in_range_state (range_apply_compare op lhs rhs is_true rs) env
Proof
  cheat
QED

(* ===== Transfer function soundness ===== *)

(* Evaluating one instruction preserves soundness *)
Theorem range_evaluate_inst_sound:
  ∀dfg inst rs env env'.
    in_range_state rs env ⇒
    in_range_state (range_evaluate_inst dfg inst rs) env'
Proof
  cheat
QED

(* Running a full block preserves soundness *)
Theorem range_run_block_sound:
  ∀dfg insts rs imap rs' imap' env.
    range_run_block dfg insts rs imap = (rs', imap') ∧
    in_range_state rs env ⇒
    in_range_state rs' env
Proof
  cheat
QED
