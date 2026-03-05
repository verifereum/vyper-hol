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
  rangeAnalysisDefs rangeEvalProofs venomExecSemantics

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

(* Eq refinement soundness.
   On true branch, narrows to constant/intersection — sound only if the
   operand values are actually equal in env. *)
Theorem range_apply_eq_sound:
  ∀lhs rhs is_true rs env.
    in_range_state rs env ∧
    (is_true ⇒
      (∀v w. (lhs = Var v ∧ rhs = Lit w ∨
              rhs = Var v ∧ lhs = Lit w) ⇒
             ∀w'. FLOOKUP env v = SOME w' ⇒ w' = w) ∧
      (∀v1 v2 w1 w2.
        lhs = Var v1 ∧ rhs = Var v2 ∧
        FLOOKUP env v1 = SOME w1 ∧ FLOOKUP env v2 = SOME w2 ⇒
        w1 = w2)) ⇒
    in_range_state (range_apply_eq lhs rhs is_true rs) env
Proof
  cheat
QED

(* Compare refinement soundness.
   Narrowing is sound only if the concrete comparison result matches is_true. *)
Theorem range_apply_compare_sound:
  ∀op lhs rhs is_true rs env.
    in_range_state rs env ∧
    (op = LT ∨ op = GT ∨ op = SLT ∨ op = SGT) ∧
    (∀v w w'.
      lhs = Var v ∧ rhs = Lit w ∧ FLOOKUP env v = SOME w' ⇒
      (is_true ⇔
        if op = LT then w2n w' < w2n w
        else if op = GT then w2n w' > w2n w
        else if op = SLT then w2i w' < w2i w
        else w2i w' > w2i w)) ∧
    (∀v w w'.
      lhs = Lit w ∧ rhs = Var v ∧ FLOOKUP env v = SOME w' ⇒
      (is_true ⇔
        if op = LT then w2n w < w2n w'
        else if op = GT then w2n w > w2n w'
        else if op = SLT then w2i w < w2i w'
        else w2i w > w2i w')) ⇒
    in_range_state (range_apply_compare op lhs rhs is_true rs) env
Proof
  cheat
QED

(* ===== Transfer function soundness ===== *)

(* Evaluating one instruction: if the pre-state ranges are sound wrt
   the variable environment before execution, then the post-state ranges
   are sound wrt the environment after execution.
   step_inst from venomExecSemantics gives the concrete semantics. *)
Theorem range_evaluate_inst_sound:
  ∀dfg inst rs s s'.
    in_range_state rs s.vs_vars ∧
    step_inst inst s = OK s' ⇒
    in_range_state (range_evaluate_inst dfg inst rs) s'.vs_vars
Proof
  cheat
QED

(* Running a full block: ranges track the environment through execution.
   Uses run_block from venomExecSemantics for the concrete semantics. *)
Theorem range_run_block_sound:
  ∀dfg bb rs imap rs' imap' s s'.
    range_run_block dfg bb.bb_instructions rs imap = (rs', imap') ∧
    in_range_state rs s.vs_vars ∧
    run_block bb s = OK s' ⇒
    in_range_state rs' s'.vs_vars
Proof
  cheat
QED
