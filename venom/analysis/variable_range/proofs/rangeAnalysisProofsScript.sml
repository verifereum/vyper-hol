(*
 * Range Analysis — Proofs
 *
 * Internal proof machinery for range analysis soundness.
 * Consumer-facing theorems are in variableRangeAnalysisPropsScript.sml.
 *)

Theory rangeAnalysisProofs
Ancestors
  rangeAnalysisDefs rangeEvalProofs venomExecSemantics

(* ===== Lattice ===== *)

Theorem range_join_two_sound:
  ∀s1 s2 env.
    in_range_state s1 env ∧ in_range_state s2 env ⇒
    in_range_state (range_join_two s1 s2) env
Proof
  cheat
QED

Theorem range_widen_states_sound:
  ∀old_st new_st env.
    in_range_state new_st env ⇒
    in_range_state (range_widen_states old_st new_st) env
Proof
  cheat
QED

(* ===== Branch refinement ===== *)

Theorem range_apply_iszero_sound:
  ∀target is_true rs env.
    in_range_state rs env ∧
    (∀w. FLOOKUP env target = SOME w ⇒
         (is_true ⇒ w = 0w) ∧ (¬is_true ⇒ w ≠ 0w)) ⇒
    in_range_state (range_apply_iszero target is_true rs) env
Proof
  cheat
QED

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

(* ===== Transfer function ===== *)

Theorem range_evaluate_inst_sound:
  ∀dfg inst rs s s'.
    in_range_state rs s.vs_vars ∧
    step_inst inst s = OK s' ⇒
    in_range_state (range_evaluate_inst dfg inst rs) s'.vs_vars
Proof
  cheat
QED

Theorem range_run_block_sound:
  ∀dfg bb rs imap rs' imap' s s'.
    range_run_block dfg bb.bb_instructions rs imap = (rs', imap') ∧
    in_range_state rs s.vs_vars ∧
    run_block bb s = OK s' ⇒
    in_range_state rs' s'.vs_vars
Proof
  cheat
QED

(* ===== PHI handling ===== *)

Theorem range_handle_phis_sound:
  ∀ra insts rs env pred_lbl.
    in_range_state rs env ∧
    (∀inst out.
      MEM inst insts ∧ inst.inst_opcode = PHI ∧
      inst.inst_outputs = [out] ⇒
      ∀w. FLOOKUP env out = SOME w ⇒
        ∃src_var.
          MEM (pred_lbl, src_var) (phi_pairs inst.inst_operands) ∧
          in_range (rs_lookup (range_exit_state ra pred_lbl) src_var) w) ⇒
    in_range_state (range_handle_phis ra insts rs) env
Proof
  cheat
QED

(* ===== Analysis output ===== *)

(* Block-level: the analysis's recorded exit state equals the transfer
   function applied to its entry state. Used by range_analyze_block_sound. *)
Theorem range_analyze_exit_consistent:
  ∀fn fuel lbl bb.
    let ra = range_analyze fn fuel in
    let dfg = dfg_build_function fn in
    lookup_block lbl fn.fn_blocks = SOME bb ∧
    lbl ∈ FDOM ra.ra_entry ⇒
    ∃imap.
      range_run_block dfg bb.bb_instructions
        (range_entry_state ra lbl) ra.ra_inst =
      (range_exit_state ra lbl, imap)
Proof
  cheat
QED
