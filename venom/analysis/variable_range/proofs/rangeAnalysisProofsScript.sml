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
    step_inst_base inst s = OK s' ⇒
    in_range_state (range_evaluate_inst dfg inst rs) s'.vs_vars
Proof
  cheat
QED

(* ===== Edge transfer ===== *)

(* Branch refinement is sound when the concrete execution actually takes
   the edge pred→succ. For JNZ terminators, this means the condition
   variable's value matches the branch direction. *)
Theorem range_branch_refine_sound:
  ∀dfg bbs pred succ rs env.
    in_range_state rs env ∧
    (∀bb.
      lookup_block pred bbs = SOME bb ∧ ¬NULL bb.bb_instructions ⇒
      let term = LAST bb.bb_instructions in
      ∀cond_op true_lbl false_lbl.
        term.inst_opcode = JNZ ∧
        term.inst_operands = [cond_op; Label true_lbl; Label false_lbl] ⇒
          (succ = true_lbl ⇒
            ∀v w. cond_op = Var v ∧ FLOOKUP env v = SOME w ⇒ w ≠ 0w) ∧
          (succ = false_lbl ⇒
            ∀v w. cond_op = Var v ∧ FLOOKUP env v = SOME w ⇒ w = 0w)) ⇒
    in_range_state (range_branch_refine dfg bbs pred succ rs) env
Proof
  cheat
QED

(* PHI renaming is sound when the concrete values of PHI outputs match
   the ranges of the predecessor operands. This holds when execution
   came from pred: PHI assigns out := v, so env(out) = env(v) ∈ range(v). *)
Theorem range_phi_edge_rename_sound:
  ∀bbs pred succ rs env.
    in_range_state rs env ∧
    (∀bb inst out v.
      lookup_block succ bbs = SOME bb ∧
      MEM inst bb.bb_instructions ∧
      inst.inst_opcode = PHI ∧
      inst.inst_outputs = [out] ∧
      ALOOKUP (phi_pairs inst.inst_operands) pred = SOME v ⇒
        ∀w. FLOOKUP env out = SOME w ⇒ in_range (rs_lookup rs v) w) ⇒
    in_range_state (range_phi_edge_rename bbs pred succ rs) env
Proof
  cheat
QED

(* ===== Analysis output ===== *)

(* Block-level: for a processed block, the exit state is consistent
   with folding the transfer function through the block's instructions
   starting from the entry state. *)
Theorem range_analyze_consistent:
  ∀fn lbl bb.
    let ra = range_analyze fn in
    let dfg = dfg_build_function fn in
    lookup_block lbl fn.fn_blocks = SOME bb ⇒
    ∀idx. idx < LENGTH bb.bb_instructions ⇒
      range_at_inst ra lbl (idx + 1) =
        range_evaluate_inst dfg (EL idx bb.bb_instructions)
          (range_at_inst ra lbl idx)
Proof
  cheat
QED

(* Block-level soundness: entry sound + run_block OK ⇒ exit sound *)
Theorem range_analyze_block_sound_proof:
  ∀fn lbl bb fuel ctx s s'.
    let ra = range_analyze fn in
    lookup_block lbl fn.fn_blocks = SOME bb ∧
    in_range_state (range_entry_state ra lbl) s.vs_vars ∧
    run_block fuel ctx bb s = OK s' ⇒
    in_range_state (range_exit_state ra lbl) s'.vs_vars
Proof
  cheat
QED

(* Query soundness: range state sound ⇒ range_get_range contains value *)
Theorem range_get_range_sound_proof:
  ∀ra lbl idx op w env.
    in_range_state (range_at_inst ra lbl idx) env ∧
    (∀v. op = Var v ⇒ FLOOKUP env v = SOME w) ∧
    (∀v. op = Lit v ⇒ w = v) ⇒
    in_range (range_get_range ra lbl idx op) w
Proof
  cheat
QED
