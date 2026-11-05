(*
 * Tail Merge Pass — Correctness Statement
 *
 * Proof in proofs/tailMergeProofScript.sml; re-exported via ACCEPT_TAC.
 *)

Theory tailMergeCorrectness
Ancestors
  tailMergeProof tailMergeWf unitShapeDefs

(* label_positions_ok keeps block labels out of value operands: the pass
   rewrites every label operand of a terminator, and eval_operand reads a
   Label through vs_labels, so a label used as a value would change. *)
Theorem tail_merge_pass_correct:
  !func s fuel ctx.
    wf_function func /\ fn_inst_wf func /\ ssa_form func /\
    EVERY label_positions_ok (fn_insts func) /\
    fn_entry_label func = SOME s.vs_current_bb /\
    s.vs_inst_idx = 0 /\
    s.vs_prev_bb = NONE ==>
    result_equiv UNIV
      (run_function fuel ctx func s)
      (run_function fuel ctx (tail_merge_fn func) s)
Proof
  ACCEPT_TAC tail_merge_fn_correct_structural
QED

(* ===== Obligations ===== *)

Theorem tail_merge_preserves_ssa_form:
  ∀func. ssa_form func ∧ wf_function func ⇒ ssa_form (tail_merge_fn func)
Proof
  metis_tac[tail_merge_fn_ssa_form]
QED

Theorem tail_merge_preserves_wf_function:
  ∀func. wf_function func ⇒ wf_function (tail_merge_fn func)
Proof
  ACCEPT_TAC tail_merge_fn_wf_function
QED
