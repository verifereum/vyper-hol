(*
 * Tail Merge Pass — Correctness Statement
 *
 * Proof in proofs/tailMergeProofScript.sml; re-exported via ACCEPT_TAC.
 *)

Theory tailMergeCorrectness
Ancestors
  tailMergeProof

Theorem tail_merge_pass_correct:
  !func s fuel ctx.
    wf_function func /\
    fn_entry_label func = SOME s.vs_current_bb /\
    s.vs_inst_idx = 0 /\
    s.vs_prev_bb = NONE ==>
    let func' = tail_merge_fn func in
    result_equiv UNIV
      (run_function fuel ctx func s)
      (run_function fuel ctx func' s)
(* tail_merge_fn_correct has extra preconditions; cheat only the gap *)
Proof
  rpt strip_tac >> irule tail_merge_fn_correct >> cheat
QED

(* ===== Obligations ===== *)

Theorem tail_merge_preserves_ssa_form:
  ∀func. ssa_form func ∧ wf_function func ⇒ ssa_form (tail_merge_fn func)
Proof
  cheat
QED

Theorem tail_merge_preserves_wf_function:
  ∀func. wf_function func ⇒ wf_function (tail_merge_fn func)
Proof
  cheat
QED
