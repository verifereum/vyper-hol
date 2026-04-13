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
    s.vs_prev_bb = NONE /\
    (* Simulation prerequisites for mergeable blocks *)
    (!bb. MEM bb func.fn_blocks /\ block_signature bb <> NONE ==>
      EVERY (\i. i.inst_opcode <> INVOKE) bb.bb_instructions /\
      EVERY (\i. i.inst_opcode <> PARAM) bb.bb_instructions /\
      ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) /\
      EVERY (\i. is_output_opcode i.inst_opcode \/ i.inst_outputs = [])
            bb.bb_instructions) /\
    (* Labels are not used as runtime values *)
    (!l. MEM l (fn_labels func) ==> FLOOKUP s.vs_labels l = NONE) ==>
    let func' = tail_merge_fn func in
    result_equiv UNIV
      (run_function fuel ctx func s)
      (run_function fuel ctx func' s)
Proof
  ACCEPT_TAC tail_merge_fn_correct
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
