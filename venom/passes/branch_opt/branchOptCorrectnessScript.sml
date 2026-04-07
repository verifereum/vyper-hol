Theory branchOptCorrectness
Ancestors
  branchOptProofs venomWf

Theorem branch_opt_function_correct:
  !fuel ctx live_at fn s.
    let fn' = branch_opt_function live_at fn in
    let dfg = dfg_build_function fn in
    wf_ssa fn /\
    fn_inst_wf fn /\
    (!bb inst x. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==> x NOTIN bo_fresh_vars_fn fn) /\
    bo_iszero_inv dfg s /\
    (* Inv preservation across original blocks *)
    (!bb fuel' ctx' s0 s0'.
       MEM bb fn.fn_blocks /\
       bo_iszero_inv dfg s0 /\ s0.vs_inst_idx = 0 /\
       exec_block fuel' ctx' bb s0 = OK s0' /\ ~s0'.vs_halted ==>
       bo_iszero_inv dfg s0') /\
    (* Inv preservation across transformed blocks *)
    (!bb fuel' ctx' s0 s0'.
       MEM bb fn'.fn_blocks /\
       bo_iszero_inv dfg s0 /\ s0.vs_inst_idx = 0 /\
       exec_block fuel' ctx' bb s0 = OK s0' /\ ~s0'.vs_halted ==>
       bo_iszero_inv dfg s0') /\
    (* Inv preservation within block prefix (both original and transformed) *)
    (!bb fuel' ctx' st st' inst.
       (MEM bb fn.fn_blocks \/ MEM bb fn'.fn_blocks) /\
       bo_iszero_inv dfg st /\
       st.vs_inst_idx < LENGTH bb.bb_instructions /\
       EL st.vs_inst_idx bb.bb_instructions = inst /\
       ~is_terminator inst.inst_opcode /\
       step_inst fuel' ctx' inst st = OK st' ==>
       bo_iszero_inv dfg (st' with vs_inst_idx := SUC st.vs_inst_idx)) /\
    s.vs_inst_idx = 0 ==>
    lift_result (state_equiv (bo_fresh_vars_fn fn))
               (execution_equiv (bo_fresh_vars_fn fn))
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx fn' s)
Proof
  ACCEPT_TAC branch_opt_function_correct_proof
QED

(* ===== Obligations ===== *)

(* Cheated: requires proving MAP over branch_opt_block preserves
   SSA uniqueness/dominance — needs wf_ssa infrastructure not yet built *)
Theorem branch_opt_preserves_ssa_form:
  ∀fn live_at. ssa_form fn ⇒ ssa_form (branch_opt_function live_at fn)
Proof
  cheat
QED

(* Cheated: requires proving branch_opt_block preserves block well-formedness
   (non-empty blocks, terminator position) — structural obligation *)
Theorem branch_opt_preserves_wf_function:
  ∀fn live_at. wf_function fn ⇒ wf_function (branch_opt_function live_at fn)
Proof
  cheat
QED
