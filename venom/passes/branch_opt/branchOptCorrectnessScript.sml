(*
 * Branch Optimization Pass — Correctness
 *
 * Top-level correctness theorem: branch_opt_function preserves
 * result equivalence up to fresh-variable projection, assuming
 * bo_iszero_inv invariance conditions.
 *
 * TOP-LEVEL:
 *   branch_opt_function_correct       — main correctness theorem
 *
 * Required preservation obligations, over branch_opt_function_supply:
 *   branch_opt_preserves_ssa_form       — SSA form preservation
 *   branch_opt_preserves_wf_function     — well-formed function preservation
 *)

Theory branchOptCorrectness
Ancestors
  branchOptProofs branchOptSupplyProofs venomExecSemantics venomWf

Theorem branch_opt_function_correct:
  !fuel ctx live_at fn s.
    let fn' = branch_opt_function live_at fn in
    let dfg = dfg_build_function fn in
    wf_ssa fn /\
    fn_inst_wf fn /\
    (!bb inst x. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==> x NOTIN bo_fresh_vars_fn fn) /\
    bo_iszero_inv dfg s /\
    (* Inv preservation across PHI prefix *)
    (!bb s0 s_phi.
       MEM bb fn.fn_blocks /\
       bo_iszero_inv dfg s0 /\
       eval_phis s0 bb.bb_instructions = OK s_phi ==>
       bo_iszero_inv dfg
         (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)) /\
    (* Inv preservation across original blocks *)
    (!bb fuel' ctx' s0 s0'.
       MEM bb fn.fn_blocks /\
       bo_iszero_inv dfg s0 /\
       run_block fuel' ctx' bb s0 = OK s0' /\ ~s0'.vs_halted ==>
       bo_iszero_inv dfg s0') /\
    (* Inv preservation across transformed blocks *)
    (!bb fuel' ctx' s0 s0'.
       MEM bb fn'.fn_blocks /\
       bo_iszero_inv dfg s0 /\
       run_block fuel' ctx' bb s0 = OK s0' /\ ~s0'.vs_halted ==>
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
                  (execution_equiv (bo_fresh_vars_fn fn))
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx fn' s)
Proof
  ACCEPT_TAC branch_opt_function_correct_proof
QED

(* ===== Obligations ===== *)

(* Over the supply-aware form: the inserted ISZERO's variable and
   instruction id come from the supply, so they are fresh. *)
Theorem branch_opt_preserves_ssa_form:
  ∀fn live_at s fn' s'.
    ssa_form fn ∧ ir_supply_covers_fn s fn ∧
    branch_opt_function_supply live_at s fn = (fn',s') ⇒
    ssa_form fn'
Proof
  ACCEPT_TAC branch_opt_function_supply_ssa_form
QED

(* Case 1 makes the ISZERO's operand the JNZ condition, so it must be
   its only operand and not a label for the successors to stay put. *)
Theorem branch_opt_preserves_wf_function:
  ∀fn live_at s fn' s'.
    wf_function fn ∧ fn_inst_wf fn ∧ EVERY label_positions_ok (fn_insts fn) ∧
    ir_supply_inst_ok s ∧ ir_supply_covers_fn s fn ∧
    branch_opt_function_supply live_at s fn = (fn',s') ⇒
    wf_function fn'
Proof
  ACCEPT_TAC branch_opt_function_supply_wf
QED
