(*
 * Pass Shared Properties (API)
 *
 * Re-exports theorems from proof files. Inline proofs only for
 * trivial one-liners or cheated stubs.
 *
 * TOP-LEVEL:
 *   Instruction builders:
 *     mk_nop_inst_correct        — NOP replacement is identity on state
 *     mk_assign_inst_correct     — ASSIGN replacement evaluates and binds output
 *
 *   NOP clearing:
 *     clear_nops_block_correct    — removing NOPs from a block preserves execution
 *     clear_nops_function_correct — removing NOPs from a function preserves execution
 *     clear_nops_lift_result      — clear_nops preserves lift_result
 *
 *   Operand substitution:
 *     subst_operand_eval           — single substitution preserves eval_operand
 *     subst_op_map_eval            — map substitution preserves eval_operand
 *     subst_operand_eval_operands  — single substitution preserves eval_operands
 *     subst_op_map_eval_operands   — map substitution preserves eval_operands
 *     subst_operands_correct       — single substitution preserves step_inst
 *     subst_operands_map_correct   — map substitution preserves step_inst
 *
 *   State preservation:
 *     step_inst_preserves_all              — 18-conjunct field preservation
 *     step_base_preserves_tracked          — step_inst_base field preservation
 *     eligible_no_write_balance_extcode    — eligible ops don't write BALANCE/EXTCODE
 *
 *   Transfer/determinism:
 *     step_inst_base_ok_transfer           — OK transfers across agreeing states
 *     step_inst_base_output_determined_fields — per-field output determinism
 *
 *   Variable frame:
 *     step_inst_base_var_frame_full        — step_inst_base preserves non-output vars
 *     step_inst_var_frame_full             — step_inst preserves non-output vars
 *
 *   Commutativity:
 *     effects_independent_commute          — independent instructions commute
 *)

Theory passSharedProps
Ancestors
  passSharedDefs venomExecSemantics venomEffects stateEquiv venomInstProofs
  passSharedField passSharedTransfer passSharedVarFrame passSharedFrame
  passSharedSubst

open venomStateTheory venomInstTheory;

(* ===================================================================== *)
(* ===== Instruction builders (trivial) ================================ *)
(* ===================================================================== *)

Theorem mk_nop_inst_correct:
  !fuel ctx inst s.
    step_inst fuel ctx (mk_nop_inst inst) s = OK s
Proof
  rw[mk_nop_inst_def, step_inst_def, step_inst_base_def]
QED

Theorem mk_assign_inst_correct:
  !fuel ctx inst src_op s v out.
    eval_operand src_op s = SOME v /\
    inst.inst_outputs = [out] ==>
    step_inst fuel ctx (mk_assign_inst inst src_op) s =
      OK (update_var out v s)
Proof
  rw[mk_assign_inst_def, step_inst_def, step_inst_base_def] >> rw[]
QED

(* ===================================================================== *)
(* ===== NOP clearing (cheated, pending block simulation proof) ======== *)
(* ===================================================================== *)

Theorem clear_nops_block_correct:
  !fuel ctx bb s.
    s.vs_inst_idx = 0 ==>
    run_block fuel ctx (clear_nops_block bb) s =
    run_block fuel ctx bb s
Proof
  cheat
QED

Theorem clear_nops_function_correct:
  !fuel ctx fn s.
    s.vs_inst_idx = 0 ==>
    run_function fuel ctx (clear_nops_function fn) s =
    run_function fuel ctx fn s
Proof
  cheat
QED

Theorem clear_nops_lift_result:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) fuel ctx fn fn' s.
    s.vs_inst_idx = 0 /\
    lift_result R_ok R_term
      (run_function fuel ctx fn s)
      (run_function fuel ctx fn' s) ==>
    lift_result R_ok R_term
      (run_function fuel ctx fn s)
      (run_function fuel ctx (clear_nops_function fn') s)
Proof
  rpt strip_tac >>
  `run_function fuel ctx (clear_nops_function fn') s =
   run_function fuel ctx fn' s` by
    (irule clear_nops_function_correct >> simp[]) >>
  gvs[]
QED

(* ===================================================================== *)
(* ===== Re-exported proof results ===================================== *)
(* ===================================================================== *)

(* Operand substitution *)
Theorem subst_operand_eval =
  passSharedSubstTheory.subst_operand_eval

Theorem subst_op_map_eval =
  passSharedSubstTheory.subst_op_map_eval

Theorem subst_operand_eval_operands =
  passSharedSubstTheory.subst_operand_eval_operands

Theorem subst_op_map_eval_operands =
  passSharedSubstTheory.subst_op_map_eval_operands

Theorem subst_operands_correct =
  passSharedSubstTheory.subst_operands_correct

Theorem subst_operands_map_correct =
  passSharedSubstTheory.subst_operands_map_correct

(* State field preservation *)
Theorem step_inst_preserves_all =
  passSharedFieldTheory.step_inst_preserves_all

Theorem step_base_preserves_tracked =
  passSharedFieldTheory.step_base_preserves_tracked

Theorem eligible_no_write_balance_extcode =
  passSharedFieldTheory.eligible_no_write_balance_extcode

(* Transfer/determinism *)
Theorem step_inst_base_ok_transfer =
  passSharedTransferTheory.step_inst_base_ok_transfer

Theorem step_inst_base_output_determined_fields =
  passSharedTransferTheory.step_inst_base_output_determined_fields

(* Variable frame *)
Theorem step_inst_base_var_frame_full =
  passSharedVarFrameTheory.step_inst_base_var_frame_full

Theorem step_inst_var_frame_full =
  passSharedVarFrameTheory.step_inst_var_frame_full

(* Commutativity *)
Theorem effects_independent_commute =
  passSharedFrameTheory.effects_independent_commute
