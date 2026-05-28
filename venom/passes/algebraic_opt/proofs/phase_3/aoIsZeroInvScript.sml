(* Within-block iszero invariant for per-block simulation.
 *
 * TOP-LEVEL:
 *   within_block_iszero_inv — ISZEROs at positions < idx have correct values
 *   wbiz_initial, wbiz_mono, wbiz_inst_idx — basic properties
 *)
Theory aoIsZeroInv
Ancestors
  venomWf venomInstProps stateEquiv stateEquivProps
  venomState venomExecSemantics
Libs
  pairLib

Definition within_block_iszero_inv_def:
  within_block_iszero_inv fn0 bb idx s <=>
    !j x iz_op.
      j < idx /\ j < LENGTH bb.bb_instructions /\
      (EL j bb.bb_instructions).inst_opcode = ISZERO /\
      (EL j bb.bb_instructions).inst_operands = [iz_op] /\
      MEM x (EL j bb.bb_instructions).inst_outputs ==>
      !val_x val_op.
        lookup_var x s = SOME val_x /\
        eval_operand iz_op s = SOME val_op ==>
        val_x = bool_to_word (val_op = 0w)
End

val _ = delsimps ["within_block_iszero_inv_def"]

Theorem wbiz_initial:
  !fn0 bb s. within_block_iszero_inv fn0 bb 0 s
Proof
  simp[within_block_iszero_inv_def]
QED

Theorem wbiz_mono:
  !fn0 bb idx idx' s.
    within_block_iszero_inv fn0 bb idx s /\ idx' <= idx ==>
    within_block_iszero_inv fn0 bb idx' s
Proof
  rw[within_block_iszero_inv_def] >> rpt strip_tac >>
  `j < idx` by DECIDE_TAC >> metis_tac[]
QED

Theorem wbiz_inst_idx:
  !fn0 bb idx s n.
    within_block_iszero_inv fn0 bb idx (s with vs_inst_idx := n) <=>
    within_block_iszero_inv fn0 bb idx s
Proof
  rw[within_block_iszero_inv_def, lookup_var_def] >>
  eq_tac >> rpt strip_tac >> res_tac >> gvs[] >>
  qpat_x_assum `eval_operand _ _ = _` mp_tac >>
  Cases_on `iz_op` >> simp[eval_operand_def, lookup_var_def]
QED
