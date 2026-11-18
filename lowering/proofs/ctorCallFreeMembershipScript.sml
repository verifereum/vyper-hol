(* Opcode exclusion for membership CFG construction. *)
Theory ctorCallFreeMembership
Ancestors
  list pair vyperAST venomInst loweringShapeDefs exprLowering
  ctorCallFreeRules ctorCallFreeValues

Theorem outcomes_free_emit_membership_eqs:
  !elems s. P EQ /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (emit_membership_eqs needle elems s)))
Proof
  Induct_on `elems` >> rpt strip_tac >> simp[emit_membership_eqs_def] >>
  rpt (FIRST [CHANGED_TAC (simp[every_state_insts_return, opcode_every_emit_op,
      opcode_every_emit_void, opcode_every_emit_inst]),
    gen_tac, strip_tac, irule every_state_insts_bind, conj_tac, first_assum irule])
QED

Theorem outcomes_free_fold_membership_or:
  !cs acc s. P OR /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (fold_membership_or acc cs s)))
Proof
  Induct_on `cs` >> rpt strip_tac >> simp[fold_membership_or_def] >>
  rpt (FIRST [CHANGED_TAC (simp[every_state_insts_return, opcode_every_emit_op,
      opcode_every_emit_void, opcode_every_emit_inst]),
    gen_tac, strip_tac, irule every_state_insts_bind, conj_tac, first_assum irule])
QED

Theorem outcomes_free_fold_membership_and:
  !cs acc s. P ISZERO /\ P AND /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (fold_membership_and acc cs s)))
Proof
  Induct_on `cs` >> rpt strip_tac >> simp[fold_membership_and_def] >>
  rpt (FIRST [CHANGED_TAC (simp[every_state_insts_return, opcode_every_emit_op,
      opcode_every_emit_void, opcode_every_emit_inst]),
    gen_tac, strip_tac, irule every_state_insts_bind, conj_tac, first_assum irule])
QED

Theorem outcomes_free_compile_list_membership_in:
  P EQ /\ P OR /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_list_membership_in needle elems s)))
Proof
  strip_tac >> simp[compile_list_membership_in_def] >> irule every_state_insts_bind >>
  simp[outcomes_free_emit_membership_eqs] >> rpt strip_tac >>
  Cases_on `x` >> simp[every_state_insts_return, outcomes_free_fold_membership_or]
QED

Theorem outcomes_free_compile_list_membership_notin:
  P EQ /\ P ISZERO /\ P AND /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_list_membership_notin needle elems s)))
Proof
  strip_tac >> simp[compile_list_membership_notin_def] >> irule every_state_insts_bind >>
  simp[outcomes_free_emit_membership_eqs] >> rpt strip_tac >>
  Cases_on `x` >> simp[every_state_insts_return] >> irule every_state_insts_bind >>
  simp[opcode_every_emit_op, opcode_every_emit_void, opcode_every_emit_inst,
      outcomes_free_fold_membership_and]
QED

Theorem outcomes_free_compile_array_membership_loop:
  (!opc. MEM opc [JMP; ASSIGN; GT; ISZERO; ASSERT; EQ; JNZ; MUL; ADD] ==> P opc) /\
  (!addr st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (loader addr st)))) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_array_membership_loop needle arr len sz off loader bound is_in s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  Cases_on `bound` >> simp[compile_array_membership_loop_def] >>
  rpt (FIRST [CHANGED_TAC (simp[every_state_insts_return, opcode_every_emit_op,
      opcode_every_emit_void, opcode_every_emit_inst,
      every_state_insts_fresh_id, every_state_insts_fresh_var, every_state_insts_fresh_label,
          every_state_insts_new_block]),
    gen_tac, strip_tac, irule every_state_insts_bind, irule every_state_insts_ignore_bind,
    conj_tac, IF_CASES_TAC, first_assum irule])
QED

Theorem outcomes_free_compile_var_array_membership:
  (!opc. MEM opc [JMP; ASSIGN; GT; ISZERO; ASSERT; EQ; JNZ; MUL; ADD;
    ILOAD; DLOAD; MLOAD; SLOAD; TLOAD; CALLDATALOAD] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_var_array_membership ce needle arr ty is_in s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_var_array_membership_def] >> irule every_state_insts_bind >>
  conj_tac
  >- (rpt strip_tac >> BETA_TAC >> irule (SRULE [DISJ_IMP_THM, FORALL_AND_THM]
        outcomes_free_compile_array_membership_loop) >> simp[outcomes_free_ptr_load]) >>
  rpt CASE_TAC >> simp[every_state_insts_return, outcomes_free_ptr_load]
QED

Theorem opcode_every_list_membership_in:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_list_membership_in v xs st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_compile_list_membership_in >> simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem opcode_every_list_membership_notin:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_list_membership_notin v xs st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_compile_list_membership_notin >> simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem opcode_every_var_array_membership:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_var_array_membership ce v vv t isin st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_compile_var_array_membership >> simp[DISJ_IMP_THM, FORALL_AND_THM]
QED
