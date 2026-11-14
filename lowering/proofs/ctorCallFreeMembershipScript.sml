(* Opcode exclusion for membership CFG construction. *)
Theory ctorCallFreeMembership
Ancestors
  list pair vyperAST venomInst loweringShapeDefs exprLowering
  ctorCallFreeRules ctorCallFreeValues

Theorem opcode_every_membership_eqs[local]:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  !xs v st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (emit_membership_eqs v xs st)))
  )
Proof
  strip_tac >>
  Induct >> simp[emit_membership_eqs_def, every_state_insts_return] >>
  rpt gen_tac >> qid_spec_tac `st` >>
  ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- simp[opcode_every_emit_op] >>
  gen_tac >> simp[every_state_insts_bind, every_state_insts_return]
QED

Theorem opcode_every_membership_or[local]:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  !xs v st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (fold_membership_or v xs st)))
  )
Proof
  strip_tac >>
  Induct >> simp[fold_membership_or_def, every_state_insts_return] >>
  rpt gen_tac >> qid_spec_tac `st` >>
  ho_match_mp_tac every_state_insts_bind >> simp[opcode_every_emit_op]
QED

Theorem opcode_every_membership_and[local]:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  !xs v st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (fold_membership_and v xs st)))
  )
Proof
  strip_tac >>
  Induct >> simp[fold_membership_and_def, every_state_insts_return] >>
  rpt gen_tac >> qid_spec_tac `st` >>
  ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- simp[opcode_every_emit_op] >>
  gen_tac >> simp[every_state_insts_bind, opcode_every_emit_op]
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
  strip_tac >>
  qid_spec_tac `st` >> simp[compile_list_membership_in_def] >>
  ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- simp[(UNDISCH opcode_every_membership_eqs)] >>
  Cases >> simp[every_state_insts_return, (UNDISCH opcode_every_membership_or)]
QED

Theorem call_free_list_membership_in:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_list_membership_in v xs st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_list_membership_in) >> simp[]
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
  strip_tac >>
  qid_spec_tac `st` >> simp[compile_list_membership_notin_def] >>
  ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- simp[(UNDISCH opcode_every_membership_eqs)] >>
  Cases >> simp[every_state_insts_return, every_state_insts_bind,
    opcode_every_emit_op, (UNDISCH opcode_every_membership_and)]
QED

Theorem call_free_list_membership_notin:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_list_membership_notin v xs st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_list_membership_notin) >> simp[]
QED

Theorem opcode_every_array_membership_loop[local]:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!addr st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (loader addr st)))) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_array_membership_loop v arr len sz off loader bound isin st)))
  )
Proof
  strip_tac >>
  strip_tac >> simp[compile_array_membership_loop_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[every_state_insts_fresh_var,
      every_state_insts_fresh_label, every_state_insts_new_block,
      every_state_insts_return, opcode_every_emit_inst, opcode_every_emit_op]),
    Cases_on `bound` >> simp[], IF_CASES_TAC >> simp[]]) >>
  simp[every_state_insts_bind, opcode_every_emit_op, opcode_every_emit_inst]
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
  strip_tac >>
  qid_spec_tac `st` >> simp[compile_var_array_membership_def] >>
  ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- (rpt CASE_TAC >> simp[(UNDISCH opcode_every_ptr_load), every_state_insts_return]) >>
  gen_tac >> ho_match_mp_tac (UNDISCH opcode_every_array_membership_loop) >> simp[(UNDISCH opcode_every_ptr_load)]
QED

Theorem call_free_var_array_membership:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_var_array_membership ce v vv t isin st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_var_array_membership) >> simp[]
QED
