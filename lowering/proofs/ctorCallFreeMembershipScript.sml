(* Opcode exclusion for membership CFG construction. *)
Theory ctorCallFreeMembership
Ancestors
  list pair vyperAST venomInst loweringShapeDefs exprLowering
  ctorCallFreeRules ctorCallFreeValues

Theorem call_free_membership_eqs[local]:
  !xs v st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (emit_membership_eqs v xs st)))
Proof
  Induct >> simp[emit_membership_eqs_def, every_state_insts_return] >>
  rpt gen_tac >> qid_spec_tac `st` >>
  ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- simp[call_free_emit_op] >>
  gen_tac >> simp[every_state_insts_bind, every_state_insts_return]
QED

Theorem call_free_membership_or[local]:
  !xs v st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (fold_membership_or v xs st)))
Proof
  Induct >> simp[fold_membership_or_def, every_state_insts_return] >>
  rpt gen_tac >> qid_spec_tac `st` >>
  ho_match_mp_tac every_state_insts_bind >> simp[call_free_emit_op]
QED

Theorem call_free_membership_and[local]:
  !xs v st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (fold_membership_and v xs st)))
Proof
  Induct >> simp[fold_membership_and_def, every_state_insts_return] >>
  rpt gen_tac >> qid_spec_tac `st` >>
  ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- simp[call_free_emit_op] >>
  gen_tac >> simp[every_state_insts_bind, call_free_emit_op]
QED

Theorem call_free_list_membership_in:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_list_membership_in v xs st)))
Proof
  qid_spec_tac `st` >> simp[compile_list_membership_in_def] >>
  ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- simp[call_free_membership_eqs] >>
  Cases >> simp[every_state_insts_return, call_free_membership_or]
QED

Theorem call_free_list_membership_notin:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_list_membership_notin v xs st)))
Proof
  qid_spec_tac `st` >> simp[compile_list_membership_notin_def] >>
  ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- simp[call_free_membership_eqs] >>
  Cases >> simp[every_state_insts_return, every_state_insts_bind,
    call_free_emit_op, call_free_membership_and]
QED

Theorem call_free_array_membership_loop[local]:
  (!addr st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (loader addr st)))) ==>
  !st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_array_membership_loop v arr len sz off loader bound isin st)))
Proof
  strip_tac >> simp[compile_array_membership_loop_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[every_state_insts_fresh_var,
      every_state_insts_fresh_label, every_state_insts_new_block,
      every_state_insts_return, call_free_emit_inst, call_free_emit_op]),
    Cases_on `bound` >> simp[], IF_CASES_TAC >> simp[]]) >>
  simp[every_state_insts_bind, call_free_emit_op, call_free_emit_inst]
QED

Theorem call_free_var_array_membership:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_var_array_membership ce v vv t isin st)))
Proof
  qid_spec_tac `st` >> simp[compile_var_array_membership_def] >>
  ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- (rpt CASE_TAC >> simp[call_free_ptr_load, every_state_insts_return]) >>
  gen_tac >> ho_match_mp_tac call_free_array_membership_loop >> simp[call_free_ptr_load]
QED
