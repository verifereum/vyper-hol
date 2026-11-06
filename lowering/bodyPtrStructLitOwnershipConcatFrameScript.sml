Theory bodyPtrStructLitOwnershipConcatFrame
Ancestors bodyPtrStructLitOwnershipStructFrame bodyPtrStructLitOwnershipInterfaces bodyPtrStructLitOwnershipScratchFrame
  bodyPtrStructLitOwnershipFreshness bodyPtrStructLitOwnershipSteps
  loweringShapeProps loweringShapeDefs loweringShapeRules context compileEnv
  exprLowering list unitShapeDefs stackPlanTypes venomInst

Theorem alloc_run_concat_op_frame:
  shape_stable R /\ (opc = ADD \/ opc = MLOAD) ==>
  alloc_run (\s. shape_state s /\ R s /\ EVERY (plain_operand s) ops)
    (emit_op opc ops) (\v s. shape_state s /\ R s /\ plain_operand s v)
Proof
  strip_tac >> irule alloc_run_conseq >>
  irule_at Any (Q.INST [`internal` |-> `F`] alloc_run_fresh_shape_frame) >>
  irule_at Any shape_step_emit_op_pre >> irule_at Any alloc_run_emit_op_fresh >>
  qexistsl [`R`, `\s. EVERY (plain_operand s) ops`] >>
  gvs[lowered_inst_ok_def, mk_inst_def, label_or_plain_def,
    raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
    is_param_opcode_def, is_read0_opcode_def, label_positions_ok_def,
    is_terminator_def, EVERY_MEM, plain_operand_def] >>
  rpt strip_tac >> rpt (CASE_TAC >> gvs[EVERY_MEM, is_label_operand_def]) >>
  metis_tac[is_label_operand_def]
QED

Theorem alloc_run_concat_void_frame:
  shape_stable R /\ (opc = MCOPY \/ opc = MSTORE) ==>
  alloc_run (\s. shape_state s /\ R s /\ EVERY (plain_operand s) ops)
    (emit_void opc ops) (\u s. shape_state s /\ R s)
Proof
  strip_tac >> irule alloc_run_conseq >>
  irule_at Any (Q.INST [`internal` |-> `F`] alloc_run_fresh_shape_frame) >>
  irule_at Any shape_step_emit_void_pre >> irule_at Any alloc_run_emit_void_fresh >>
  qexistsl [`R`, `\s. EVERY (plain_operand s) ops`] >>
  gvs[lowered_inst_ok_def, mk_inst_def, label_or_plain_def,
    raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
    is_param_opcode_def, is_read0_opcode_def, label_positions_ok_def,
    is_terminator_def, EVERY_MEM, plain_operand_def] >>
  rpt strip_tac >> rpt (CASE_TAC >> gvs[EVERY_MEM, is_label_operand_def]) >>
  metis_tac[is_label_operand_def]
QED

Theorem alloc_run_concat_op_bind:
  shape_stable R /\ (opc = ADD \/ opc = MLOAD) /\
  (!s. R s ==> EVERY (plain_operand s) ops) /\
  (!v. alloc_run (\s. shape_state s /\ R s /\ plain_operand s v) (k v) Q) ==>
  alloc_run (\s. shape_state s /\ R s) (comp_bind (emit_op opc ops) k) Q
Proof
  strip_tac >> irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ R s /\ plain_operand s v` >> simp[] >>
  irule alloc_run_conseq >> irule_at Any alloc_run_concat_op_frame >>
  qexists `R` >> simp[]
QED

Theorem alloc_run_concat_void_bind:
  shape_stable R /\ (opc = MCOPY \/ opc = MSTORE) /\
  (!s. R s ==> EVERY (plain_operand s) ops) /\
  (!v. alloc_run (\s. shape_state s /\ R s) (k v) Q) ==>
  alloc_run (\s. shape_state s /\ R s) (comp_bind (emit_void opc ops) k) Q
Proof
  strip_tac >> irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ R s` >> simp[] >>
  irule alloc_run_conseq >> irule_at Any alloc_run_concat_void_frame >>
  qexists `R` >> simp[]
QED

Theorem alloc_run_compile_concat_frame:
  !es infos R.
  shape_stable R /\
  (!e. MEM e es ==>
    shape_step F compiler_label (\s. cenv_shape_ok s ce)
      (cfn ce (expr_type e) e) (\v s. value_shape_ok s v) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (cfn ce (expr_type e) e) (\v s. T)) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce /\ R s /\
      EVERY (plain_operand s) [data_ptr;off_ptr])
    (compile_concat cfn ce es data_ptr infos off_ptr)
    (\u s. shape_state s /\ cenv_shape_ok s ce /\ R s /\
      EVERY (plain_operand s) [data_ptr;off_ptr])
Proof
  Induct
  >- simp[compile_concat_def, comp_return_def, alloc_run_def, alloc_frame_refl] >>
  rpt gen_tac >> strip_tac >> Cases_on `infos`
  >- simp[compile_concat_def, comp_return_def, alloc_run_def, alloc_frame_refl] >>
  rename1 `compile_concat _ _ _ _ (info::_) _` >> PairCases_on `info` >>
  simp[compile_concat_def, comp_ignore_bind_def] >>
  IF_CASES_TAC >> simp[] >> irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ (cenv_shape_ok s ce /\ R s /\
    EVERY (plain_operand s) [data_ptr;off_ptr]) /\ plain_operand s v` >>
  (reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_lower_value_frame >>
      qexistsl [`F`, `\s. R s /\ EVERY (plain_operand s) [data_ptr;off_ptr]`] >>
      simp[shape_stable_conj, shape_stable_plain_operands] >> fs[MEM] >> metis_tac[])) >>
  qx_gen_tac `v` >> simp[] >>
  rpt (FIRST [ho_match_mp_tac alloc_run_concat_op_bind,
      ho_match_mp_tac alloc_run_concat_void_bind] >>
    simp[SRULE [is_label_operand_def]
      (Q.INST [`op` |-> `Lit w`] (SPEC_ALL plain_operand_def))] >>
    (conj_tac >- (rpt (ho_match_mp_tac shape_stable_conj >> conj_tac) >>
      simp[cenv_shape_ok_stable,
        SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands)])) >> rpt gen_tac) >>
  irule alloc_run_conseq >>
  first_x_assum (qspec_then `t` (irule_at Any)) >>
  qexists `R` >> simp[] >> fs[MEM] >> metis_tac[]
QED
