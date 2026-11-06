Theory bodyPtrTypeBuiltinsScalarOps
Ancestors
  bodyPtrTypeBuiltinsIszero bodyPtrTypeBuiltinsScalarTransfer
  decoderGhostFramePtr ptrSafeRun ptrDiscipline venomExecSemantics
  venomState venomInst codegenRel contextCodegenRel finite_map pred_set list

Theorem convert_scalar_run_shape:
  MEM opc [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  step_inst_base (mk_inst id opc [x;y] [z]) s = OK u ==>
  ?w. u = update_var z w s
Proof
  simp[MEM] >> strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[mk_inst_def, instruction_accessors,
                  instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure2_def] >>
  Cases_on `eval_operand x s` >> simp[] >>
  Cases_on `eval_operand y s` >> simp[] >> strip_tac >> gvs[] >>
  irule_at Any EQ_REFL
QED

Theorem convert_scalar_runtime_frame:
  MEM opc [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  step_inst_base (mk_inst id opc [x;y] [z]) s = OK u ==>
  (u with vs_vars := s.vs_vars) = s /\
  (!p. p <> z ==> lookup_var p u = lookup_var p s)
Proof
  strip_tac >> drule_all convert_scalar_run_shape >> strip_tac >>
  gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem convert_scalar_ptr_inst_ok:
  MEM opc [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  op_prov G x = NONE /\ op_prov G y = NONE /\
  op_taint tn x = {} /\ op_taint tn y = {} /\
  ~ctx_has_dalloca ctx /\
  step_inst_base (mk_inst id opc [x;y] [z]) s = OK u ==>
  ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id opc [x;y] [z]) s
Proof
  strip_tac >> drule_all convert_scalar_run_shape >> strip_tac >>
  gvs[MEM] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def,
       allocas_from_def] >>
  simp[GSYM mk_inst_def, step_inst_non_invoke] >>
  simp[update_var_def] >>
  rpt strip_tac >> gvs[op_prov_def, FLOOKUP_DEF] >> metis_tac[]
QED

Theorem convert_scalar_output_prov:
  MEM opc [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] ==>
  op_prov (step_prov PG G (mk_inst id opc [x;y] [z]) u) (Var z) = NONE
Proof
  strip_tac >> simp[op_prov_def] >> irule step_prov_output_none >>
  simp[mk_inst_def] >> irule out_prov_clearing_none >> gvs[MEM, mk_inst_def]
QED

Theorem convert_scalar_ghost_update:
  MEM opc [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  op_taint tn x = {} /\ op_taint tn y = {} /\
  step_inst_base (mk_inst id opc [x;y] [z]) s = OK u ==>
  step_taint (mk_inst id opc [x;y] [z]) s u tn =
    (tn with t_var := tn.t_var |+ (z,{}))
Proof
  strip_tac >> drule_all convert_scalar_run_shape >> strip_tac >>
  `new_site_bytes s u = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF,
         EXTENSION, SF CONJ_ss] >>
  gvs[MEM] >>
  simp[step_taint_def, set_var_taint_def, mk_inst_def,
       mem_taint_def, step_writes_def, source_memory_write_ranges_def,
       written_taint_def, store_taint_def, adopt_reset_def,
       imm_taint_def, range_bytes_def, out_taint_def, taint_component_equality] >>
  Cases_on `eval_operand x s` >> simp[shift_taint_def, EXTENSION]
QED

Theorem convert_scalar_ghost_frame:
  p <> z ==>
  FLOOKUP (step_prov PG G (mk_inst id opc [x;y] [z]) u) p = FLOOKUP G p /\
  op_taint (step_taint (mk_inst id opc [x;y] [z]) s u tn) (Var p) =
    op_taint tn (Var p)
Proof
  strip_tac >> conj_tac
  >- (irule step_prov_other_output >> simp[mk_inst_def]) >>
  irule step_taint_other_output >> simp[mk_inst_def]
QED

Theorem convert_scalar_taint_result_frame:
  MEM opc [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  op_taint tn x = {} /\ op_taint tn y = {} /\
  step_inst_base (mk_inst id opc [x;y] [z]) s = OK u ==>
  op_taint (step_taint (mk_inst id opc [x;y] [z]) s u tn) (Var z) = {} /\
  (step_taint (mk_inst id opc [x;y] [z]) s u tn).t_mem = tn.t_mem /\
  (step_taint (mk_inst id opc [x;y] [z]) s u tn).t_stor = tn.t_stor /\
  (step_taint (mk_inst id opc [x;y] [z]) s u tn).t_trans = tn.t_trans /\
  (step_taint (mk_inst id opc [x;y] [z]) s u tn).t_imm = tn.t_imm
Proof
  strip_tac >> drule_all convert_scalar_ghost_update >>
  simp[op_taint_def, FLOOKUP_UPDATE]
QED

Theorem convert_scalar_no_abort:
  MEM opc [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] ==>
  step_inst_base (mk_inst id opc [x;y] [z]) s <> Abort err t
Proof
  simp[MEM] >> strip_tac >> gvs[] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[mk_inst_def, instruction_accessors,
                  instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure2_def, AllCaseEqs()]
QED

Theorem scalar_iszero_no_abort:
  step_inst_base (mk_inst id ISZERO [x] [z]) s <> Abort err t
Proof
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[mk_inst_def, instruction_accessors,
                  instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure1_def, AllCaseEqs()]
QED

Theorem convert_scalar_opcode_filter:
  MEM opc [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] ==>
  opc <> INVOKE /\ ~is_terminator opc /\ opc <> GAS
Proof
  simp[MEM] >> strip_tac >> gvs[is_terminator_def]
QED
