Theory lowerDloadGuardProducer
Ancestors
  lowerDloadOwnership ptrDiscipline venomExecSemantics venomState venomInst
  list finite_map memLocDefs pred_set codegenRel

Theorem ld_guard_backward:
  MEM i.inst_opcode [NOP; ASSERT; ASSERT_UNREACHABLE] /\
  eval_operands i.inst_operands s = eval_operands i.inst_operands t /\
  step_inst ft CT i t = OK t' ==>
  t' = t /\ step_inst fs CS i s = OK s
Proof
  simp[MEM] >> strip_tac >>
  qpat_x_assum `step_inst ft _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >> asm_rewrite_tac[step_inst_base_def, opcode_case_def] >>
  gvs[AllCaseEqs(), eval_operands_def] >>
  simp[step_inst_non_invoke] >> asm_rewrite_tac[step_inst_base_def, opcode_case_def] >>
  strip_tac >> gvs[eval_operands_def, AllCaseEqs()]
QED

Theorem ld_guard_prov:
  MEM i.inst_opcode [NOP; ASSERT; ASSERT_UNREACHABLE] ==>
  ld_step_prov AP AG L i = ld_set_prov AG i.inst_outputs NONE
Proof
  simp[MEM] >> strip_tac >> simp[ld_step_prov_def, ld_out_prov_def]
QED

Theorem ld_guard_taint:
  MEM i.inst_opcode [NOP; ASSERT; ASSERT_UNREACHABLE] ==>
  step_taint i s s tn =
    tn with t_var := set_var_taint tn.t_var i.inst_outputs {}
Proof
  simp[MEM] >> strip_tac >>
  simp[step_taint_def, mem_taint_def, new_site_bytes_def,
    step_writes_def, source_memory_write_ranges_def,
    store_taint_def, imm_taint_def, adopt_reset_def,
    range_bytes_def, FLOOKUP_DEF, EXTENSION, SF CONJ_ss] >>
  Cases_on `tn` >> simp[] >>
  namedCases_on `i.inst_operands` ["", "a ops1"] >>
  simp[written_taint_def, out_taint_def, taint_component_equality] >>
  Cases_on `eval_operand a s` >> simp[] >>
  namedCases_on `ops1` ["", "b ops2"] >>
  simp[written_taint_def, out_taint_def, taint_component_equality, AllCaseEqs()] >>
  namedCases_on `ops2` ["", "c ops3"] >>
  simp[written_taint_def, out_taint_def, taint_component_equality, AllCaseEqs()] >>
  Cases_on `ops3` >> simp[written_taint_def, out_taint_def, taint_component_equality]
QED
