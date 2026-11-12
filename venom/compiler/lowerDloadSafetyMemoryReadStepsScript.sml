(* Shared successful byte-memory read effects, independent of read opcode. *)
Theory lowerDloadSafetyMemoryReadSteps
Ancestors
  lowerDloadSafetyUpdates ptrDiscipline venomExecSemantics venomState
  venomInst memLocDefs codegenRel contextCodegenRel finite_map list pred_set

Theorem ld_memory_read_success:
  MEM inst.inst_opcode [MLOAD;ILOAD] /\ step_inst_base inst s = OK s' ==>
  ?out x. inst.inst_outputs = [out] /\ s' = update_var out x s
Proof
  strip_tac >> gvs[MEM] >>
  (qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
   pure_once_rewrite_tac[step_inst_base_def] >>
   asm_rewrite_tac[opcode_case_def] >>
   simp[exec_read1_def, AllCaseEqs()] >>
   rpt strip_tac >> gvs[] >> metis_tac[])
QED

Theorem ld_memory_read_taint:
  MEM inst.inst_opcode [MLOAD;ILOAD] ==>
  step_taint inst s (update_var v x s) tn =
    tn with t_var := set_var_taint tn.t_var inst.inst_outputs (out_taint tn inst s)
Proof
  strip_tac >>
  `written_taint tn inst s = {}` by
    (namedCases_on `inst.inst_operands` ["", "a rest"]
     >- gvs[MEM, written_taint_def] >>
     namedCases_on `rest` ["", "b tail"]
     >- gvs[MEM, written_taint_def] >>
     namedCases_on `tail` ["", "c more"]
     >- gvs[MEM, written_taint_def] >>
     Cases_on `more` >> gvs[MEM, written_taint_def]) >>
  gvs[MEM] >>
  (simp[step_taint_def, mem_taint_def, update_var_def,
        new_site_bytes_def, step_writes_def, range_bytes_def,
        source_memory_write_ranges_def, store_taint_def, adopt_reset_def,
        imm_taint_def, FLOOKUP_DEF, taint_component_equality] >> SET_TAC[])
QED
