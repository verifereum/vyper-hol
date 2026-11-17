Theory bodyFullStoreSlotsStaticExit
Ancestors
  augAssignFullStore fragGasEmitCtrl fragGasOriginPtr ptrSafeRun ptrDiscipline
  emitHelper emitHelperProps compileEnv exprLoweringProps fragExec contextCodegenRel codegenRel
  venomExecSemantics venomState venomInst gasEvents gasCount memSafeRun
  unitTransformDefs list

Theorem store_slots_checked_store_static:
  emit_void (if tr then TSTORE else SSTORE) [dst;value] ca = ((),cb) /\
  fn_has_code ca cb func /\
  u.vs_current_bb = ca.cs_current_bb /\
  u.vs_inst_idx = LENGTH ca.cs_current_insts /\
  gas_origin_ptr_edge (D0,lo,explicit,ctx,func,PG) (u,G,tn) []
    (OK v,G1,tn1) ==>
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (u with vs_call_ctx := (u.vs_call_ctx with cc_static := T),G,tn) []
    (Abort ExHalt_abort (halt_state (set_returndata []
      (u with vs_call_ctx := (u.vs_call_ctx with cc_static := T)))),G,tn)) /\
  ?bb inst.
    lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb u.vs_inst_idx = SOME inst /\
    inst.inst_opcode = (if tr then TSTORE else SSTORE) /\
    step_inst_base inst
      (u with vs_call_ctx := (u.vs_call_ctx with cc_static := T)) =
      Abort ExHalt_abort (halt_state (set_returndata []
        (u with vs_call_ctx := (u.vs_call_ctx with cc_static := T))))
Proof
  strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_same_blocks >> strip_tac >> fs[same_blocks_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  qabbrev_tac `i = mk_inst ca.cs_next_id (if tr then TSTORE else SSTORE)
    [dst;value] []` >>
  `get_instruction bb u.vs_inst_idx = SOME i` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[Abbr `i`]) >>
  `~is_terminator i.inst_opcode` by
    (Cases_on `tr` >> simp[Abbr `i`, mk_inst_def, is_terminator_def]) >>
  drule gas_origin_ptr_edge_common_fuel >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (REPEAT_TCL CHOOSE_THEN (REPEAT_TCL CONJUNCTS_THEN assume_tac))) >>
  gnvs[] >>
  `ptr_inst_ok D0 lo fuel ctx func G tn i u` by
    gvs[ptr_safe_step_def] >>
  `?addr w. eval_operand dst u = SOME addr /\
            eval_operand value u = SOME w` by
    (Cases_on `tr` >>
     gvs[Abbr `i`, step_inst_non_invoke, step_inst_base_SSTORE, step_inst_base_TSTORE,
         mk_inst_def, exec_write2_def, eval_operands_def, AllCaseEqs(),
         is_terminator_def, fragExecTheory.exit_result_def]) >>
  qabbrev_tac `us = u with vs_call_ctx := (u.vs_call_ctx with cc_static := T)` >>
  `!op. eval_operand op us = eval_operand op u` by
    (gen_tac >> Cases_on `op` >>
     simp[Abbr `us`, eval_operand_def, lookup_var_def]) >>
  `step_inst_base i us =
     Abort ExHalt_abort (halt_state (set_returndata [] us))` by
    (Cases_on `tr` >>
     simp[Abbr `i`, step_inst_base_SSTORE, step_inst_base_TSTORE, mk_inst_def,
          Abbr `us`, eval_operands_def] >>
     fs[eval_operand_def, lookup_var_def]) >>
  reverse conj_tac
  >- simp[Abbr `i`, mk_inst_def] >>
  `op_taint tn dst = {}` by
    (qpat_x_assum `ptr_inst_ok _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[ptr_inst_ok_def, taint_ok_def, Abbr `i`, mk_inst_def] >>
     strip_tac >> spose_not_then assume_tac >>
     first_x_assum (qspec_then `dst` mp_tac) >>
     Cases_on `tr` >> simp[] >> metis_tac[]) >>
  `allocas_from lo us /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp us)` by
    (gvs[ptr_inst_ok_def, Abbr `us`, allocas_from_def, allocas_below_fmp_def] >>
     metis_tac[]) >>
  gen_tac >> Cases_on `op_taint tn value = {}`
  >- (irule storage_emit_static_origin_ptr >> simp[Abbr `us`] >>
      qexistsl_tac [`addr`, `dst`, `ca`, `cb`, `tr`, `value`, `w`] >> simp[]) >>
  `ptr_inst_ok D lo 0 ctx func G tn i us` by
    (fs[ptr_inst_ok_def] >>
     Cases_on `tr` >>
     gvs[Abbr `i`, ptr_inst_ok_def, access_ok_def, taint_ok_def,
         mk_inst_def, source_memory_write_ranges_def,
         source_memory_read_ranges_def, fixed_source_write_range_def,
         Abbr `us`, allocas_from_def, allocas_below_fmp_def,
         step_inst_non_invoke] >> rpt strip_tac >> gvs[]) >>
  irule exit_inst_origin_ptr >> simp[exit_result_def, Abbr `us`] >>
  Cases_on `tr` >>
  simp[Abbr `i`, mk_inst_def, step_inst_non_invoke,
       gas_events_step_def, gas_count_step_def, exit_result_def,
       mem_safe_step_non_invoke, inst_mem_below_frontier_def,
       inst_dload_in_section_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def]
QED
