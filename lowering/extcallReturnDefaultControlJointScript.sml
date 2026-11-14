(* Joint routing edges for the default-return shell. *)
Theory extcallReturnDefaultControlJoint
Ancestors
  extcallReturnDefaultWordJoint extcallReturnDefaultRouting fragGasCopyLoop
  externalEntryProps context emitHelper emitHelperProps fragExec fragExecPtr venomMemDefs venomState venomInst
  venomExecSemantics ptrDiscipline compileEnv ptrSafeRun contextCodegenRel codegenRel

Theorem return_default_join_joint:
  emit_inst JMP [Label lbl] [] a = ((),b) /\ fn_has_code a b func /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  s.vs_current_bb = a.cs_current_bb /\ s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK (jump_to lbl s),G,tn)
Proof
  strip_tac >> gen_tac >>
  drule_all emitted_jump_common_instruction >> strip_tac >>
  irule copy_jmp_origin_ptr >> simp[] >> qexists_tac `a.cs_next_id` >> simp[]
QED

Theorem return_default_select_joint:
  emit_inst JNZ [test;Label yes;Label no] [] a = ((),b) /\
  fn_has_code a b func /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  allocas_from lo s /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  eval_operand test s = SOME (if empty then 1w else 0w) /\
  op_taint tn test = {} ==>
  !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (jump_to (if empty then yes else no) s),G,tn)
Proof
  strip_tac >> gen_tac >>
  `b.cs_current_bb = a.cs_current_bb /\
   b.cs_current_insts = a.cs_current_insts ++
     [mk_inst a.cs_next_id JNZ [test;Label yes;Label no] []]` by
    gvs[emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  irule copy_jump_origin_ptr >> simp[] >>
  qexists_tac `mk_inst a.cs_next_id JNZ [test;Label yes;Label no] []` >>
  simp[mk_inst_def] >>
  conj_tac >- (Cases_on `empty` >> simp[step_inst_base_opcode_eqs, mk_inst_def]) >>
  conj_tac >- (first_x_assum (qspec_then `0` mp_tac) >> simp[mk_inst_def]) >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
    allocas_from_def, source_memory_write_ranges_def, source_memory_read_ranges_def,
    GSYM op_taint_def] >>
  conj_tac >- (gen_tac >> Cases_on `op = test` >> gvs[] >> Cases_on `op` >> gvs[op_taint_def]) >>
  Cases_on `empty` >> simp[GSYM mk_inst_def, step_inst_non_invoke,
    step_inst_base_opcode_eqs, mk_inst_def, jump_to_def]
QED
