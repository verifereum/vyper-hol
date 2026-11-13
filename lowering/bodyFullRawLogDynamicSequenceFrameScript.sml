Theory bodyFullRawLogDynamicSequenceFrame
Ancestors
  fragGasSeqPtr exprLoweringProps emitHelper compileEnv exprLowering
  allocaHistory fragExec venomInst venomState list rich_list arithmetic
  venomExecSemantics ptrDiscipline memSafeRun finite_map pred_set codegenRel

Theorem raw_log_dynamic_sequence_history:
  emit_op MLOAD [data_op] sm = (len_op,s1) /\
  emit_op ADD [data_op;Lit 32w] s1 = (ptr_op,s2) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [len_op;ptr_op]) [] s2 = ((),sb) /\
  fn_has_code sm sb func /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  alloca_history func s /\
  u.vs_allocas = s.vs_allocas /\
  u.vs_current_bb = s.vs_current_bb /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  alloca_history func u
Proof
  strip_tac >>
  gvs[emit_op_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  gvs[alloca_history_def, fn_has_code_def] >> rpt strip_tac >>
  Cases_on `k < LENGTH sm.cs_current_insts`
  >- metis_tac[] >>
  gvs[IS_PREFIX_APPEND, get_instruction_def, EL_APPEND_EQN, mk_inst_def] >>
  `k - LENGTH sm.cs_current_insts < 3` by decide_tac >>
  `k - LENGTH sm.cs_current_insts = 0 \/
   k - LENGTH sm.cs_current_insts = 1 \/
   k - LENGTH sm.cs_current_insts = 2` by decide_tac >> gvs[]
QED

Theorem raw_log_dynamic_prepare_memory_taint:
  emit_op MLOAD [data_op] sm = (len_op,s1) /\
  emit_op ADD [data_op;Lit 32w] s1 = (ptr_op,s2) /\
  inst_seq_ptr D lo ctx func PG G tn (emitted_insts sm s2) s G1 tn1 ==>
  tn1.t_mem = tn.t_mem
Proof
  strip_tac >>
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_var_def, fresh_id_def, emit_def] >>
  fs[emitted_insts_def, APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, DROP_LENGTH_APPEND, APPEND]) >>
  fs[inst_seq_ptr_def] >>
  Cases_on `step_inst_base
    (mk_inst sm.cs_next_id MLOAD [data_op] [STRING #"%" (toString sm.cs_next_var)]) s` >> gvs[] >>
  rename1 `step_inst_base _ s = OK v` >>
  Cases_on `step_inst_base
    (mk_inst (sm.cs_next_id+1) ADD [data_op;Lit 32w]
      [STRING #"%" (toString (sm.cs_next_var+1))])
    (v with vs_inst_idx := SUC s.vs_inst_idx)` >> gvs[] >>
  gvs[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def, exec_pure2_def,
      AllCaseEqs(), update_var_def] >>
  simp[step_taint_def, mem_taint_def, new_site_bytes_def, step_writes_def,
       source_memory_write_ranges_def, written_taint_def, range_bytes_def,
       mk_inst_def, finite_mapTheory.FLOOKUP_DEF] >> SET_TAC[]
QED
