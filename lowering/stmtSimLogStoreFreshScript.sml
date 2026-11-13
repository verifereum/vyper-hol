(* Stores preserve names above the generated output frontier. *)
Theory stmtSimLogStoreFresh
Ancestors
  stmtSimLogStoreContinue stmtSimLogTopics stmtSimLogDataRun
  freshWrites exprLoweringProps emitHelper emitHelperProps exprSimBufferStore context stmtLowering compileEnv loweringStateRelDefs
  venomExecSemantics venomInst venomState words list rich_list arithmetic finite_map ASCIInumbers

Theorem log_store_scalar_outputs[local]:
  supported_scalar_type ty /\ compile_store_memory ce src dst ty ty sa = ((),sb) /\
  sb.cs_next_var <= nv ==>
  EVERY (\i. MEM i.inst_opcode [ADD; AND; MLOAD; MSTORE; MCOPY; NOT] /\
    EVERY (\x. ?n. x = STRING #"%" (toString n) /\ n < nv)
    i.inst_outputs) (emitted_insts sa sb)
Proof
  strip_tac >>
  `is_word_type ty \/ is_bytestring_type ty` by
    (drule log_scalar_topic_shape >> Cases_on `is_bytestring_type ty` >> simp[]) >>
  Cases_on `is_word_type ty` >>
  qpat_x_assum `compile_store_memory _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_store_memory_def, compile_store_bytestring_def,
    compile_bytestring_copy_len_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[] >> simp[emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def] >> rpt conj_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem log_store_step_var[local]:
  MEM inst.inst_opcode [ADD; AND; MLOAD; MSTORE; MCOPY; NOT] /\
  step_inst_base inst s = OK t /\ ~MEM x inst.inst_outputs ==>
  FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x
Proof
  strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  fs[] >> simp[step_inst_base_opcode_eqs] >> strip_tac
  >>~- ([`exec_pure2 _ _ _ = OK _`],
    drule (cj 2 exec_pure_ok_update) >> strip_tac >>
    gvs[update_var_def, FLOOKUP_UPDATE])
  >>~- ([`exec_pure1 _ _ _ = OK _`],
    drule (cj 1 exec_pure_ok_update) >> strip_tac >>
    gvs[update_var_def, FLOOKUP_UPDATE])
  >> gvs[exec_read0_def, exec_read1_def, exec_write2_def, AllCaseEqs(),
         update_var_def, FLOOKUP_UPDATE, mstore_def, mcopy_def,
         write_memory_with_expansion_def]
QED

Theorem log_store_code_var[local]:
  !code s t x. EVERY (\i. MEM i.inst_opcode [ADD; AND; MLOAD; MSTORE; MCOPY; NOT] /\
    ~MEM x i.inst_outputs) code /\ run_inst_seq code s = OK t ==>
  FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x
Proof
  Induct >> simp[run_inst_seq_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  drule_at (Pat `step_inst_base _ _ = _`) log_store_step_var >> simp[] >>
  disch_then (qspec_then `x` mp_tac) >> simp[] >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem log_store_code_fresh[local]:
  EVERY (\i. MEM i.inst_opcode [ADD; AND; MLOAD; MSTORE; MCOPY; NOT] /\
    EVERY (\x. ?n. x = STRING #"%" (toString n) /\ n < nv) i.inst_outputs) code /\
  run_inst_seq code s = OK t /\ nv <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st s ==> fresh_vars_wrt limit_st t
Proof
  strip_tac >> simp[fresh_vars_wrt_def] >> rpt strip_tac >>
  `FLOOKUP t.vs_vars (STRING #"%" (toString n)) =
   FLOOKUP s.vs_vars (STRING #"%" (toString n))` by
    (irule log_store_code_var >> goal_assum (drule_at Any) >>
     qpat_x_assum `EVERY _ code` mp_tac >> simp[EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> strip_tac >> simp[] >>
     qpat_x_assum `!x. MEM x _.inst_outputs ==> _` drule >> strip_tac >>
     gvs[toString_inj] >> decide_tac) >>
  `STRING #"%" (toString n) NOTIN FDOM s.vs_vars` by
    (fs[fresh_vars_wrt_def] >> first_x_assum irule >> simp[]) >>
  gvs[FLOOKUP_DEF]
QED

Theorem log_store_data_outputs[local]:
  !xs buf off sa sb nv. EVERY (supported_scalar_type o SND) xs /\
    compile_log_store_data ce xs (MAP SND xs) buf off sa = ((),sb) /\ sb.cs_next_var <= nv ==>
    EVERY (\i. MEM i.inst_opcode [ADD; AND; MLOAD; MSTORE; MCOPY; NOT] /\
      EVERY (\x. ?n. x = STRING #"%" (toString n) /\ n < nv)
        i.inst_outputs) (emitted_insts sa sb)
Proof
  Induct_on `xs`
  >- simp[compile_log_store_data_def, comp_return_def, emitted_insts_def] >>
  gen_tac >> PairCases_on `h` >> simp[] >> rpt gen_tac >> strip_tac >>
  drule_all compile_log_store_data_scalar_split >> strip_tac >>
  drule_all compile_log_store_data_shape >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  drule buffer_store_memory_shape >> strip_tac >>
  `sn.cs_next_var <= nv` by decide_tac >>
  drule_all log_store_scalar_outputs >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  `emitted_insts sm sb = emitted_insts sm sn ++ emitted_insts sn sb` by
    (irule emitted_insts_append >> simp[]) >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> simp[]) >>
  simp[] >>
  qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def,
    fresh_id_def, emit_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND, mk_inst_def] >>
  qexists_tac `sa.cs_next_var` >> simp[] >> decide_tac
QED

Theorem log_store_data_fresh:
  EVERY (supported_scalar_type o SND) xs /\
  compile_log_store_data ce xs (MAP SND xs) buf off sa = ((),sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  sb.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  fresh_vars_wrt limit_st t
Proof
  strip_tac >>
  `EVERY (\i. MEM i.inst_opcode [ADD; AND; MLOAD; MSTORE; MCOPY; NOT] /\
    EVERY (\x. ?n. x = STRING #"%" (toString n) /\ n < sb.cs_next_var)
      i.inst_outputs) (emitted_insts sa sb)` by
    (irule log_store_data_outputs >> simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all log_store_code_fresh >> simp[]
QED
