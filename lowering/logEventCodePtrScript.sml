(* Compiler interval facts for the post-topic event suffix. *)
Theory logEventCodePtr
Ancestors
  logEncoderEntryPtr stmtSimLogEncodeFields abiEncoderCounters
  abiBuiltinAllocation abiEmptyAllocate abiDecoderIndexInit stmtSimLogDataRun
  emitHelperProps exprLoweringProps contextCodegenRelProps loweringSlice
  compileEnv context list arithmetic rich_list fragExec loweringHalt

Theorem log_tuple_encoder_interval:
  EVERY supported_scalar_type tys /\
  SUM (MAP (type_memory_bytes ce) tys) < dimword(:256) /\
  compile_abi_encode_to_buf dst src
    (type_to_abi_enc_info ce.ce_struct_fields ce (TupleT tys)) sa = (out,sb) ==>
  inst_extends sa sb /\ same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var
Proof
  strip_tac >>
  drule_all (ISPEC ``(ce:compile_env).ce_struct_fields``
    (Q.GEN `sf` scalar_tuple_encoder_shape)) >> strip_tac >> gvs[]
  >- (drule log_encode_copy_safe >> strip_tac >>
      drule abi_encoder_counters >> simp[]) >>
  drule_all log_encode_dynamic_safe >> strip_tac >>
  drule abi_encoder_counters >> simp[]
QED

val _ = if null (hyp log_tuple_encoder_interval) then ()
  else raise Fail "log_tuple_encoder_interval is not closed";

Theorem emitted_interval_split:
  inst_extends a b /\ inst_extends b c /\
  same_blocks a b /\ same_blocks b c /\ fn_has_code a c func /\
  isPREFIX (emitted_insts a c) (DROP j code) ==>
  fn_has_code a b func /\ fn_has_code b c func /\
  isPREFIX (emitted_insts a b) (DROP j code) /\
  isPREFIX (emitted_insts b c) (DROP (j + LENGTH (emitted_insts a b)) code)
Proof
  strip_tac >>
  `cs_extends a b /\ cs_extends b c` by
    (conj_tac >> irule cs_extends_same_block >>
     fs[same_blocks_def, inst_extends_def, rich_listTheory.IS_PREFIX_APPEND] >> metis_tac[]) >>
  drule_all fn_has_code_split >> strip_tac >>
  `emitted_insts a c = emitted_insts a b ++ emitted_insts b c` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  qpat_x_assum `isPREFIX (emitted_insts a c) _` mp_tac >>
  simp[rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
  conj_tac >- metis_tac[APPEND_ASSOC] >>
  once_rewrite_tac[ADD_COMM] >>
  rewrite_tac[GSYM DROP_DROP_T] >> asm_rewrite_tac[] >>
  qexists_tac `l` >> rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND]
QED

Theorem log_alloc_buffer_interval:
  compile_alloc_buffer cap sa = (buf,sb) ==>
  inst_extends sa sb /\ same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var
Proof
  strip_tac >> drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule compile_alloc_buffer_insts >> simp[same_blocks_def, inst_extends_def]
QED

Theorem log_data_trace_intervals:
  EVERY supported_scalar_type (MAP SND xs) /\
  SUM (MAP (type_memory_bytes ce) (MAP SND xs)) < dimword(:256) /\
  compile_alloc_buffer cap st = (src,s1) /\
  compile_log_store_data ce xs src.buf_operand 0 s1 = ((),s2) /\
  compile_alloc_buffer outcap s2 = (dst,s3) /\
  compile_abi_encode_to_buf dst.buf_operand src.buf_operand
    (type_to_abi_enc_info ce.ce_struct_fields ce (TupleT (MAP SND xs))) s3 = (len,s4) /\
  emit_inst LOG operands [] s4 = ((),sb) ==>
  inst_extends st s1 /\ inst_extends s1 s2 /\ inst_extends s2 s3 /\
  inst_extends s3 s4 /\ inst_extends s4 sb /\
  same_blocks st s1 /\ same_blocks s1 s2 /\ same_blocks s2 s3 /\
  same_blocks s3 s4 /\ same_blocks s4 sb /\
  st.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= s2.cs_next_var /\
  s2.cs_next_var <= s3.cs_next_var /\ s3.cs_next_var <= s4.cs_next_var /\
  s4.cs_next_var = sb.cs_next_var
Proof
  strip_tac >>
  `inst_extends st s1 /\ same_blocks st s1 /\ st.cs_next_var <= s1.cs_next_var` by
    metis_tac[log_alloc_buffer_interval] >>
  `inst_extends s2 s3 /\ same_blocks s2 s3 /\ s2.cs_next_var <= s3.cs_next_var` by
    metis_tac[log_alloc_buffer_interval] >>
  `EVERY (supported_scalar_type o SND) xs` by fs[EVERY_MAP, combinTheory.o_DEF] >>
  drule_all compile_log_store_data_shape >> strip_tac >>
  drule_all log_tuple_encoder_interval >> strip_tac >>
  drule emitted_insts_emit_inst >> strip_tac >>
  `inst_extends s4 sb` by
    (gvs[emitHelperTheory.emit_inst_def, compileEnvTheory.emit_def,
        compileEnvTheory.fresh_id_def, compileEnvTheory.comp_bind_def,
        compileEnvTheory.comp_return_def, inst_extends_def]) >>
  fs[inst_extends_def, same_blocks_def]
QED

Theorem emitted_four_intervals:
  inst_extends a b /\ inst_extends b c /\ inst_extends c d /\ inst_extends d e /\
  same_blocks a b /\ same_blocks b c /\ same_blocks c d /\ same_blocks d e /\
  fn_has_code a e func /\ isPREFIX (emitted_insts a e) (DROP j code) ==>
  fn_has_code a b func /\ fn_has_code b c func /\ fn_has_code c d func /\
  fn_has_code d e func /\
  isPREFIX (emitted_insts a b) (DROP j code) /\
  isPREFIX (emitted_insts b c) (DROP (j + LENGTH (emitted_insts a b)) code) /\
  isPREFIX (emitted_insts c d)
    (DROP (j + LENGTH (emitted_insts a b) + LENGTH (emitted_insts b c)) code) /\
  isPREFIX (emitted_insts d e)
    (DROP (j + LENGTH (emitted_insts a b) + LENGTH (emitted_insts b c) +
      LENGTH (emitted_insts c d)) code)
Proof
  strip_tac >>
  `inst_extends c e /\ same_blocks c e` by
    metis_tac[inst_extends_trans, same_blocks_trans] >>
  `inst_extends b e /\ same_blocks b e` by
    metis_tac[inst_extends_trans, same_blocks_trans] >>
  drule_all (Q.INST [`a` |-> `a`, `b` |-> `b`, `c` |-> `e`] emitted_interval_split) >>
  strip_tac >>
  drule_all (Q.INST [`a` |-> `b`, `b` |-> `c`, `c` |-> `e`] emitted_interval_split) >>
  strip_tac >>
  drule_all (Q.INST [`a` |-> `c`, `b` |-> `d`, `c` |-> `e`] emitted_interval_split) >>
  strip_tac >> asm_rewrite_tac[]
QED

Theorem log_data_trace_code:
  EVERY supported_scalar_type (MAP SND xs) /\
  SUM (MAP (type_memory_bytes ce) (MAP SND xs)) < dimword(:256) /\
  compile_alloc_buffer cap st = (src,s1) /\
  compile_log_store_data ce xs src.buf_operand 0 s1 = ((),s2) /\
  compile_alloc_buffer outcap s2 = (dst,s3) /\
  compile_abi_encode_to_buf dst.buf_operand src.buf_operand
    (type_to_abi_enc_info ce.ce_struct_fields ce (TupleT (MAP SND xs))) s3 = (len,s4) /\
  emit_inst LOG operands [] s4 = ((),sb) /\
  fn_has_code st sb func /\ isPREFIX (emitted_insts st sb) (DROP j code) /\
  sb.cs_next_var <= limit_st.cs_next_var ==>
  fn_has_code st s1 func /\ fn_has_code s2 s3 func /\ fn_has_code s3 s4 func /\
  fn_has_code s4 sb func /\ s1.cs_next_var <= s2.cs_next_var /\
  s2.cs_next_var <= limit_st.cs_next_var /\ s4.cs_next_var <= limit_st.cs_next_var /\
  isPREFIX (emitted_insts st s1) (DROP j code) /\
  isPREFIX (emitted_insts s1 s2) (DROP (j + LENGTH (emitted_insts st s1)) code) /\
  isPREFIX (emitted_insts s2 s4)
    (DROP (j + LENGTH (emitted_insts st s1) + LENGTH (emitted_insts s1 s2)) code) /\
  isPREFIX (emitted_insts s4 sb)
    (DROP (j + LENGTH (emitted_insts st s1) + LENGTH (emitted_insts s1 s2) +
      LENGTH (emitted_insts s2 s4)) code) /\
  inst_extends st sb /\
  emitted_insts st sb = emitted_insts st s1 ++ emitted_insts s1 s2 ++
    emitted_insts s2 s4 ++ emitted_insts s4 sb
Proof
  strip_tac >> drule_all log_data_trace_intervals >> strip_tac >>
  `inst_extends s2 s4 /\ same_blocks s2 s4` by
    metis_tac[inst_extends_trans, same_blocks_trans] >>
  drule_all (Q.INST [`a` |-> `st`, `b` |-> `s1`, `c` |-> `s2`,
    `d` |-> `s4`, `e` |-> `sb`] emitted_four_intervals) >> strip_tac >>
  drule_all (Q.INST [`a` |-> `s2`, `b` |-> `s3`, `c` |-> `s4`]
    emitted_interval_split) >> strip_tac >>
  `inst_extends s1 sb` by metis_tac[inst_extends_trans] >>
  `inst_extends st sb` by metis_tac[inst_extends_trans] >>
  `emitted_insts st sb = emitted_insts st s1 ++ emitted_insts s1 sb` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `inst_extends s2 sb` by metis_tac[inst_extends_trans] >>
  `emitted_insts s1 sb = emitted_insts s1 s2 ++ emitted_insts s2 sb` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `emitted_insts s2 sb = emitted_insts s2 s4 ++ emitted_insts s4 sb` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  asm_simp_tac bool_ss [APPEND_ASSOC] >> decide_tac
QED
