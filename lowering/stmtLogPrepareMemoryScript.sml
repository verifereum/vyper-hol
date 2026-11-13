(* Source allocation followed by the checked Log store/encode continuation. *)
Theory stmtLogPrepareMemory
Ancestors
  stmtLogStoreEncodeMemory stmtSimLogSourceAllocate stmtLogSuffixStageMemory loweringStateRelDefs
  stmtSimLogStoreEncode stmtSimLogDataRun abiEncoderCounters abiDecoderReentry
  exprLoweringProps localPtrsProps emitHelperProps stmtSimLogAllocate compileEnv
  fragExec fragExecMem venomMemDefs abiBuiltinAllocation words list arithmetic

Theorem log_data_prepare_run_mem:
  cap = SUM (MAP (type_memory_bytes ce) (MAP SND xs)) /\
  srccap = MAX 32 cap /\
  outcap = MAX 32 (abi_size_bound ce.ce_struct_fields (TupleT (MAP SND xs))) /\
  ei = type_to_abi_enc_info ce.ce_struct_fields ce (TupleT (MAP SND xs)) /\
  compile_alloc_buffer srccap source_st = (srcbuf,start) /\
  fn_has_code source_st start func /\
  compile_log_store_data ce xs srcbuf.buf_operand 0 start = ((),stored_st) /\
  compile_alloc_buffer outcap stored_st = (dst,prepared) /\
  fn_has_code stored_st prepared func /\
  compile_abi_encode_to_buf dst.buf_operand srcbuf.buf_operand ei prepared = (out,end_st) /\
  fn_has_code prepared end_st func /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce source_st /\
  fresh_vars_wrt limit_st s /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  LIST_REL (\arg v. log_arg_rel ce cx sa source_st es s arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v) xs vs /\
  EVERY (\p. (!z. FST p = Var z ==> not_fresh_at source_st z) /\ (!l. FST p <> Label l)) xs /\
  EVERY supported_scalar_type (MAP SND xs) /\ cap < dimword (:256) /\
  abi_size_bound ce.ce_struct_fields (TupleT (MAP SND xs)) < dimword (:256) /\
  LIST_REL (\arg v. !w n. ~is_word_type (SND arg) /\
    eval_operand (FST arg) s = SOME w /\
    ((?bs. v = BytesV bs /\ n = LENGTH bs) \/
     (?str. v = StringV str /\ n = LENGTH str)) ==>
    w2n w + 32 + 32 * ((n+31) DIV 32) <= s.vs_alloca_next) xs vs ==>
  run_inst_seq_mem_ok (emitted_insts source_st end_st) s /\
  (!t. run_inst_seq (emitted_insts source_st end_st) s = OK t ==>
    s.vs_alloca_next <= t.vs_alloca_next) /\
  ?avs actual db.
    vyper_to_abi_list (get_tenv cx) (MAP SND xs) vs = SOME avs /\
    run_inst_seq (emitted_insts source_st end_st) s = OK actual /\
    inst_extends source_st end_st /\ fresh_vars_wrt limit_st actual /\
    eval_operand dst.buf_operand actual = SOME (n2w db) /\
    mem_bytes_at db (LENGTH (enc (Tuple (vyper_to_abi_types (get_tenv cx) (MAP SND xs))) (ListV avs))) actual.vs_memory =
      enc (Tuple (vyper_to_abi_types (get_tenv cx) (MAP SND xs))) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Tuple (vyper_to_abi_types (get_tenv cx) (MAP SND xs))) (ListV avs)))) /\
    stmt_state_rel ctx func ce cx es actual /\
    db < dimword (:256) /\
    LENGTH (enc (Tuple (vyper_to_abi_types (get_tenv cx) (MAP SND xs))) (ListV avs)) < dimword (:256) /\
    (!op w. abi_decoder_operand_live source_st.cs_next_var op /\
      eval_operand op s = SOME w ==> eval_operand op actual = SOME w) /\
    db + LENGTH (enc (Tuple (vyper_to_abi_types (get_tenv cx) (MAP SND xs))) (ListV avs)) <= actual.vs_alloca_next
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `compile_alloc_buffer _ source_st = _`
    (mp_then Any strip_assume_tac log_output_buffer_shape) >>
  `EVERY (supported_scalar_type o SND) xs` by gvs[EVERY_MAP, combinTheory.o_DEF] >>
  drule_all compile_log_store_data_shape >> strip_tac >>
  drule_at (Pat `compile_alloc_buffer _ stored_st = _`) log_output_buffer_shape >> strip_tac >>
  drule abi_encoder_counters >> strip_tac >>
  `srccap < dimword (:256) /\ start.cs_next_var <= limit_st.cs_next_var` by
    gvs[Excl "enc_def", dimword_def] >>
  drule_all log_buffer_allocate_sources >>
  disch_then (qx_choose_then `allocated` (qx_choose_then `b`
    (map_every assume_tac o CONJUNCTS))) >>
  `local_ptrs_reserved ce start` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `source_st` >> simp[]) >>
  suspend "continue"
QED

Resume log_data_prepare_run_mem[continue]:
  `alloca_next_valid allocated` by fs[stmt_state_rel_def, alloca_inv_def] >>
  drule_all log_mem_alloc_frame_bounds >> strip_tac >>
  `EVERY (\arg. eval_operand (FST arg) allocated = eval_operand (FST arg) s) xs` by
    (fs[EVERY_MEM] >> rpt strip_tac >>
     qpat_assum `!p. MEM p xs ==> (_ /\ _)` (drule_then strip_assume_tac) >>
     first_x_assum irule >> Cases_on `FST arg` >>
     gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
  drule_all log_mem_rounded_transport >> strip_tac >>
  qpat_x_assum `LIST_REL (\arg v. log_arg_rel _ _ _ _ _ _ arg v /\ _) xs vs` kall_tac >>
  qpat_x_assum `EVERY (\p. (_ /\ _)) xs` kall_tac >>
  drule_all log_store_encode_continue_mem >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (qx_choose_then `avs` (qx_choose_then `actual`
      (qx_choose_then `db` (map_every assume_tac o CONJUNCTS)))))) >>
  suspend "finish"
QED

Resume log_data_prepare_run_mem[finish]:
  `emitted_insts source_st end_st = emitted_insts source_st start ++ emitted_insts start end_st` by
    (irule emitted_insts_append >> gvs[inst_extends_def]) >>
  `run_inst_seq (emitted_insts source_st end_st) s = OK actual` by
    (drule_all run_inst_seq_compose_ok >> simp[]) >>
  `inst_extends source_st end_st` by
    (irule inst_extends_trans >> qexists_tac `start` >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts source_st start) s` by
    (irule log_mem_alloc_check >> goal_assum (drule_at Any)) >>
  conj_tac
  >- (asm_rewrite_tac[] >> irule run_inst_seq_mem_ok_append >>
      simp[] >> rpt strip_tac >> gvs[]) >>
  conj_tac >- (rpt strip_tac >> gvs[] >> metis_tac[LESS_EQ_TRANS]) >>
  qexistsl_tac [`avs`,`actual`,`db`] >> asm_simp_tac bool_ss [] >>
  rpt strip_tac >>
  `abi_decoder_operand_live start.cs_next_var op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `source_st.cs_next_var` >> simp[]) >>
  `eval_operand op allocated = SOME w` by metis_tac[] >>
  first_x_assum drule_all >> simp[]
QED

Finalise log_data_prepare_run_mem
