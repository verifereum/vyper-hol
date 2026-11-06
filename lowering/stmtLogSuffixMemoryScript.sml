(* The memory checks of the log statement's suffix: after the arguments,
   the topic hashes, the data buffer and its stores, the encode buffer and
   the tuple encoder, and LOG, as log_success_suffix_actual_run runs them.
   Every access lies in an argument's footprint (expr_val_at: an allocation
   or a local's region) or in one of the suffix's own two ALLOCA buffers,
   all below the allocation frontier; ALLOCA only raises the frontier.
   A bytestring argument is copied whole, its length word and its bytes
   rounded up to a multiple of 32 (compile_store_bytestring), which can
   read past val_footprint; the last premise puts that rounded range
   below the frontier. *)
Theory stmtLogSuffixMemory
Ancestors
  stmtSimLogSuffixActual stmtSimLogArgs stmtSimLogSource fragExecMem
  exprLoweringProps stmtLowering compileEnv loweringPosts
  vyperEvent vyperInterpreter vyperState venomState
  stmtLogPrepareMemory stmtLogTopicsMemory stmtLogEmitMemory
  stmtLogSuffixStageMemory stmtSimLogSuffix stmtSimLogTrace stmtSimLogTopicFresh stmtSimLogTopics
  stmtSimLogStoreEncode stmtSimLogDataRun abiEncoderCounters abiDecoderReentry
  emitHelperProps localPtrsProps fragExec words list arithmetic

Theorem log_data_prepare_run_mem_direct[local]:
  compile_alloc_buffer (MAX 32 (SUM (MAP (type_memory_bytes ce) (MAP SND xs)))) source_st = (srcbuf,start) /\
  fn_has_code source_st start func /\
  compile_log_store_data ce xs srcbuf.buf_operand 0 start = ((),stored_st) /\
  compile_alloc_buffer (MAX 32 (abi_size_bound ce.ce_struct_fields (TupleT (MAP SND xs)))) stored_st = (dst,prepared) /\
  fn_has_code stored_st prepared func /\
  compile_abi_encode_to_buf dst.buf_operand srcbuf.buf_operand
    (type_to_abi_enc_info ce.ce_struct_fields ce (TupleT (MAP SND xs))) prepared = (out,end_st) /\
  fn_has_code prepared end_st func /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce source_st /\
  fresh_vars_wrt limit_st s /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  LIST_REL (\arg v. log_arg_rel ce cx sa source_st es s arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v) xs vs /\
  EVERY (\p. (!z. FST p = Var z ==> not_fresh_at source_st z) /\ (!l. FST p <> Label l)) xs /\
  EVERY supported_scalar_type (MAP SND xs) /\
  SUM (MAP (type_memory_bytes ce) (MAP SND xs)) < dimword (:256) /\
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
  irule (SIMP_RULE bool_ss [] (Q.INST
    [`cap` |-> `SUM (MAP (type_memory_bytes ce) (MAP SND xs))`,
     `srccap` |-> `MAX 32 (SUM (MAP (type_memory_bytes ce) (MAP SND xs)))`,
     `outcap` |-> `MAX 32 (abi_size_bound ce.ce_struct_fields (TupleT (MAP SND xs)))`,
     `ei` |-> `type_to_abi_enc_info ce.ce_struct_fields ce (TupleT (MAP SND xs))`]
    log_data_prepare_run_mem)) >> simp[] >> goal_assum (drule_at Any)
QED

Theorem log_success_suffix_mem_ok:
  ce.ce_event_info (nsid_to_string id) = SOME (h,tys,flags) /\
  compile_log_eval_all ce args sa = (xs,sm) /\
  compile_log_topic_ops (FST (split_log_ops xs flags)) sm = (ops,st) /\
  compile_stmt ce lctx ty (Log id args) sa = ((),sb) /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sm /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  LENGTH flags = LENGTH xs /\ LENGTH (FILTER I flags) <= 3 /\
  EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sm z) /\ (!l. FST p <> Label l)) xs /\
  LIST_REL (\arg v. log_arg_rel ce cx sa sm es s arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v) xs vs /\
  encode_indexed_event_topics flags (MAP SND xs) vs = SOME topics /\
  SUM (MAP (type_memory_bytes ce) (log_non_indexed_types flags (MAP SND xs))) < dimword (:256) /\
  abi_size_bound ce.ce_struct_fields (TupleT (log_non_indexed_types flags (MAP SND xs))) < dimword (:256) /\
  vyper_to_abi_list (get_tenv cx) (log_non_indexed_types flags (MAP SND xs))
    (log_non_indexed_values flags vs) = SOME avs /\
  LIST_REL (\arg v. !w n.
    ~is_word_type (SND arg) /\ eval_operand (FST arg) s = SOME w /\
    ((?bs. v = BytesV bs /\ n = LENGTH bs) \/
     (?str. v = StringV str /\ n = LENGTH str)) ==>
    w2n w + 32 + 32 * ((n + 31) DIV 32) <= s.vs_alloca_next) xs vs ==>
  run_inst_seq_mem_ok (emitted_insts sm sb) s /\
  !t. run_inst_seq (emitted_insts sm sb) s = OK t ==>
      s.vs_alloca_next <= t.vs_alloca_next
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qspecl_then [`s`,`sb`] (qx_choose_then `limit_st` strip_assume_tac) log_fresh_limit_exists >>
  `LIST_REL (\arg v. !w n. ~is_word_type (SND arg) /\
    eval_operand (FST arg) s = SOME w /\
    ((?bs. v = BytesV bs /\ n = LENGTH bs) \/
     (?str. v = StringV str /\ n = LENGTH str)) ==>
    w2n w + (32 * ((n+31) DIV 32) + 32) <= s.vs_alloca_next) xs vs` by
    (qpat_assum `LIST_REL (\arg v. !w n. _) xs vs` mp_tac >>
     match_mp_tac EQ_IMPLIES >> AP_THM_TAC >> AP_THM_TAC >> AP_TERM_TAC >>
     simp[FUN_EQ_THM] >> rpt gen_tac >>
     `!a b c:num. a + (b+c) = a+c+b` by decide_tac >>
     asm_rewrite_tac[]) >>
  drule_all compile_split_log_topics_mem_ok >> strip_tac >>
  drule_all compile_split_log_topics_run >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  `u.vs_alloca_next = s.vs_alloca_next` by metis_tac[] >>
  drule_all log_mem_selected_frontier >> disch_then (qspec_then `h` strip_assume_tac) >>
  `LENGTH (Lit (n2w h)::ops) < dimword (:256)` by
    (drule_all log_emitted_topic_count_exact >> simp[dimword_def]) >>
  Cases_on `SND (split_log_ops xs flags) = []`
  >- suspend "empty" >>
  drule_all split_log_ops_data_types >> strip_tac >>
  drule_all (SRULE [] (Q.INST [`data_ops` |-> `SND (split_log_ops xs flags)`]
    compile_log_data_trace)) >> strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >> simp[Excl "enc_def"] >>
  disch_then (qx_choose_then `src` (qx_choose_then `s1` (qx_choose_then `s2`
    (qx_choose_then `dst` (qx_choose_then `s3` (qx_choose_then `len`
      (qx_choose_then `s4` strip_assume_tac))))))) >>
  suspend "data"
QED

Resume log_success_suffix_mem_ok[empty]:
  drule_all compile_log_empty_trace >> strip_tac >>
  `emit_inst LOG (Lit (n2w (LENGTH (Lit (n2w h)::ops))) ::
    REVERSE (Lit (n2w h)::ops) ++ [Lit 0w;Lit 0w]) [] st = ((),sb)` by gvs[] >>
  `run_inst_seq_mem_ok (emitted_insts st sb) u` by
    (irule compile_log_emit_mem_ok >> goal_assum (drule_at Any) >>
     simp[eval_operand_def]) >>
  drule log_topics_inst_extends >> strip_tac >>
  drule inst_extends_emit_inst >> strip_tac >>
  `emitted_insts sm sb = emitted_insts sm st ++ emitted_insts st sb` by
    (irule emitted_insts_append >> gvs[inst_extends_def]) >>
  conj_tac
  >- (asm_rewrite_tac[] >> irule run_inst_seq_mem_ok_append >> simp[] >> rpt strip_tac >> gvs[]) >>
  rpt strip_tac >>
  `run_inst_seq (emitted_insts st sb) u = OK t` by
    metis_tac[run_inst_seq_append] >>
  `eval_operands (Lit (n2w h)::ops) u = SOME (n2w h::topics)` by
    (drule stmtSimLogSuffixTheory.log_operands_values >> simp[eval_operands_def, eval_operand_def]) >>
  `eval_operand (Lit 0w) u = SOME 0w` by simp[eval_operand_def] >>
  drule_all compile_log_emit_frontier >> simp[]
QED

Resume log_success_suffix_mem_ok[data]:
  qpat_x_assum `!ty sb lctx. _` kall_tac >>
  `EVERY supported_scalar_type (MAP SND xs)` by
    (gvs[EVERY_MAP, LIST_REL_EL_EQN, EVERY_EL] >> metis_tac[LIST_REL_LENGTH]) >>
  `EVERY supported_scalar_type (MAP SND (SND (split_log_ops xs flags)))` by
    (simp[EVERY_MAP] >> irule log_split_data_every >>
     simp[GSYM EVERY_MAP, combinTheory.o_DEF, Excl "enc_def"]) >>
  `EVERY (supported_scalar_type o SND) (SND (split_log_ops xs flags))` by
    gvs[EVERY_MAP, combinTheory.o_DEF, Excl "enc_def"] >>
  drule_all log_mem_data_stage_code >> strip_tac >>
  `st.cs_next_var <= limit_st.cs_next_var` by
    (drule log_output_buffer_shape >> strip_tac >>
     drule_all compile_log_store_data_shape >> strip_tac >>
     drule abi_encoder_counters >> strip_tac >>
     imp_res_tac log_output_buffer_shape >> decide_tac) >>
  drule_all log_mem_selected_typed >> strip_tac >>
  `local_ptrs_reserved ce st` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sm` >> simp[Excl "enc_def"]) >>
  `fresh_vars_wrt limit_st u` by (drule_all log_topics_fresh >> simp[Excl "enc_def"]) >>
  `EVERY (\arg. eval_operand (FST arg) u = eval_operand (FST arg) s)
    (SND (split_log_ops xs flags))` by
    (drule_all log_split_data_every >> strip_tac >>
     fs[EVERY_MEM] >> rpt strip_tac >>
     qpat_assum `!e. MEM e (SND (split_log_ops xs flags)) ==> _ /\ _`
       (drule_then strip_assume_tac) >>
     `?v. log_arg_rel ce cx sa sm es s arg v` by
       (qpat_assum `LIST_REL (\arg v. log_arg_rel _ _ _ sm _ s arg v /\ _) xs vs`
          (mp_then Any mp_tac split_log_ops_data_rel) >>
        disch_then drule >> strip_tac >>
        qpat_x_assum `LIST_REL (\arg v. log_arg_rel _ _ _ sm _ s arg v /\ _) _ _` mp_tac >>
        simp[LIST_REL_EL_EQN] >> strip_tac >>
        fs[MEM_EL] >> metis_tac[]) >>
     `?w. eval_operand (FST arg) s = SOME w` by
       (Cases_on `arg` >> fs[log_arg_rel_def, expr_val_rel_def]) >>
     simp[] >> irule log_frame_operand >>
     qpat_assum `wb_frame ce es sm s u` (irule_at Any) >> simp[]) >>
  `s.vs_alloca_next <= u.vs_alloca_next` by simp[] >>
  drule_all log_mem_selected_rounded >> strip_tac >>
  suspend "prepare"
QED

Resume log_success_suffix_mem_ok[prepare]:
  qpat_x_assum `ce.ce_event_info _ = _` kall_tac >>
  qpat_x_assum `compile_log_eval_all _ _ _ = _` kall_tac >>
  qpat_x_assum `LIST_REL (\arg v. _ /\ _) xs vs` kall_tac >>
  qpat_x_assum `EVERY supported_scalar_type (MAP SND xs)` kall_tac >>
  qpat_x_assum `encode_indexed_event_topics _ _ _ = _` kall_tac >>
  qpat_x_assum `EVERY (\p. _ /\ _) xs` kall_tac >>
  qpat_x_assum `LIST_REL (log_arg_rel _ _ _ _ _ _) _ _` kall_tac >>
  qpat_x_assum `MAP SND _ = _` (SUBST_ALL_TAC o SYM) >>
  gvs[Excl "enc_def"] >>
  `LIST_REL (\arg v. !w n. ~is_word_type (SND arg) /\
    eval_operand (FST arg) u = SOME w /\
    ((?bs. v = BytesV bs /\ n = LENGTH bs) \/
     (?str. v = StringV str /\ n = LENGTH str)) ==>
    w2n w + 32 + 32 * ((n+31) DIV 32) <= u.vs_alloca_next)
    (SND (split_log_ops xs flags)) (log_non_indexed_values flags vs)` by
    (qpat_assum `LIST_REL (\arg v. !w n. _) (SND _) _` mp_tac >>
     qpat_assum `u.vs_alloca_next = _` (fn th => pure_rewrite_tac[th]) >>
     match_mp_tac EQ_IMPLIES >> AP_THM_TAC >> AP_THM_TAC >> AP_TERM_TAC >>
     simp[FUN_EQ_THM] >> rpt gen_tac >>
     `!a b c:num. a + (b+c) = a+c+b` by decide_tac >>
     asm_rewrite_tac[]) >>
  drule_all log_data_prepare_run_mem_direct >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (qx_choose_then `avs2` (qx_choose_then `actual`
      (qx_choose_then `db` (map_every assume_tac o CONJUNCTS)))))) >>
  suspend "emit"
QED

Resume log_success_suffix_mem_ok[emit]:
  `emit_inst LOG (Lit (n2w (LENGTH (Lit (n2w h)::ops))) ::
    REVERSE (Lit (n2w h)::ops) ++ [len;dst.buf_operand]) [] s4 = ((),sb)` by gvs[] >>
  `run_inst_seq_mem_ok (emitted_insts s4 sb) actual` by
    (irule compile_log_emit_mem_ok >> goal_assum (drule_at Any) >>
     simp[Excl "enc_def"]) >>
  `LIST_REL (\op w. eval_operand op actual = SOME w) ops topics` by
    (fs[LIST_REL_EL_EQN, EVERY_EL] >> rpt strip_tac >> metis_tac[]) >>
  `eval_operands (Lit (n2w h)::ops) actual = SOME (n2w h::topics)` by
    (drule stmtSimLogSuffixTheory.log_operands_values >> simp[eval_operands_def, eval_operand_def]) >>
  drule log_topics_inst_extends >> strip_tac >>
  drule inst_extends_emit_inst >> strip_tac >>
  `emitted_insts st sb = emitted_insts st s4 ++ emitted_insts s4 sb` by
    (irule emitted_insts_append >> gvs[inst_extends_def]) >>
  `emitted_insts sm sb = emitted_insts sm st ++ emitted_insts st sb` by
    (irule emitted_insts_append >> gvs[inst_extends_def] >>
     metis_tac[inst_extends_trans, inst_extends_def]) >>
  suspend "finish"
QED

Resume log_success_suffix_mem_ok[finish]:
  `run_inst_seq_mem_ok (emitted_insts st sb) u` by
    (asm_rewrite_tac[] >> irule run_inst_seq_mem_ok_append >>
     simp[Excl "enc_def"] >> rpt strip_tac >> gvs[Excl "enc_def"]) >>
  conj_tac
  >- (qpat_assum `emitted_insts sm sb = _` (fn th => rewrite_tac[th]) >>
      irule run_inst_seq_mem_ok_append >> simp[Excl "enc_def"] >>
      rpt strip_tac >> gvs[Excl "enc_def"]) >>
  rpt strip_tac >>
  `run_inst_seq (emitted_insts st sb) u = OK t` by
    metis_tac[run_inst_seq_append] >>
  `run_inst_seq (emitted_insts s4 sb) actual = OK t` by
    metis_tac[run_inst_seq_append] >>
  `t.vs_alloca_next = actual.vs_alloca_next` by
    (irule compile_log_emit_frontier >> conj_tac
     >- (qpat_assum `run_inst_seq (emitted_insts s4 sb) actual = OK t` (irule_at Any) >>
         qpat_assum `eval_operands (Lit _::ops) actual = _` (irule_at Any) >>
         qpat_assum `eval_operand len actual = _` (irule_at Any) >>
         qpat_assum `eval_operand dst.buf_operand actual = _` (irule_at Any) >>
         simp[Excl "enc_def"]) >>
     goal_assum (drule_at Any)) >>
  metis_tac[LESS_EQ_TRANS]
QED

Finalise log_success_suffix_mem_ok
