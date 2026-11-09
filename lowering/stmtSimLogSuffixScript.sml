(* Successful Log suffixes use the checked store/encoder and LOG boundaries. *)
Theory stmtSimLogSuffix
Ancestors
  stmtSimLogStoreCompose stmtSimLogEmit stmtSimLogTrace stmtSimLogTopics
  compileEnv loweringStateRelDefs exprLoweringProps emitHelperProps venomExecSemantics venomState
  valueEncoding valueEncodingDefs words list arithmetic stmtSimLogTopicFresh stmtSimLogSourceAllocate
  exprSimWordArgs stmtSimLogArgs fragExec stmtLowering stmtSimLogStoreEncode
  stmtSimLogDataRun abiEncoderCounters abiDecoderReentry abiEncoderAppend
  loweringHalt vyperABI contractABI

Theorem log_emit_continuation:
  emit_inst LOG
    (Lit (n2w (LENGTH topic_ops)) :: REVERSE topic_ops ++ [len_op;ptr_op]) [] sa =
      ((),sb) /\
  LENGTH topic_ops < dimword (:256) /\
  eval_operand ptr_op s = SOME off /\ eval_operand len_op s = SOME sz /\
  eval_operands topic_ops s = SOME topics /\
  mem_bytes_at (w2n off) (w2n sz) s.vs_memory = data /\
  stmt_state_rel ctx func ce cx es s /\ fresh_vars_wrt limit_st s ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    stmt_state_rel ctx func ce cx
      (es with logs := es.logs ++
        [<|logger := w2w cx.txn.target; topics := topics; data := data |>]) t /\
    fresh_vars_wrt limit_st t /\ inst_extends sa sb /\
    (!op. eval_operand op t = eval_operand op s) /\
    (t with vs_logs := s.vs_logs) = s
Proof
  strip_tac >> drule_all compile_log_emit_run >> strip_tac >>
  drule emit_inst_extends >> strip_tac >>
  `t.vs_vars = s.vs_vars` by
    (qpat_x_assum `(t with vs_logs := _) = s`
      (mp_tac o Q.AP_TERM `\u. u.vs_vars`) >> simp[]) >>
  `fresh_vars_wrt limit_st t` by gvs[fresh_vars_wrt_def] >>
  `inst_extends sa sb` by (drule inst_extends_emit_inst >> simp[]) >>
  `t.vs_labels = s.vs_labels` by
    (qpat_x_assum `(t with vs_logs := _) = s`
      (mp_tac o Q.AP_TERM `\u. u.vs_labels`) >> simp[]) >>
  qexists_tac `t` >> gvs[] >>
  Cases >> simp[eval_operand_def, lookup_var_def]
QED

Theorem log_emit_empty_suffix:
  emit_inst LOG
    (Lit (n2w (LENGTH topic_ops)) :: REVERSE topic_ops ++ [Lit 0w;Lit 0w]) [] sa =
      ((),sb) /\ LENGTH topic_ops < dimword (:256) /\
  eval_operands topic_ops s = SOME topics /\
  stmt_state_rel ctx func ce cx es s /\ fresh_vars_wrt limit_st s ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    stmt_state_rel ctx func ce cx
      (es with logs := es.logs ++
        [<|logger := w2w cx.txn.target; topics := topics; data := [] |>]) t /\
    fresh_vars_wrt limit_st t /\ inst_extends sa sb /\
    (!op. eval_operand op t = eval_operand op s) /\
    (t with vs_logs := s.vs_logs) = s
Proof
  strip_tac >> irule log_emit_continuation >> simp[] >>
  qexistsl_tac [`Lit 0w`,`0w`,`Lit 0w`,`0w`,`topic_ops`] >>
  gvs[eval_operand_def, mem_bytes_at_def]
QED

Theorem log_emit_encoded_suffix:
  emit_inst LOG
    (Lit (n2w (LENGTH topic_ops)) :: REVERSE topic_ops ++ [len_op;ptr_op]) [] sa =
      ((),sb) /\ LENGTH topic_ops < dimword (:256) /\
  eval_operand ptr_op s = SOME (n2w b) /\
  eval_operand len_op s = SOME (n2w (LENGTH data)) /\
  b < dimword (:256) /\ LENGTH data < dimword (:256) /\
  mem_bytes_at b (LENGTH data) s.vs_memory = data /\
  eval_operands topic_ops s = SOME topics /\
  stmt_state_rel ctx func ce cx es s /\ fresh_vars_wrt limit_st s ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    stmt_state_rel ctx func ce cx
      (es with logs := es.logs ++
        [<|logger := w2w cx.txn.target; topics := topics; data := data |>]) t /\
    fresh_vars_wrt limit_st t /\ inst_extends sa sb /\
    (!op. eval_operand op t = eval_operand op s) /\
    (t with vs_logs := s.vs_logs) = s
Proof
  strip_tac >> irule log_emit_continuation >> simp[] >>
  qexistsl_tac [`len_op`,`n2w b`,`ptr_op`,`n2w (LENGTH data)`,`topic_ops`] >>
  gvs[w2n_n2w]
QED

Theorem log_operands_values:
  !ops ws. LIST_REL (\op w. eval_operand op s = SOME w) ops ws ==>
    eval_operands ops s = SOME ws
Proof
  Induct >> Cases_on `ws` >> simp[eval_operands_def] >> rpt strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem log_empty_suffix_finish[local]:
  compile_log_topic_ops raw sm = (ops,st) /\
  run_inst_seq (emitted_insts sm st) s = OK u /\
  wb_frame ce es sm s u /\
  LIST_REL (\op w. eval_operand op u = SOME w) ops topics /\
  stmt_state_rel ctx func ce cx es u /\ fresh_vars_wrt limit_st s /\
  sb.cs_next_var <= limit_st.cs_next_var /\
  emit_inst LOG
    (Lit (n2w (LENGTH (Lit (n2w h)::ops))) ::
      REVERSE (Lit (n2w h)::ops) ++ [Lit 0w;Lit 0w]) [] st = ((),sb) /\
  LENGTH (Lit (n2w h)::ops) < dimword (:256) ==>
  ?t. run_inst_seq (emitted_insts sm sb) s = OK t /\
    stmt_state_rel ctx func ce cx
      (es with logs := es.logs ++
        [<|logger := w2w cx.txn.target; topics := n2w h::topics; data := [] |>]) t /\
    fresh_vars_wrt limit_st t /\ inst_extends sm sb /\
    (!op w. (!z. op = Var z ==> not_fresh_at sm z) /\ (!l. op <> Label l) /\
      eval_operand op s = SOME w ==> eval_operand op t = SOME w)
Proof
  strip_tac >> drule emit_inst_extends >> strip_tac >>
  `st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  `fresh_vars_wrt limit_st u` by (drule_all log_topics_fresh >> simp[]) >>
  `eval_operands (Lit (n2w h)::ops) u = SOME (n2w h::topics)` by
    (drule log_operands_values >> simp[eval_operands_def, eval_operand_def]) >>
  drule_all log_emit_empty_suffix >> strip_tac >>
  drule log_topics_inst_extends >> strip_tac >>
  `run_inst_seq (emitted_insts sm sb) s = OK t` by
    (drule_all run_inst_seq_compose_ok >> simp[]) >>
  `inst_extends sm sb` by
    (irule inst_extends_trans >> qexists_tac `st` >> simp[]) >>
  qexists_tac `t` >> gvs[] >> rpt strip_tac >>
  drule_all log_frame_operand >> simp[]
QED

Theorem log_split_data_every:
  !xs flags. LENGTH flags = LENGTH xs /\ EVERY P xs ==>
    EVERY P (SND (split_log_ops xs flags))
Proof
  Induct >- (Cases_on `flags` >> simp[split_log_ops_def]) >>
  gen_tac >> PairCases_on `h` >> Cases_on `flags` >> simp[] >>
  rename1 `split_log_ops _ (flag::flags)` >> Cases_on `flag` >>
  simp[split_log_ops_def] >> rpt strip_tac >> pairarg_tac >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

Theorem log_success_empty_run[local]:
  ce.ce_event_info (nsid_to_string id) = SOME (h,tys,flags) /\
  compile_log_eval_all ce args sa = (xs,sm) /\
  compile_log_topic_ops (FST (split_log_ops xs flags)) sm = (ops,st) /\
  SND (split_log_ops xs flags) = [] /\
  compile_stmt ce lctx ty (Log id args) sa = ((),sb) /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sm /\
  fresh_vars_wrt limit_st s /\ sb.cs_next_var <= limit_st.cs_next_var /\
  LENGTH flags = LENGTH xs /\ LENGTH (FILTER I flags) <= 3 /\
  EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sm z) /\ (!l. FST p <> Label l)) xs /\
  LIST_REL (\arg v. log_arg_rel ce cx sa sm es s arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v) xs vs /\
  encode_indexed_event_topics flags (MAP SND xs) vs = SOME topics ==>
  ?t. run_inst_seq (emitted_insts sm sb) s = OK t /\
    stmt_state_rel ctx func ce cx
      (es with logs := es.logs ++
        [<|logger := w2w cx.txn.target; topics := n2w h::topics; data := [] |>]) t /\
    fresh_vars_wrt limit_st t /\ inst_extends sm sb /\
    (!op w. (!z. op = Var z ==> not_fresh_at sm z) /\ (!l. op <> Label l) /\
      eval_operand op s = SOME w ==> eval_operand op t = SOME w)
Proof
  strip_tac >> drule_all compile_log_empty_trace >> strip_tac >>
  `emit_inst LOG
    (Lit (n2w (LENGTH (Lit (n2w h)::ops))) ::
      REVERSE (Lit (n2w h)::ops) ++ [Lit 0w;Lit 0w]) [] st = ((),sb)` by gvs[] >>
  drule_all compile_split_log_topics_run >> strip_tac >>
  `LENGTH (Lit (n2w h)::ops) < dimword (:256)` by
    (drule_all log_emitted_topic_count_exact >> simp[dimword_def]) >>
  irule log_empty_suffix_finish >> simp[] >>
  qexistsl_tac [`ops`,`FST (split_log_ops xs flags)`,`st`,`t`] >> gvs[]
QED

Theorem log_data_prepare_run[local]:
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
  abi_size_bound ce.ce_struct_fields (TupleT (MAP SND xs)) < dimword (:256) ==>
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
      eval_operand op s = SOME w ==> eval_operand op actual = SOME w)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
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
    (MAP_EVERY assume_tac o CONJUNCTS))) >>
  `local_ptrs_reserved ce start` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `source_st` >> simp[]) >>
  qpat_x_assum `LIST_REL (\arg v. log_arg_rel _ _ _ _ _ _ arg v /\ _) xs vs` kall_tac >>
  qpat_x_assum `EVERY (\p. (_ /\ _)) xs` kall_tac >>
  drule_all log_store_encode_continue_bounded >>
  disch_then (qx_choose_then `avs` (qx_choose_then `actual` (qx_choose_then `db`
    (MAP_EVERY assume_tac o CONJUNCTS)))) >>
  `run_inst_seq (emitted_insts source_st end_st) s = OK actual` by
    (drule_all run_inst_seq_compose_ok >> simp[]) >>
  `inst_extends source_st end_st` by
    (irule inst_extends_trans >> qexists_tac `start` >> simp[]) >>
  qexistsl_tac [`avs`,`actual`,`db`] >> asm_simp_tac bool_ss [] >>
  rpt strip_tac >>
  `abi_decoder_operand_live start.cs_next_var op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `source_st.cs_next_var` >> simp[]) >>
  `eval_operand op allocated = SOME w` by metis_tac[] >>
  first_x_assum drule_all >> simp[]
QED

val _ = if null (hyp log_data_prepare_run) then ()
  else raise Fail "open theorem: log_data_prepare_run";

Theorem log_operands_live_transport[local]:
  !ops ws. EVERY (abi_decoder_operand_live nv) ops /\
    eval_operands ops s = SOME ws /\
    (!op w. abi_decoder_operand_live nv op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w) ==>
    eval_operands ops t = SOME ws
Proof
  Induct >> simp[eval_operands_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >> first_x_assum irule >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem log_data_emit_run[local]:
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
  eval_operands topic_ops s = SOME topics /\
  EVERY (abi_decoder_operand_live source_st.cs_next_var) topic_ops /\
  LENGTH topic_ops < dimword (:256) /\
  emit_inst LOG (Lit (n2w (LENGTH topic_ops)) :: REVERSE topic_ops ++
    [out;dst.buf_operand]) [] end_st = ((),final) ==>
  ?avs t.
    vyper_to_abi_list (get_tenv cx) (MAP SND xs) vs = SOME avs /\
    run_inst_seq (emitted_insts source_st final) s = OK t /\
    stmt_state_rel ctx func ce cx
      (es with logs := es.logs ++ [<|logger := w2w cx.txn.target;
        topics := topics; data := enc (Tuple (vyper_to_abi_types (get_tenv cx)
          (MAP SND xs))) (ListV avs) |>]) t /\
    fresh_vars_wrt limit_st t /\ inst_extends source_st final /\
    (!op w. abi_decoder_operand_live source_st.cs_next_var op /\
      eval_operand op s = SOME w ==> eval_operand op t = SOME w)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all log_data_prepare_run >>
  disch_then (qx_choose_then `avs` (qx_choose_then `actual` (qx_choose_then `db`
    (MAP_EVERY assume_tac o CONJUNCTS)))) >>
  `eval_operands topic_ops actual = SOME topics` by
    (drule_all log_operands_live_transport >> simp[]) >>
  drule_all log_emit_encoded_suffix >> strip_tac >>
  `run_inst_seq (emitted_insts source_st final) s = OK t` by
    (drule_all run_inst_seq_compose_ok >> simp[]) >>
  `inst_extends source_st final` by
    (irule inst_extends_trans >> qexists_tac `end_st` >> simp[]) >>
  qexistsl_tac [`avs`,`t`] >> asm_simp_tac bool_ss [] >>
  rpt strip_tac >> first_x_assum drule_all >> simp[]
QED

val _ = if null (hyp log_data_emit_run) then ()
  else raise Fail "open theorem: log_data_emit_run";

Theorem log_selected_typed[local]:
  !xs vs flags.
  LIST_REL (\arg v. log_arg_rel ce cx sa sm es s arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v) xs vs /\
  LENGTH flags = LENGTH xs /\
  LIST_REL (log_arg_rel ce cx sa st es t)
    (SND (split_log_ops xs flags)) (log_non_indexed_values flags vs) ==>
  LIST_REL (\arg v. log_arg_rel ce cx sa st es t arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v)
    (SND (split_log_ops xs flags)) (log_non_indexed_values flags vs)
Proof
  rpt gen_tac >> strip_tac >> drule_all split_log_ops_data_rel >>
  qpat_abbrev_tac `ds = SND (split_log_ops xs flags)` >>
  qpat_abbrev_tac `ws = log_non_indexed_values flags vs` >>
  qpat_x_assum `LIST_REL _ xs vs` kall_tac >>
  qpat_x_assum `Abbrev (ds = _)` kall_tac >>
  qpat_x_assum `Abbrev (ws = _)` kall_tac >>
  qpat_x_assum `LIST_REL _ ds ws` mp_tac >>
  qid_spec_tac `ws` >> qid_spec_tac `ds` >>
  Induct >> Cases_on `ws` >> simp[] >> metis_tac[]
QED

Theorem log_data_stage_code[local]:
  cs_extends sm st /\
  compile_alloc_buffer cap st = (src,s1) /\
  compile_log_store_data ce xs src.buf_operand 0 s1 = ((),s2) /\
  EVERY (supported_scalar_type o SND) xs /\
  compile_alloc_buffer outcap s2 = (dst,s3) /\
  compile_abi_encode_to_buf dst.buf_operand src.buf_operand ei s3 = (len,s4) /\
  emit_inst LOG operands [] s4 = ((),sb) /\
  fn_has_code sm sb func /\ sb.cs_next_var <= limit_st.cs_next_var ==>
  fn_has_code st s1 func /\ fn_has_code s2 s3 func /\
  fn_has_code s3 s4 func /\ s4.cs_next_var <= limit_st.cs_next_var
Proof
  strip_tac >>
  imp_res_tac compile_alloc_buffer_extends >>
  drule_all compile_log_store_data_shape >> strip_tac >>
  `cs_extends s1 s2` by
    (irule cs_extends_same_block >>
     gvs[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND] >> metis_tac[]) >>
  drule cs_extends_abi_encode >> strip_tac >>
  drule emit_inst_extends >> strip_tac >>
  `cs_extends s4 sb` by
    (irule cs_extends_same_block >> simp[rich_listTheory.IS_PREFIX_APPEND] >> metis_tac[]) >>
  `cs_extends sm s1` by (irule cs_extends_trans >> qexists_tac `st` >> simp[]) >>
  `cs_extends sm s2` by (irule cs_extends_trans >> qexists_tac `s1` >> simp[]) >>
  `cs_extends sm s3` by (irule cs_extends_trans >> qexists_tac `s2` >> simp[]) >>
  `cs_extends s3 sb` by (irule cs_extends_trans >> qexists_tac `s4` >> simp[]) >>
  `cs_extends s2 sb` by (irule cs_extends_trans >> qexists_tac `s3` >> simp[]) >>
  `cs_extends s1 sb` by (irule cs_extends_trans >> qexists_tac `s2` >> simp[]) >>
  rpt conj_tac
  >- (irule fn_has_code_mid >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) 
  >- (irule fn_has_code_mid >> goal_assum (drule_at Any) >> simp[] >> metis_tac[])
  >- (irule fn_has_code_mid >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  decide_tac
QED

Theorem log_selected_frontier[local]:
  LENGTH flags = LENGTH xs /\
  EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sm z) /\ (!l. FST p <> Label l)) xs /\
  compile_log_topic_ops (FST (split_log_ops xs flags)) sm = (ops,st) ==>
  cs_extends sm st /\ sm.cs_next_var <= st.cs_next_var /\
  EVERY (\p. (!z. FST p = Var z ==> not_fresh_at st z) /\ (!l. FST p <> Label l))
    (SND (split_log_ops xs flags)) /\
  EVERY (abi_decoder_operand_live st.cs_next_var) (Lit (n2w h)::ops)
Proof
  strip_tac >>
  `EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sm z) /\ (!l. FST p <> Label l))
    (FST (split_log_ops xs flags))` by
    (drule_all log_indexed_selection_every >>
     drule_all split_log_ops_select >> strip_tac >>
     simp[MAP_MAP_o, combinTheory.o_DEF, EVERY_MAP]) >>
  drule_all compile_log_topic_ops_frontier >> strip_tac >>
  drule_all log_split_data_every >> strip_tac >>
  asm_simp_tac bool_ss [] >> conj_tac
  >- (gvs[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >> strip_tac >>
      gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  gvs[EVERY_MEM, abi_decoder_operand_live_def, abi_decoder_older_vars_def,
      not_fresh_at_def] >> rpt strip_tac >> Cases_on `e` >> gvs[] >> metis_tac[]
QED

Theorem log_success_suffix_run:
  ce.ce_event_info (nsid_to_string id) = SOME (h,tys,flags) /\
  compile_log_eval_all ce args sa = (xs,sm) /\
  compile_log_topic_ops (FST (split_log_ops xs flags)) sm = (ops,st) /\
  compile_stmt ce lctx ty (Log id args) sa = ((),sb) /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sm /\
  fresh_vars_wrt limit_st s /\ sb.cs_next_var <= limit_st.cs_next_var /\
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
    (log_non_indexed_values flags vs) = SOME avs ==>
  ?t. run_inst_seq (emitted_insts sm sb) s = OK t /\
    stmt_state_rel ctx func ce cx
      (es with logs := es.logs ++ [<|logger := w2w cx.txn.target;
        topics := n2w h::topics; data := enc (Tuple (vyper_to_abi_types (get_tenv cx)
          (log_non_indexed_types flags (MAP SND xs)))) (ListV avs) |>]) t /\
    fresh_vars_wrt limit_st t /\ inst_extends sm sb /\
    (!op w. (!z. op = Var z ==> not_fresh_at sm z) /\ (!l. op <> Label l) /\
      eval_operand op s = SOME w ==> eval_operand op t = SOME w)
Proof
  strip_tac >> drule_all split_log_ops_data_types >> strip_tac >>
  drule_all log_selected_frontier >> disch_then (qspec_then `h` strip_assume_tac) >>
  Cases_on `SND (split_log_ops xs flags) = []`
  >- suspend "empty" >>
  drule_all (SRULE [] (Q.INST [`data_ops` |-> `SND (split_log_ops xs flags)`]
    compile_log_data_trace)) >> strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >> simp[Excl "enc_def"] >>
  disch_then (qx_choose_then `src` (qx_choose_then `s1` (qx_choose_then `s2`
    (qx_choose_then `dst` (qx_choose_then `s3` (qx_choose_then `len`
      (qx_choose_then `s4` strip_assume_tac))))))) >>
  suspend "data"
QED

Resume log_success_suffix_run[empty]:
  drule_all split_log_ops_data_rel >> strip_tac >>
  `log_non_indexed_values flags vs = []` by gvs[] >>
  `log_non_indexed_types flags (MAP SND xs) = []` by gvs[] >>
  gvs[] >> drule_all log_success_empty_run >> simp[enc_def, listTheory.REV_DEF]
QED

Resume log_success_suffix_run[data]:
  qpat_x_assum `!ty sb lctx. _` kall_tac >>
  `EVERY supported_scalar_type (MAP SND xs)` by
    (gvs[EVERY_MAP, LIST_REL_EL_EQN, EVERY_EL] >> metis_tac[LIST_REL_LENGTH]) >>
  `EVERY supported_scalar_type (MAP SND (SND (split_log_ops xs flags)))` by
    (simp[EVERY_MAP] >> irule log_split_data_every >>
     simp[GSYM EVERY_MAP, combinTheory.o_DEF, Excl "enc_def"]) >>
  `EVERY (supported_scalar_type o SND) (SND (split_log_ops xs flags))` by
    gvs[EVERY_MAP, combinTheory.o_DEF, Excl "enc_def"] >>
  drule_all log_data_stage_code >> strip_tac >>
  `st.cs_next_var <= limit_st.cs_next_var` by
    (drule log_output_buffer_shape >> strip_tac >>
     drule_all compile_log_store_data_shape >> strip_tac >>
     drule abi_encoder_counters >> strip_tac >>
     imp_res_tac log_output_buffer_shape >> decide_tac) >>
  drule_all compile_split_log_topics_run >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  drule_all log_selected_typed >> strip_tac >>
  `local_ptrs_reserved ce st` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sm` >> simp[Excl "enc_def"]) >>
  `fresh_vars_wrt limit_st u` by (drule_all log_topics_fresh >> simp[Excl "enc_def"]) >>
  `eval_operands (Lit (n2w h)::ops) u = SOME (n2w h::topics)` by
    (drule log_operands_values >> simp[eval_operands_def, eval_operand_def, Excl "enc_def"]) >>
  `LENGTH (Lit (n2w h)::ops) < dimword (:256)` by
    (drule_all log_emitted_topic_count_exact >> simp[dimword_def, Excl "enc_def"]) >>
  qpat_x_assum `ce.ce_event_info _ = _` kall_tac >>
  qpat_x_assum `compile_log_eval_all _ _ _ = _` kall_tac >>
  qpat_x_assum `LIST_REL (\arg v. _ /\ _) xs vs` kall_tac >>
  qpat_x_assum `EVERY supported_scalar_type (MAP SND xs)` kall_tac >>
  qpat_x_assum `encode_indexed_event_topics _ _ _ = _` kall_tac >>
  qpat_x_assum `EVERY (\p. _ /\ _) xs` kall_tac >>
  qpat_x_assum `LIST_REL (log_arg_rel _ _ _ _ _ _) _ _` kall_tac >>
  qpat_x_assum `MAP SND _ = _` (SUBST_ALL_TAC o SYM) >>
  gvs[Excl "enc_def"] >>
  drule_all (SRULE [Excl "enc_def"] (GEN_ALL
    (Q.INST [`topic_ops` |-> `Lit (n2w h)::ops`] log_data_emit_run))) >>
  disch_then (qx_choose_then `avs2` (qx_choose_then `t` strip_assume_tac)) >>
  suspend "finish"
QED

Resume log_success_suffix_run[finish]:
  `avs2 = avs` by gvs[Excl "enc_def"] >>
  drule log_topics_inst_extends >> strip_tac >>
  `run_inst_seq (emitted_insts sm sb) s = OK t` by
    (drule_all run_inst_seq_compose_ok >> simp[Excl "enc_def"]) >>
  `inst_extends sm sb` by
    (irule inst_extends_trans >> qexists_tac `st` >> simp[Excl "enc_def"]) >>
  qexists_tac `t` >> gvs[Excl "enc_def"] >> rpt strip_tac >>
  `eval_operand op u = SOME w` by (drule_all log_frame_operand >> simp[]) >>
  `abi_decoder_operand_live st.cs_next_var op` by
    (Cases_on `op` >> gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  first_x_assum drule_all >> simp[]
QED
Finalise log_success_suffix_run

val _ = if null (hyp log_success_suffix_run) then ()
  else raise Fail "open theorem: log_success_suffix_run";
