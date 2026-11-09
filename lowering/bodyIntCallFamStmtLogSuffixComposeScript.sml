(* Compose allocation-site memory frames across the successful Log suffix. *)
Theory bodyIntCallFamStmtLogSuffixCompose
Ancestors
  bodyIntCallFamStmtLogSuffixPipeline bodyIntCallFamStmtLogSuffixMemory
  bodyIntCallFamStmtLogSuffixFootprint stmtSimLogTopics stmtSimLogTrace
  stmtSimLogSuffixCode stmtSimLogDataRun stmtSimLogSuffixActual
  fragExec compileEnv loweringHalt abiEncoderAppend abiEncoderCounters
  exprLoweringProps emitHelperProps freshWrites venomState
  finite_map words list rich_list arithmetic

Theorem intcall_straight_subinterval:
  cs_extends a b /\ cs_extends b c /\ same_blocks a c ==>
  inst_extends a b /\ inst_extends b c
Proof
  strip_tac >>
  `LENGTH b.cs_blocks = LENGTH a.cs_blocks /\
   LENGTH c.cs_blocks = LENGTH b.cs_blocks` by
    (gvs[cs_extends_def, same_blocks_def] >>
     qpat_x_assum `_ = _ ++ _` (mp_tac o AP_TERM ``LENGTH``) >>
     simp[]) >>
  gvs[cs_extends_def, same_blocks_def, inst_extends_def,
      IS_PREFIX_APPEND, emitted_insts_def, DROP_LENGTH_APPEND] >>
  simp[DROP_APPEND1]
QED

Theorem intcall_log_suffix_memory:
  ce.ce_event_info (nsid_to_string id) = SOME (h,tys,flags) /\
  compile_log_eval_all ce args sa = (xs,sm) /\
  compile_log_topic_ops (FST (split_log_ops xs flags)) sm = (ops,st) /\
  compile_stmt ce lctx ty (Log id args) sa = ((),sb) /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sm /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  LENGTH flags = LENGTH xs /\
  EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sm z) /\ (!l. FST p <> Label l)) xs /\
  LIST_REL (\arg v. log_arg_rel ce cx sa sm es s arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v) xs vs /\
  encode_indexed_event_topics flags (MAP SND xs) vs = SOME topics /\
  SUM (MAP (type_memory_bytes ce) (log_non_indexed_types flags (MAP SND xs))) < dimword (:256) /\
  abi_size_bound ce.ce_struct_fields (TupleT (log_non_indexed_types flags (MAP SND xs))) < dimword (:256) /\
  run_inst_seq (emitted_insts sm sb) s = OK t ==>
  !a k. (!aid b z. sm.cs_next_id <= aid /\ aid < sb.cs_next_id /\
    FLOOKUP t.vs_allocas aid = SOME (b,z) ==> a+k <= b \/ b+z <= a) ==>
    mem_bytes_at a k t.vs_memory = mem_bytes_at a k s.vs_memory
Proof
  strip_tac >>
  drule_all compile_split_log_topics_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sm st) s = OK topic_state` >>
  `topic_state.vs_memory = s.vs_memory` by
    (drule_all intcall_log_topics_memory >> simp[]) >>
  drule_all split_log_ops_select >> strip_tac >>
  `EVERY (\p. (!z. FST (FST p) = Var z ==> not_fresh_at sm z) /\
    (!l. FST (FST p) <> Label l)) (ZIP (xs,flags))` by
    (simp[every_zip_fst]) >>
  `EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sm z) /\
    (!l. FST p <> Label l)) (FST (split_log_ops xs flags))` by
    (simp[EVERY_MAP] >> gvs[EVERY_MEM, MEM_FILTER] >> metis_tac[]) >>
  drule_all compile_log_topic_ops_frontier >> strip_tac >>
  `EVERY (supported_scalar_type o SND) xs` by
    (gvs[LIST_REL_EL_EQN, EVERY_EL] >> rpt strip_tac >>
     first_x_assum drule >> simp[]) >>
  drule_all log_success_suffix_code >> strip_tac >>
  suspend "branches"
QED

Resume intcall_log_suffix_memory[branches]:
  Cases_on `SND (split_log_ops xs flags) = []`
  >- (drule_all compile_log_empty_trace >> strip_tac >>
      `cs_extends st sb` by metis_tac[cs_extends_emit_inst] >>
      drule_all intcall_straight_subinterval >> strip_tac >>
      `run_inst_seq (emitted_insts st sb) topic_state = OK t` by
        (drule_all run_inst_seq_emit_extend >> simp[]) >>
      metis_tac[intcall_log_emit_memory_allocas]) >>
  drule_at (Pat `compile_log_topic_ops _ _ = _`) compile_log_data_trace >>
  simp[] >> disch_then (drule_at (Pat `compile_stmt _ _ _ _ _ = _`) o iffLR) >>
  disch_then drule_all >> strip_tac >>
  rename1 `compile_alloc_buffer _ st = (src,s1)` >>
  rename1 `compile_log_store_data _ _ _ _ s1 = ((),s2)` >>
  rename1 `compile_alloc_buffer _ s2 = (dst,s3)` >>
  rename1 `compile_abi_encode_to_buf _ _ _ s3 = (len,s4)` >>
  suspend "data"
QED

Resume intcall_log_suffix_memory[data]:
  drule_all split_log_ops_data_rel >> strip_tac >>
  `LIST_REL (\arg v. log_arg_rel ce cx sa st es topic_state arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v)
    (SND (split_log_ops xs flags)) (log_non_indexed_values flags vs)` by
    (gvs[LIST_REL_EL_EQN] >> metis_tac[]) >>
  `EVERY (\p. (!z. FST p = Var z ==> not_fresh_at st z) /\
    (!l. FST p <> Label l)) (SND (split_log_ops xs flags))` by
    (simp[EVERY_MAP] >> gvs[EVERY_MEM, MEM_FILTER] >>
     metis_tac[not_fresh_at_mono]) >>
  `EVERY (supported_scalar_type o SND) (SND (split_log_ops xs flags))` by
    (gvs[LIST_REL_EL_EQN, EVERY_EL] >> rpt strip_tac >>
     first_x_assum drule >> simp[]) >>
  gvs[] >>
  drule_all compile_log_store_data_shape >> strip_tac >>
  `cs_extends s1 s2` by
    (simp[cs_extends_def, same_blocks_def] >> qexists_tac `[]` >>
     gvs[same_blocks_def] >> simp[]) >>
  `cs_extends st s1 /\ cs_extends s2 s3` by
    metis_tac[compile_alloc_buffer_extends] >>
  drule cs_extends_abi_encode >> strip_tac >>
  `cs_extends s4 sb` by metis_tac[cs_extends_emit_inst] >>
  `cs_extends st s4 /\ cs_extends st sb` by metis_tac[cs_extends_trans] >>
  drule_all intcall_straight_subinterval >> strip_tac >>
  `fn_has_code st s4 func` by
    metis_tac[fn_has_code_split, fn_has_code_mid, cs_extends_trans] >>
  `local_ptrs_reserved ce st` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sm` >> simp[]) >>
  drule_all split_log_ops_data_types >> strip_tac >>
  gvs[] >>
  drule_at (Pat `compile_log_store_data _ _ _ _ _ = _`)
    intcall_log_data_pipeline_footprint >>
  simp[] >> disch_then drule_all >> strip_tac >>
  suspend "observe"
QED

Resume intcall_log_suffix_memory[observe]:
  rename1 `run_inst_seq (emitted_insts st s4) topic_state = OK actual` >>
  `cs_extends sm s4` by metis_tac[cs_extends_trans] >>
  `inst_extends sm s4 /\ inst_extends s4 sb` by
    metis_tac[intcall_straight_subinterval] >>
  `run_inst_seq (emitted_insts st sb) topic_state = OK t` by
    (drule_all run_inst_seq_emit_extend >> simp[]) >>
  `same_blocks st sb` by
    (qpat_assum `cs_extends sm st` mp_tac >>
     qpat_assum `cs_extends st sb` mp_tac >>
     gvs[cs_extends_def, same_blocks_def] >> rpt strip_tac >>
     rename1 `sm.cs_blocks = sm.cs_blocks ++ bs ++ cs` >>
     `bs = [] /\ cs = []` by
       (qpat_x_assum `sm.cs_blocks = _` (mp_tac o AP_TERM ``LENGTH``) >> simp[]) >>
     gvs[]) >>
  `inst_extends st s4` by metis_tac[intcall_straight_subinterval] >>
  `run_inst_seq (emitted_insts s4 sb) actual = OK t` by
    (drule_all run_inst_seq_emit_extend >> simp[]) >>
  drule_all intcall_log_emit_memory_allocas >> strip_tac >>
  `s4.cs_next_id < sb.cs_next_id` by
    (drule emit_inst_extends >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `mem_bytes_at a k actual.vs_memory = mem_bytes_at a k topic_state.vs_memory` suffices_by
    simp[] >>
  irule intcall_footprint_allocation_frame >>
  goal_assum (drule_at Any) >>
  qmatch_assum_abbrev_tac `abi_decode_footprint_frame fp topic_state actual` >>
  qexists_tac `fp` >> simp[] >>
  simp[Abbr `fp`] >> rpt gen_tac >> strip_tac >>
  gvs[]
  >- (qexists_tac `st.cs_next_id` >> simp[] >> decide_tac)
  >- (qexists_tac `s2.cs_next_id` >> simp[] >> decide_tac) >>
  Cases_on `?infos. type_to_abi_enc_info ce.ce_struct_fields ce
    (TupleT (log_non_indexed_types flags (MAP SND xs))) = AbiComplex infos` >>
  gvs[] >>
  qexists_tac `s3.cs_next_id` >> simp[] >> decide_tac
QED

Finalise intcall_log_suffix_memory
