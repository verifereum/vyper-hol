(* Source allocation and store/encode footprint, including reused sites. *)
Theory bodyIntCallFamStmtLogSuffixPipeline
Ancestors
  bodyIntCallFamStmtLogSuffixMemory bodyIntCallFamStmtLogSuffixStore
  stmtSimLogSourceAllocate
  stmtSimLogSuffixActual stmtSimLogDataRun stmtSimLogTrace
  loweringHalt abiEncoderAppend abiEncoderCounters fragExec
  compileEnv exprLoweringProps emitHelperProps abiDecoderFrame
  venomState venomInstProofs3 venomMemProofs venomInst
  finite_map words list arithmetic rich_list

Theorem intcall_log_data_pipeline_footprint:
  compile_alloc_buffer cap source_st = (buf,start) /\
  cap = MAX 32 (SUM (MAP (type_memory_bytes ce) (MAP SND xs))) /\
  compile_log_store_data ce xs buf.buf_operand 0 start = ((),stored_st) /\
  compile_alloc_buffer outcap stored_st = (dst,prepared) /\
  outcap = MAX 32 (abi_size_bound ce.ce_struct_fields (TupleT (MAP SND xs))) /\
  ei = type_to_abi_enc_info ce.ce_struct_fields ce (TupleT (MAP SND xs)) /\
  compile_abi_encode_to_buf dst.buf_operand buf.buf_operand ei prepared = (out,end_st) /\
  fn_has_code source_st end_st func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce source_st /\
  SUM (MAP (type_memory_bytes ce) (MAP SND xs)) < dimword (:256) /\
  abi_size_bound ce.ce_struct_fields (TupleT (MAP SND xs)) < dimword (:256) /\
  LIST_REL (\arg v. log_arg_rel ce cx sa source_st es s arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v) xs vs /\
  EVERY (\p. (!z. FST p = Var z ==> not_fresh_at source_st z) /\
    (!l. FST p <> Label l)) xs ==>
  ?actual b db p.
    run_inst_seq (emitted_insts source_st end_st) s = OK actual /\
    abi_decode_footprint_frame
      ((b,cap)::(db,outcap)::(if (?infos. ei = AbiComplex infos) then [(p,32)] else [])) s actual /\
    FLOOKUP actual.vs_allocas source_st.cs_next_id = SOME (b,cap) /\
    FLOOKUP actual.vs_allocas stored_st.cs_next_id = SOME (db,outcap) /\
    ((?infos. ei = AbiComplex infos) ==>
      FLOOKUP actual.vs_allocas prepared.cs_next_id = SOME (p,32)) /\
    source_st.cs_next_id < stored_st.cs_next_id /\
    stored_st.cs_next_id < prepared.cs_next_id /\
    prepared.cs_next_id <= end_st.cs_next_id
Proof
  strip_tac >>
  `EVERY (supported_scalar_type o SND) xs` by
    (gvs[LIST_REL_EL_EQN, EVERY_EL] >> rpt strip_tac >>
     first_x_assum drule >> simp[]) >>
  drule_all compile_log_store_data_shape >> strip_tac >>
  `cs_extends start stored_st` by
    (simp[cs_extends_def, same_blocks_def] >>
     qexists_tac `[]` >> gvs[same_blocks_def] >> simp[]) >>
  `cs_extends source_st start` by
    (irule compile_alloc_buffer_extends >> goal_assum (drule_at Any)) >>
  `cs_extends stored_st prepared` by metis_tac[compile_alloc_buffer_extends] >>
  drule cs_extends_abi_encode >> strip_tac >>
  `cs_extends start end_st` by metis_tac[cs_extends_trans] >>
  `cs_extends source_st prepared` by metis_tac[cs_extends_trans] >>
  `fn_has_code source_st start func /\ fn_has_code stored_st prepared func /\
   fn_has_code prepared end_st func` by
    metis_tac[fn_has_code_split, fn_has_code_mid, cs_extends_trans] >>
  suspend "allocate"
QED

Resume intcall_log_data_pipeline_footprint[allocate]:
  `cap < dimword (:256)` by gvs[dimword_def] >>
  qspecl_then [`s`,`start`] strip_assume_tac log_fresh_limit_exists >>
  drule_all log_buffer_allocate_sources >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts source_st start) s = OK allocated` >>
  `local_ptrs_reserved ce start` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `source_st` >>
     qpat_assum `compile_alloc_buffer cap source_st = _`
       (mp_tac o MATCH_MP compile_alloc_buffer_parts) >> simp[]) >>
  `EVERY supported_scalar_type (MAP SND xs)` by gvs[EVERY_MAP, combinTheory.o_DEF] >>
  gvs[] >>
  drule_at (Pat `compile_log_store_data _ _ _ _ _ = _`)
    intcall_log_store_encode_footprint >>
  simp[] >> disch_then drule_all >> strip_tac >>
  suspend "compose"
QED

Resume intcall_log_data_pipeline_footprint[compose]:
  `run_inst_seq (emitted_insts source_st end_st) s = OK actual` by
    (drule_all run_inst_seq_compose_ok >> simp[]) >>
  `stored_st.cs_next_id < prepared.cs_next_id` by
    (drule compile_alloc_buffer_parts >> simp[]) >>
  `prepared.cs_next_id <= end_st.cs_next_id` by
    (drule abi_encoder_counters >> simp[]) >>
  `source_st.cs_next_id < stored_st.cs_next_id` by decide_tac >>
  rename1 `abi_decode_footprint_frame ((source_base,_)::(db,_)::
    (if _ then [(cursor_base,32)] else [])) allocated actual` >>
  qexistsl_tac [`actual`,`source_base`,`db`,`cursor_base`] >> simp[] >>
  gvs[abi_decode_footprint_frame_def,
      abiBuiltinAllocationTheory.abi_builtin_allocation_frame_def]
QED

Finalise intcall_log_data_pipeline_footprint

Theorem intcall_log_emit_memory_allocas:
  emit_inst LOG ops [] sa = ((),sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas
Proof
  strip_tac >>
  `emitted_insts sa sb = [mk_inst sa.cs_next_id LOG ops []]` by
    (drule emit_inst_extends >> simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND]) >>
  gvs[run_inst_seq_def, AllCaseEqs()] >>
  conj_tac
  >- (irule venomInstProofs3Theory.step_inst_base_preserves_memory >>
      goal_assum (drule_at Any) >>
      simp[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def,
        venomInstTheory.is_alloca_op_def, venomEffectsTheory.write_effects_def]) >>
  irule venomMemProofsTheory.step_inst_base_preserves_allocas >>
  qexists_tac `mk_inst sa.cs_next_id LOG ops []` >>
  simp[venomInstTheory.mk_inst_def]
QED
