(* Store/encode pipeline with allocation-indexed resource footprints. *)
Theory bodyIntCallFamStmtLogSuffixStore
Ancestors
  bodyIntCallFamStmtLogSuffixAllocated stmtSimLogStoreCompose
  stmtSimLogStoreContinue stmtSimLogAllocate stmtSimLogStoreEncode
  stmtSimLogDataInput stmtSimLogEncodeLayout stmtSimLogTrace stmtSimLogDataRun
  abiDecoderFrame abiDecoderReentry abiEncoderCounters abiEncoderInput
  vyperTypeABI vyperABI compileEnv loweringStateRelDefs supportedTypes contractABI
  exprLoweringProps localPtrsProps emitHelperProps venomExecSemantics
  venomState finite_map words list arithmetic

Theorem intcall_log_store_encode_footprint:
  cap = SUM (MAP (type_memory_bytes ce) (MAP SND xs)) /\
  srccap = MAX 32 cap /\
  outcap = MAX 32 (abi_size_bound ce.ce_struct_fields (TupleT (MAP SND xs))) /\
  ei = type_to_abi_enc_info ce.ce_struct_fields ce (TupleT (MAP SND xs)) /\
  compile_alloc_buffer srccap source_st = (srcbuf,source_end) /\
  fn_has_code source_st source_end func /\
  FLOOKUP initial.vs_allocas source_st.cs_next_id = SOME (b,srccap) /\
  source_st.cs_next_id < start.cs_next_id /\ b+srccap < dimword (:256) /\
  eval_operand src initial = SOME (n2w b) /\
  LIST_REL (log_data_source cx b srccap initial) xs vs /\
  EVERY (\(op,ty). !x. op = Var x ==> not_fresh_at start x) xs /\
  abi_decoder_operand_live start.cs_next_var src /\
  compile_log_store_data ce xs src 0 start = ((),stored_st) /\
  compile_alloc_buffer outcap stored_st = (dst,prepared) /\
  fn_has_code stored_st prepared func /\
  compile_abi_encode_to_buf dst.buf_operand src ei prepared = (out,end_st) /\
  fn_has_code prepared end_st func /\
  stmt_state_rel ctx func ce cx es initial /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce source_st /\ local_ptrs_reserved ce start /\
  EVERY supported_scalar_type (MAP SND xs) /\ cap < dimword (:256) /\
  abi_size_bound ce.ce_struct_fields (TupleT (MAP SND xs)) < dimword (:256) ==>
  ?avs actual db p.
    vyper_to_abi_list (get_tenv cx) (MAP SND xs) vs = SOME avs /\
    run_inst_seq (emitted_insts start end_st) initial = OK actual /\
    inst_extends start end_st /\
    eval_operand dst.buf_operand actual = SOME (n2w db) /\
    mem_bytes_at db (LENGTH (enc (Tuple (vyper_to_abi_types (get_tenv cx) (MAP SND xs))) (ListV avs))) actual.vs_memory =
      enc (Tuple (vyper_to_abi_types (get_tenv cx) (MAP SND xs))) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Tuple (vyper_to_abi_types (get_tenv cx) (MAP SND xs))) (ListV avs)))) /\
    stmt_state_rel ctx func ce cx es actual /\
    (!op w. abi_decoder_operand_live start.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w) /\
    db < dimword (:256) /\
    LENGTH (enc (Tuple (vyper_to_abi_types (get_tenv cx) (MAP SND xs))) (ListV avs)) < dimword (:256) /\
    abi_decode_footprint_frame
      ((b,srccap)::(db,outcap)::(if (?infos. ei = AbiComplex infos) then [(p,32)] else [])) initial actual /\
    FLOOKUP actual.vs_allocas source_st.cs_next_id = SOME (b,srccap) /\
    FLOOKUP actual.vs_allocas stored_st.cs_next_id = SOME (db,outcap) /\
    ((?infos. ei = AbiComplex infos) ==>
      FLOOKUP actual.vs_allocas prepared.cs_next_id = SOME (p,32)) /\
    (!aid r. FLOOKUP initial.vs_allocas aid = SOME r ==>
      FLOOKUP actual.vs_allocas aid = SOME r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!x. src = Var x ==> not_fresh_at start x` by
    (rpt strip_tac >> gvs[abi_decoder_operand_live_def,
      abi_decoder_older_vars_def, not_fresh_at_def] >> metis_tac[]) >>
  `cap <= srccap` by simp[] >>
  `!name lo sz. local_region ce es.scopes initial name lo sz ==>
    lo+sz <= b+0 \/ b+0+SUM (MAP (type_memory_bytes ce) (MAP SND xs)) <= lo` by
    (rpt strip_tac >> drule_all log_buffer_clear_of_locals >> strip_tac >> decide_tac) >>
  `ce.ce_is_ctor ==> !name tv v p.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc p) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    p+type_memory_size tv <= b+0 \/
    b+0+SUM (MAP (type_memory_bytes ce) (MAP SND xs)) <= p` by
    (rpt strip_tac >> drule_all log_buffer_clear_of_immutable >> strip_tac >> decide_tac) >>
  `0+SUM (MAP (type_memory_bytes ce) (MAP SND xs)) <= srccap` by simp[] >>
  qabbrev_tac `store_sf = ce.ce_struct_fields` >>
  Q.ISPEC_THEN `store_sf` drule_all (Q.GEN `sf` (SPEC_ALL log_store_data_stmt)) >>
  disch_then (qspec_then `store_sf` strip_assume_tac) >>
  qunabbrev_tac `store_sf` >>
  rename1 `run_inst_seq (emitted_insts start stored_st) initial = OK stored` >>
  qpat_x_assum `!name lo sz. _` kall_tac >>
  qpat_x_assum `ce.ce_is_ctor ==> _` kall_tac >>
  suspend "encode"
QED

Resume intcall_log_store_encode_footprint[encode]:
  drule log_write_frame_fields >> strip_tac >>
  `FLOOKUP stored.vs_allocas source_st.cs_next_id = SOME (b,srccap)` by simp[] >>
  `EVERY (supported_scalar_type o SND) xs` by gvs[EVERY_MAP, combinTheory.o_DEF] >>
  `local_ptrs_reserved ce stored_st` by (drule_all local_ptrs_reserved_next_var >> simp[]) >>
  `abi_decoder_operand_live stored_st.cs_next_var src` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `start.cs_next_var` >> simp[]) >>
  drule log_data_sources_typed >> strip_tac >>
  `SUM (MAP (type_memory_bytes ce) (MAP SND xs)) < dimword (:256)` by simp[] >>
  drule_all log_stored_tuple_encoding_bound >> strip_tac >>
  `abi_encoder_input ei (Tuple (vyper_to_abi_types (get_tenv cx) (MAP SND xs)))
    (ListV avs) b cap stored.vs_memory` by
    (qpat_x_assum `abi_encoder_input _ _ _ _ _ _` mp_tac >>
     asm_simp_tac bool_ss [ADD_0, vyper_to_abi_type_def]) >>
  `LENGTH (enc (Tuple (vyper_to_abi_types (get_tenv cx) (MAP SND xs))) (ListV avs)) <= outcap /\
   outcap < dimword (:256)` by gvs[Excl "enc_def", dimword_def] >>
  drule_all compile_log_store_data_shape >> strip_tac >>
  `source_st.cs_next_id < stored_st.cs_next_id` by decide_tac >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ initial` kall_tac >>
  Q.SUBGOAL_THEN `((?n. ei = AbiCopy n /\ n < dimword (:256)) \/
    (?infos. ei = AbiComplex infos /\ EXISTS (\(_,_,_,dyn). dyn) infos /\
      EVERY (\(child,asz,mz,dyn). log_scalar_enc_info child) infos))` assume_tac
  >- (asm_simp_tac bool_ss [] >> irule log_tuple_encoder_shape >> simp[]) >>
  drule_all intcall_log_allocated_tuple_footprint >>
  disch_then (qx_choose_then `actual` (qx_choose_then `db` (qx_choose_then `p` strip_assume_tac))) >>
  suspend "finish"
QED

Resume intcall_log_store_encode_footprint[finish]:
  `run_inst_seq (emitted_insts start end_st) initial = OK actual` by
    (drule_all run_inst_seq_compose_ok >> simp[]) >>
  `inst_extends start end_st` by
    (irule inst_extends_trans >> qexists_tac `stored_st` >> simp[]) >>
  `LENGTH (enc (Tuple (vyper_to_abi_types (get_tenv cx) (MAP SND xs))) (ListV avs)) < dimword (:256)` by decide_tac >>
  qexistsl_tac [`avs`,`actual`,`db`,`p`] >> asm_simp_tac bool_ss [] >>
  conj_tac
  >- (rpt strip_tac >>
      `!x. op = Var x ==> not_fresh_at start x` by
        (rpt strip_tac >> gvs[abi_decoder_operand_live_def,
          abi_decoder_older_vars_def, not_fresh_at_def] >> metis_tac[]) >>
      `eval_operand op stored = SOME w` by metis_tac[] >>
      `abi_decoder_operand_live stored_st.cs_next_var op` by
        (irule abi_decoder_operand_live_mono >> qexists_tac `start.cs_next_var` >> simp[]) >>
      first_x_assum drule_all >> simp[]) >>
  irule abi_decode_footprint_frame_trans >> qexists_tac `stored` >> conj_tac
  >- (irule abi_decode_footprint_frame_weaken >>
      qexists_tac `[(b+0,SUM (MAP (type_memory_bytes ce) (MAP SND xs)))]` >>
      simp[] >> rpt strip_tac >> qexistsl_tac [`b`,`srccap`] >> simp[]) >>
  irule abi_decode_footprint_frame_weaken >>
  qexists_tac `(db,outcap)::(if (?infos. ei = AbiComplex infos) then [(p,32)] else [])` >>
  simp[] >> rpt strip_tac >> qexistsl_tac [`d`,`sz`] >> simp[]
QED

Finalise intcall_log_store_encode_footprint
