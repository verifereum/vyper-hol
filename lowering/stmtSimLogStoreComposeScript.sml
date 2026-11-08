Theory stmtSimLogStoreCompose
Ancestors
  stmtSimLogStoreEncode stmtSimLogStoreContinue stmtSimLogStoreFresh
  stmtSimLogEncodeLayout stmtSimLogDataInput vyperTypeABI vyperABI compileEnv supportedTypes contractABI list stmtSimLogAllocate abiDecoderReentry exprLoweringProps vyperTyping abiEncoderCounters stmtSimLogTrace emitHelperProps stmtSimLogDataRun arithmetic words

val _ = if null (hyp stmtSimLogStoreContinueTheory.log_store_data_stmt)
  then print "STORE PREREQUISITE CLOSED\n"
  else (print_thm stmtSimLogStoreContinueTheory.log_store_data_stmt;
        raise Fail "open store prerequisite");

Theorem log_scalar_embedded_bound[local]:
  supported_scalar_type ty ==>
  vyper_abi_embedded_size env ty =
    abi_embedded_static_size sf ty +
      (if is_abi_dynamic sf ty then abi_size_bound sf ty else 0)
Proof
  Cases_on `ty` >> simp[supported_scalar_type_def, supported_word_type_def,
    supported_string_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[supported_word_type_def, supported_string_type_def,
    vyper_abi_size_bound_def, vyper_is_dynamic_def,
    abi_embedded_static_size_def, is_abi_dynamic_def, abi_size_bound_def,
    abi_static_size_def, ceil32_def] >>
  rename1 `BytesT bound` >> Cases_on `bound` >>
  simp[supported_word_type_def, supported_string_type_def,
    vyper_abi_size_bound_def, vyper_is_dynamic_def,
    abi_embedded_static_size_def, is_abi_dynamic_def, abi_size_bound_def,
    abi_static_size_def, ceil32_def]
QED

Theorem log_tuple_source_bound[local]:
  !tys. EVERY supported_scalar_type tys ==>
  vyper_abi_size_bound_list env tys = abi_size_bound ce.ce_struct_fields (TupleT tys)
Proof
  Induct >> simp[abi_size_bound_def, Once vyper_abi_size_bound_def] >>
  rpt strip_tac >> simp[log_scalar_embedded_bound]
QED

Theorem log_stored_tuple_encoding_bound:
  EVERY supported_scalar_type tys /\
  LIST_REL (\ty v. ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
                        value_has_type tv v) tys vs /\
  log_data_layout cx tys vs p mem /\
  SUM (MAP (type_memory_bytes ce) tys) < dimword (:256) /\
  vyper_to_abi_list (get_tenv cx) tys vs = SOME avs ==>
  LENGTH (enc (Tuple (vyper_to_abi_types (get_tenv cx) tys)) (ListV avs)) <=
    abi_size_bound ce.ce_struct_fields (TupleT tys)
Proof
  strip_tac >> drule_all log_data_layout_typed_tuple >> strip_tac >>
  `vyper_to_abi (get_tenv cx) (TupleT tys) (ArrayV (TupleV vs)) = SOME (ListV avs)` by
    simp[Once vyper_to_abi_def] >>
  drule_all (cj 1 vyper_to_abi_enc_length_bound) >>
  drule log_tuple_source_bound >>
  strip_tac >> simp[vyper_abi_size_bound_def, vyper_to_abi_type_def] >>
  metis_tac[]
QED

Theorem log_tuple_encoder_shape:
  EVERY supported_scalar_type tys /\
  SUM (MAP (type_memory_bytes ce) tys) < dimword (:256) ==>
  ((?n. type_to_abi_enc_info sf ce (TupleT tys) = AbiCopy n /\ n < dimword (:256)) \/
   (?infos. type_to_abi_enc_info sf ce (TupleT tys) = AbiComplex infos /\
    EXISTS (\(_,_,_,dyn). dyn) infos /\
    EVERY (\(child,asz,mz,dyn). log_scalar_enc_info child) infos))
Proof
  strip_tac >> simp[log_tuple_enc_info_selected] >>
  Cases_on `is_abi_dynamic ce.ce_struct_fields (TupleT tys)` >> simp[] >>
  conj_tac >- gvs[is_abi_dynamic_def, EXISTS_MAP, combinTheory.o_DEF] >>
  irule log_tuple_enc_members_scalar >> simp[]
QED

Theorem log_store_encode_continue_bounded:
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
  fresh_vars_wrt limit_st initial /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  EVERY supported_scalar_type (MAP SND xs) /\ cap < dimword (:256) /\
  abi_size_bound ce.ce_struct_fields (TupleT (MAP SND xs)) < dimword (:256) ==>
  ?avs actual db.
    vyper_to_abi_list (get_tenv cx) (MAP SND xs) vs = SOME avs /\
    run_inst_seq (emitted_insts start end_st) initial = OK actual /\
    inst_extends start end_st /\ fresh_vars_wrt limit_st actual /\
    eval_operand dst.buf_operand actual = SOME (n2w db) /\
    mem_bytes_at db (LENGTH (enc (Tuple (vyper_to_abi_types (get_tenv cx) (MAP SND xs))) (ListV avs))) actual.vs_memory =
      enc (Tuple (vyper_to_abi_types (get_tenv cx) (MAP SND xs))) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Tuple (vyper_to_abi_types (get_tenv cx) (MAP SND xs))) (ListV avs)))) /\
    stmt_state_rel ctx func ce cx es actual /\
    (!op w. abi_decoder_operand_live start.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w) /\
    db < dimword (:256) /\
    LENGTH (enc (Tuple (vyper_to_abi_types (get_tenv cx) (MAP SND xs))) (ListV avs)) < dimword (:256)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
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
  `0+SUM (MAP (type_memory_bytes ce) (MAP SND xs)) <= srccap /\
   b+srccap < dimword (:256)` by simp[] >>
  qabbrev_tac `store_sf = ce.ce_struct_fields` >>
  Q.ISPEC_THEN `store_sf` drule_all
    (Q.GEN `sf` (SPEC_ALL log_store_data_stmt)) >>
  disch_then (qspec_then `store_sf` strip_assume_tac) >>
  qunabbrev_tac `store_sf` >>
  rename1 `run_inst_seq (emitted_insts start stored_st) initial = OK stored` >>
  qpat_x_assum `!name lo sz. _` kall_tac >>
  qpat_x_assum `ce.ce_is_ctor ==> _` kall_tac >>
  suspend "encode"
QED

Resume log_store_encode_continue_bounded[encode]:
  drule log_write_frame_fields >> strip_tac >>
  `FLOOKUP stored.vs_allocas source_st.cs_next_id = SOME (b,srccap)` by simp[] >>
  `EVERY (supported_scalar_type o SND) xs` by
    gvs[EVERY_MAP, combinTheory.o_DEF] >>
  drule log_output_buffer_shape >> strip_tac >>
  drule abi_encoder_counters >> strip_tac >>
  `stored_st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  `fresh_vars_wrt limit_st stored` by (drule_all log_store_data_fresh >> simp[]) >>
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
   outcap < dimword (:256)` by
    gvs[Excl "enc_def", dimword_def] >>
  Q.SUBGOAL_THEN `((?n. ei = AbiCopy n /\ n < dimword (:256)) \/
    (?infos. ei = AbiComplex infos /\ EXISTS (\(_,_,_,dyn). dyn) infos /\
      EVERY (\(child,asz,mz,dyn). log_scalar_enc_info child) infos))` assume_tac
  >- (asm_simp_tac bool_ss [] >> irule log_tuple_encoder_shape >> simp[]) >>
  drule_all compile_log_store_data_shape >> strip_tac >>
  `source_st.cs_next_id < stored_st.cs_next_id` by decide_tac >>
  drule_all log_allocated_tuple_encode_continue_bounded >>
  disch_then (qx_choose_then `actual` (qx_choose_then `db`
    (MAP_EVERY assume_tac o CONJUNCTS))) >>
  suspend "finish"
QED

Resume log_store_encode_continue_bounded[finish]:
  `run_inst_seq (emitted_insts start end_st) initial = OK actual` by
    (drule_all run_inst_seq_compose_ok >> simp[]) >>
  `inst_extends start end_st` by
    (irule inst_extends_trans >> qexists_tac `stored_st` >> simp[]) >>
  `LENGTH (enc (Tuple (vyper_to_abi_types (get_tenv cx) (MAP SND xs))) (ListV avs)) < dimword (:256)` by decide_tac >>
  qexistsl_tac [`avs`,`actual`,`db`] >> asm_simp_tac bool_ss [] >>
  rpt strip_tac >>
  `!x. op = Var x ==> not_fresh_at start x` by
    (rpt strip_tac >> gvs[abi_decoder_operand_live_def,
      abi_decoder_older_vars_def, not_fresh_at_def] >> metis_tac[]) >>
  `eval_operand op stored = SOME w` by metis_tac[] >>
  `abi_decoder_operand_live stored_st.cs_next_var op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `start.cs_next_var` >> simp[]) >>
  first_x_assum drule_all >> simp[]
QED

Finalise log_store_encode_continue_bounded

Theorem log_store_encode_continue:
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
  fresh_vars_wrt limit_st initial /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  EVERY supported_scalar_type (MAP SND xs) /\ cap < dimword (:256) /\
  abi_size_bound ce.ce_struct_fields (TupleT (MAP SND xs)) < dimword (:256) ==>
  ?avs actual db.
    vyper_to_abi_list (get_tenv cx) (MAP SND xs) vs = SOME avs /\
    run_inst_seq (emitted_insts start end_st) initial = OK actual /\
    inst_extends start end_st /\ fresh_vars_wrt limit_st actual /\
    eval_operand dst.buf_operand actual = SOME (n2w db) /\
    mem_bytes_at db (LENGTH (enc (Tuple (vyper_to_abi_types (get_tenv cx) (MAP SND xs))) (ListV avs))) actual.vs_memory =
      enc (Tuple (vyper_to_abi_types (get_tenv cx) (MAP SND xs))) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Tuple (vyper_to_abi_types (get_tenv cx) (MAP SND xs))) (ListV avs)))) /\
    stmt_state_rel ctx func ce cx es actual /\
    (!op w. abi_decoder_operand_live start.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all log_store_encode_continue_bounded >> strip_tac >>
  qexistsl_tac [`avs`,`actual`,`db`] >> asm_simp_tac bool_ss []
QED

val _ = app (fn (name,th) => if null (hyp th) then ()
  else (app (fn tm => (print_term tm; print "\n")) (hyp th);
        raise Fail ("open theorem: " ^ name)))
  [("log_store_encode_continue_bounded",log_store_encode_continue_bounded),
   ("log_store_encode_continue",log_store_encode_continue)];
