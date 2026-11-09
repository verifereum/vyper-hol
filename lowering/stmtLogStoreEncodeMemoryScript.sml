(* Checked stores followed by the allocated scalar tuple encoder. *)
Theory stmtLogStoreEncodeMemory
Ancestors
  stmtLogAllocatedEncodeMemory stmtLogEncodingCapacity stmtLogDataMemory loweringStateRelDefs
  stmtSimLogStoreCompose stmtSimLogStoreContinue stmtSimLogStoreFresh
  stmtSimLogEncodeLayout stmtSimLogDataInput stmtSimLogAllocate stmtSimLogStoreEncode
  abiDecoderReentry exprLoweringProps localPtrsProps abiEncoderCounters
  stmtSimLogTrace emitHelperProps stmtSimLogDataRun vyperTypeABI vyperABI
  compileEnv supportedTypes contractABI context venomMemDefs fragExecMem
  fragExec words list arithmetic

Theorem log_store_encode_continue_mem:
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
  abi_size_bound ce.ce_struct_fields (TupleT (MAP SND xs)) < dimword (:256) /\
  LIST_REL (\arg v. !w n. ~is_word_type (SND arg) /\
    eval_operand (FST arg) initial = SOME w /\
    ((?bs. v = BytesV bs /\ n = LENGTH bs) \/
     (?str. v = StringV str /\ n = LENGTH str)) ==>
    w2n w + 32 + 32 * ((n+31) DIV 32) <= initial.vs_alloca_next) xs vs ==>
  run_inst_seq_mem_ok (emitted_insts start end_st) initial /\
  (!t. run_inst_seq (emitted_insts start end_st) initial = OK t ==>
    initial.vs_alloca_next <= t.vs_alloca_next) /\
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
    LENGTH (enc (Tuple (vyper_to_abi_types (get_tenv cx) (MAP SND xs))) (ListV avs)) < dimword (:256) /\
    db + LENGTH (enc (Tuple (vyper_to_abi_types (get_tenv cx) (MAP SND xs))) (ListV avs)) <= actual.vs_alloca_next
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all log_store_encode_continue_bounded >> disch_then (mk_asm "functional") >>
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

Resume log_store_encode_continue_mem[encode]:
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
   outcap < dimword (:256)` by gvs[Excl "enc_def", dimword_def] >>
  Q.SUBGOAL_THEN `((?n. ei = AbiCopy n /\ n < dimword (:256)) \/
    (?infos. ei = AbiComplex infos /\ EXISTS (\(_,_,_,dyn). dyn) infos /\
      EVERY (\(child,asz,mz,dyn). log_scalar_enc_info child) infos))` assume_tac
  >- (asm_simp_tac bool_ss [] >> irule log_tuple_encoder_shape >> simp[]) >>
  drule_all compile_log_store_data_shape >> strip_tac >>
  `source_st.cs_next_id < stored_st.cs_next_id` by decide_tac >>
  drule_all log_allocated_tuple_encode_continue_mem >> strip_tac >>
  suspend "finish"
QED

Resume log_store_encode_continue_mem[finish]:
  `b+srccap <= initial.vs_alloca_next` by
    (`alloca_next_valid initial` by fs[stmt_state_rel_def, alloca_inv_def] >>
     qpat_x_assum `alloca_next_valid initial` mp_tac >>
     simp[alloca_next_valid_def] >> disch_then drule >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts start stored_st) initial` by
    (drule_all compile_log_store_data_run_mem >> simp[]) >>
  `emitted_insts start end_st = emitted_insts start stored_st ++ emitted_insts stored_st end_st` by
    (irule emitted_insts_append >> gvs[inst_extends_def]) >>
  `run_inst_seq (emitted_insts start end_st) initial = OK actual` by
    (drule_all run_inst_seq_compose_ok >> simp[]) >>
  conj_tac
  >- (asm_rewrite_tac[] >> irule run_inst_seq_mem_ok_append >>
      simp[] >> rpt strip_tac >> gvs[]) >>
  conj_tac >- (rpt strip_tac >> gvs[] >> metis_tac[]) >>
  asm_x "functional" (qx_choose_then `favs` (qx_choose_then `finished`
    (qx_choose_then `dbase` (map_every assume_tac o CONJUNCTS)))) >>
  `favs = avs` by gvs[] >>
  `finished = actual` by gvs[] >>
  `dbase = db` by gvs[] >>
  qexistsl_tac [`avs`,`actual`,`db`] >> gvs[]
QED

Finalise log_store_encode_continue_mem
