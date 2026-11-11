(* The store's write footprint is the sole mutable part of statement state. *)
Theory stmtSimLogStoreContinue
Ancestors
  stmtSimLogDataRun stmtSimLogDataFrame stmtSimLogAllocate stmtSimLogEncodeFrame
  stmtSimLogExecFields abiDecoderFrame compileEnv exprLoweringProps
  stmtSimLogEncodeFields exprSimBufferStore context emitHelper emitHelperProps
  stmtSimLogData stmtSimLogTopics stmtSimLogDataInput vyperABI supportedTypes stmtLowering venomInst venomState words list rich_list arithmetic

Theorem log_write_frame_fields:
  log_write_frame st b n s t ==>
  log_encode_external t = log_encode_external s /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  abi_decode_footprint_frame [(b,n)] s t
Proof
  simp_tac bool_ss [log_write_frame_def] >> strip_tac >>
  `log_encode_external t = log_encode_external s /\
   t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section` by
    gvs[log_encode_external_def, venom_state_component_equality] >>
  simp[abi_decode_footprint_frame_def, abi_footprint_disjoint_def, ADD_COMM] >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED

Theorem log_write_frame_stmt:
  stmt_state_rel ctx func ce cx es s /\ log_write_frame st b n s t /\
  local_ptrs_reserved ce st /\ LENGTH s.vs_memory <= LENGTH t.vs_memory /\
  (!name lo sz. local_region ce es.scopes s name lo sz ==>
    lo+sz <= b \/ b+n <= lo) /\
  (ce.ce_is_ctor ==> !name tv v off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    off+type_memory_size tv <= b \/ b+n <= off) ==>
  stmt_state_rel ctx func ce cx es t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule log_write_frame_fields >> strip_tac >>
  `!name entry p sz. lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    lookup_var p t = lookup_var p s` by
    (rpt strip_tac >>
     `not_fresh_at st p` by
       (fs[local_ptrs_reserved_def] >> first_x_assum drule >> simp[]) >>
     fs[log_write_frame_def]) >>
  `!x. ce.ce_imm_alloca = SOME (Var x) ==> lookup_var x t = lookup_var x s` by
    (rpt strip_tac >>
     `not_fresh_at st x` by fs[local_ptrs_reserved_def] >>
     fs[log_write_frame_def]) >>
  irule log_encode_continuation >>
  qexistsl_tac [`F`,`[(b,n)]`,`32`,`s`,`0`] >>
  simp[abi_footprint_disjoint_def] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem log_store_scalar_safe[local]:
  supported_scalar_type ty /\ compile_store_memory ce src dst ty ty st = ((),final) ==>
  inst_extends st final /\ same_blocks st final /\
  EVERY (\i. log_encode_safe_opcode i.inst_opcode) (emitted_insts st final)
Proof
  rpt strip_tac >>
  `is_word_type ty \/ is_bytestring_type ty` by
    (drule log_scalar_topic_shape >>
     Cases_on `is_bytestring_type ty` >> simp[]) >>
  Cases_on `is_word_type ty` >>
  qpat_x_assum `compile_store_memory _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_store_memory_def, compile_store_bytestring_def,
    compile_bytestring_copy_len_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[] >>
  simp[same_blocks_def, inst_extends_def, emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, IS_PREFIX_APPEND, log_encode_safe_opcode_def, mk_inst_def]
QED

Theorem log_store_data_safe:
  !xs buf off st final. EVERY (supported_scalar_type o SND) xs /\
    compile_log_store_data ce xs (MAP SND xs) buf off st = ((),final) ==>
  inst_extends st final /\ same_blocks st final /\
  EVERY (\i. log_encode_safe_opcode i.inst_opcode) (emitted_insts st final)
Proof
  Induct_on `xs`
  >- simp[compile_log_store_data_def, comp_return_def, same_blocks_def, inst_extends_def, emitted_insts_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >> strip_tac >>
  fs[] >>
  drule_all compile_log_store_data_scalar_split >> strip_tac >>
  drule_all log_store_scalar_safe >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  drule log_encode_emit_safe >>
  (impl_tac >- simp[log_encode_safe_opcode_def]) >> strip_tac >>
  `inst_extends st sn /\ same_blocks st sn /\
   EVERY (\i. log_encode_safe_opcode i.inst_opcode) (emitted_insts st sn)` by
    (irule log_encode_safe_append >> qexists_tac `sm` >> simp[]) >>
  irule log_encode_safe_append >> qexists_tac `sn` >> simp[]
QED

Theorem log_store_data_memory_mono:
  compile_log_store_data ce xs (MAP SND xs) buf off sa = ((),sb) /\
  EVERY (supported_scalar_type o SND) xs /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  strip_tac >> drule_all log_store_data_safe >> strip_tac >>
  drule_all log_encode_run_memory_mono >> simp[]
QED

Theorem log_store_data_stmt:
  compile_log_store_data ce xs (MAP SND xs) buf off sa = ((),sb) /\
  LIST_REL (log_data_source cx b cap s) xs vs /\
  EVERY (\(op,ty). !x. op = Var x ==> not_fresh_at sa x) xs /\
  (!x. buf = Var x ==> not_fresh_at sa x) /\
  eval_operand buf s = SOME (n2w b) /\
  off + SUM (MAP (type_memory_bytes ce) (MAP SND xs)) <= cap /\
  b + cap < dimword (:256) /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sa /\
  (!name lo sz. local_region ce es.scopes s name lo sz ==>
    lo+sz <= b+off \/ b+off+SUM (MAP (type_memory_bytes ce) (MAP SND xs)) <= lo) /\
  (ce.ce_is_ctor ==> !name tv v p.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc p) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    p+type_memory_size tv <= b+off \/
    b+off+SUM (MAP (type_memory_bytes ce) (MAP SND xs)) <= p) ==>
  inst_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
  ?t avs. run_inst_seq (emitted_insts sa sb) s = OK t /\
    stmt_state_rel ctx func ce cx es t /\
    vyper_to_abi_list (get_tenv cx) (MAP SND xs) vs = SOME avs /\
    abi_encoder_input (type_to_abi_enc_info sf ce (TupleT (MAP SND xs)))
      (vyper_to_abi_type (get_tenv cx) (TupleT (MAP SND xs))) (ListV avs)
      (b+off) (SUM (MAP (type_memory_bytes ce) (MAP SND xs))) t.vs_memory /\
    log_data_layout cx (MAP SND xs) vs (b+off) t.vs_memory /\
    log_write_frame sa (b+off) (SUM (MAP (type_memory_bytes ce) (MAP SND xs))) s t /\
    LIST_REL (log_data_source cx b cap t) xs vs /\
    eval_operand buf t = SOME (n2w b) /\
    (!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
      eval_operand op t = eval_operand op s)
Proof
  strip_tac >> drule_all compile_log_store_data_input >>
  disch_then (qspec_then `sf` strip_assume_tac) >>
  drule log_data_sources_types >> strip_tac >>
  `LENGTH s.vs_memory <= LENGTH t.vs_memory` by
    (drule_all log_store_data_memory_mono >> simp[]) >>
  `stmt_state_rel ctx func ce cx es t` by
    (drule_all log_write_frame_stmt >> simp[]) >>
  gvs[vyper_to_abi_type_def] >> rpt strip_tac >>
  drule_all log_write_frame_operand >> simp[]
QED
