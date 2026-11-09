(* Concrete bytes child execution, with a physical owner independent of its destination. *)
Theory entryReachBodyOwnedBytesChild
Ancestors
  valueEncodingDefs loweringStateRelDefs entryReachBodySequenceObservations entryReachBodyOwnedLoop
  entryReachBodyOwnedRegion entryReachBodyOperationalPath entryReachBodyExactArrayLoop
  abiEncoderRegisteredEffect allocaBudgetProps allocaFrontierBound abiAllocationHistory
  ctorAbiActualBytes abiDecoderCoherence abiDecoderTypedContract abiDecoderDynamicLoopSetup
  abiDecoderBytesTyped abiDecoderArraySetupInputs abiDecoderReentry abiDecoderCounters
  abiDecoderArrayInit abiDecodeRanges venomExecSemantics venomExecProofs valueEncoding contractABI words
  venomMemDefs venomState venomInstProps instIdxIndep finite_map pred_set
  entryReachBodyCanonicalBytes entryReachBodyCanonicalChildAddress
  abiDecoderLoopSetup abiDecoderIndexedAddress abiDecoderContract abiEncoder
  emitHelper emitHelperProps compileEnv venomInst rich_list list arithmetic fragExec exprLoweringProps

Theorem bytes_child_sequence_observations[local]:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w)
    (DecBytestring n) az mz st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops))
    CALLDATALOAD (Lit 0w) (Lit 0w) (DecBytestring n) middle = ((),last) /\
  last.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  run_inst_seq (emitted_insts st last) s = OK t ==>
  entry_loop_fields s t /\ fresh_vars_wrt limit_st t
Proof
  strip_tac >> irule entry_sequence_observations >>
  asm_rewrite_tac[] >> qexists_tac `emitted_insts st last` >> asm_rewrite_tac[] >>
  qpat_x_assum `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _` mp_tac >>
  simp[abi_decode_array_element_setup_def, compile_abi_decode_to_buf_def,
    compile_abi_decode_dyn_elem_ptr_def, abi_decode_indexed_address_def,
    dec_info_needs_offset_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def] >> metis_tac[LESS_ADD]
QED

(* Lift a single allocation-free write window to the owned operational interface. *)
Theorem owned_sequence_endpoint[local]:
  st'.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts st'.cs_current_insts /\ fn_has_code st st' fn /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st') /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  run_inst_seq (emitted_insts st st') s = OK t /\
  entry_loop_fields s t /\ fresh_vars_wrt limit_st t /\
  abi_decode_frame d sz s t /\ t.vs_allocas = s.vs_allocas /\
  t.vs_alloca_next = s.vs_alloca_next /\
  entry_owned_loop_resources ctx fn site cid p oid root extent region_d cap s ==>
  entry_decode_path ctx fn s (t with vs_inst_idx := LENGTH st'.cs_current_insts) /\
  entry_loop_fields s (t with vs_inst_idx := LENGTH st'.cs_current_insts) /\
  fresh_vars_wrt limit_st (t with vs_inst_idx := LENGTH st'.cs_current_insts) /\
  abi_encoder_registered_effect {} [(d,sz)] s
    (t with vs_inst_idx := LENGTH st'.cs_current_insts) /\
  entry_owned_loop_resources ctx fn site cid p oid root extent region_d cap
    (t with vs_inst_idx := LENGTH st'.cs_current_insts)
Proof
  strip_tac >>
  `entry_decode_path ctx fn s (t with vs_inst_idx := LENGTH st'.cs_current_insts)` by
    (irule entry_decode_emitted_path >> asm_rewrite_tac[] >>
     goal_assum (drule_at Any) >> asm_rewrite_tac[]) >>
  `abi_encoder_registered_effect {} [(d,sz)] s t` by
    (fs[abi_encoder_registered_effect_def, abi_decode_frame_def, entry_loop_fields_def] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `remaining_alloca_budget (fn_insts fn) t = remaining_alloca_budget (fn_insts fn) s` by
    (irule remaining_alloca_budget_domain_cong >> simp[]) >>
  fs[entry_owned_loop_resources_def, entry_owned_region_def,
     alloca_frontier_inv_def, abi_alloca_history_def, alloca_inv_def,
     allocas_non_overlapping_def, alloca_next_valid_def,
     entry_loop_fields_def, fresh_vars_wrt_def, abi_encoder_registered_effect_def] >>
  rpt conj_tac >> first_x_assum MATCH_ACCEPT_TAC
QED

Theorem entry_owned_bytes_child:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce ty) (abi_embedded_static_size ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops))
    CALLDATALOAD (Lit 0w) (Lit 0w) (DecBytestring n) middle = ((),last) /\
  type_to_abi_dec_info sf ce ty = DecBytestring n /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV avs) (ArrayV (DynArrayV xs)) /\
  j < LENGTH xs /\ is_dynamic (vyper_to_abi_type env ty) /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) src dst sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap s /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    (abi_decode_source CALLDATALOAD s) =
    enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  eval_operand ip s = SOME p /\ mload (w2n p) s = n2w j /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  last.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st last fn /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d cap s ==>
  ?t. val_in_memory tv (EL j xs) (d+32+j*type_memory_bytes ce ty) t.vs_memory /\
    entry_loop_fields s t /\ fresh_vars_wrt limit_st t /\
    entry_decode_path ctx fn s t /\
    abi_encoder_registered_effect {}
      [(d+32+j*type_memory_bytes ce ty,type_memory_bytes ce ty)] s t /\
    entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d cap t /\
    t.vs_current_bb = last.cs_current_bb /\
    t.vs_inst_idx = LENGTH last.cs_current_insts /\ ~t.vs_halted /\
    eval_operand (FST ops) t = SOME (n2w j) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    abi_decode_frame (d+32+j*type_memory_bytes ce ty) (type_memory_bytes ce ty) s t /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `middle.cs_next_var <= last.cs_next_var` by
    (qpat_x_assum `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _` mp_tac >>
     simp[compile_abi_decode_to_buf_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
     rpt strip_tac >> gvs[]) >>
  `middle.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all entry_canonical_dynamic_child_address >>
  disch_then (qx_choose_then `prepared` strip_assume_tac) >>
  drule_all ctor_actual_bytestring_metadata >> strip_tac >>
  `?actual. run_inst_seq (emitted_insts middle last) prepared = OK actual /\
    val_in_memory tv (EL j xs) (d+32+j*type_memory_bytes ce ty) actual.vs_memory /\
    abi_decode_frame (d+32+j*type_memory_bytes ce ty) (type_memory_bytes ce ty) prepared actual /\
    (!op. abi_decoder_operand_live middle.cs_next_var op ==>
      eval_operand op actual = eval_operand op prepared) /\
    actual.vs_allocas = prepared.vs_allocas /\ actual.vs_alloca_next = prepared.vs_alloca_next` by
    suspend "bytes_run" >>
  suspend "endpoint"
QED

Resume entry_owned_bytes_child[bytes_run]:
  `sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) < dimword (:256) /\
   d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) < dimword (:256)` by
    fs[abi_decoder_ranges_def] >>
  `sb + abi_array_child_offset NONE (vyper_to_abi_type env ty) avs j +
     LENGTH (enc (Bytes NONE) (contractABI$BytesV bs)) < dimword (:256) /\
   d+32+j*type_memory_bytes ce ty+abi_decode_bytes_copy_size n < dimword (:256)` by
    (gvs[] >> decide_tac) >>
  `n < dimword (:256)` by
    (mp_tac (cj 3 abi_decoder_bytes_copy_size) >> decide_tac) >>
  qpat_x_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `abi_decoder_metadata _ _ (ArrayT _ _) _ _ _ _` kall_tac >>
  qpat_x_assum `abi_decoder_coherent _ _ _ (ArrayT _ _) _` kall_tac >>
  qpat_x_assum `entry_owned_loop_resources _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `fn_has_code _ _ _` kall_tac >>
  rule_assum_tac (PURE_REWRITE_RULE [abi_decode_source_def]) >>
  drule entry_canonical_bytes_sequence >>
  disch_then (qspecl_then
    [`sb+abi_array_child_offset NONE (vyper_to_abi_type env ty) avs j`,
     `prepared`,`d+32+j*type_memory_bytes ce ty`,`bs`] mp_tac) >>
  (impl_tac >- gvs[Excl "enc_def"]) >> strip_tac >>
  goal_assum (drule_at Any) >> gvs[Excl "enc_def"]
QED
Resume entry_owned_bytes_child[endpoint]:
  map_every (fn q => qpat_x_assum q kall_tac)
    [`abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _`,
     `abi_decoder_coherent _ _ _ (ArrayT _ _) _`, `abi_decoder_coherent _ _ _ ty tv`,
     `abi_decoder_metadata _ _ (ArrayT _ _) _ _ _ _`,
     `abi_decoder_metadata _ _ ty tv _ _ _`,
     `mem_bytes_at sb _ _ = _`, `mem_bytes_at (_ + abi_array_child_offset _ _ _ _) _ _ = _`,
     `j < LENGTH xs`, `is_dynamic _`, `eval_operand ip s = _`, `mload _ s = _`,
     `eval_operand (FST (SND ops)) prepared = _`,
     `eval_operand (SND (SND ops)) prepared = _`,
     `EL j avs = _`, `LENGTH bs <= n`, `enc _ _ = enc _ _`,
     `type_memory_bytes ce ty = _`, `!d mem. val_in_memory _ _ _ _ <=> _`,
     `sb + abi_array_child_offset _ _ _ _ < _`,
     `sb + abi_array_child_offset _ _ _ _ + _ <= _`,
     `d+32+j*type_memory_bytes ce ty < _`,
     `d+32+j*type_memory_bytes ce ty+_ <= _`, `abi_embedded_static_size _ _ <= _`] >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_element_setup_shape >> strip_tac >>
  drule_all abi_decoder_bytes_shape >> strip_tac >>
  `inst_extends middle last` by
    (qpat_x_assum `isPREFIX middle.cs_current_insts last.cs_current_insts` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[IS_PREFIX_APPEND] >> strip_tac >>
     simp[inst_extends_def, emitted_insts_def, DROP_LENGTH_APPEND]) >>
  `run_inst_seq (emitted_insts st last) s = OK actual` by
    (drule_all run_inst_seq_compose_ok >> simp[]) >>
  `entry_loop_fields s actual /\ fresh_vars_wrt limit_st actual` by
    (irule bytes_child_sequence_observations >>
     goal_assum (drule_at Any) >> asm_rewrite_tac[] >> metis_tac[]) >>
  suspend "endpoint_finish"
QED
Resume entry_owned_bytes_child[endpoint_finish]:
  `eval_operand (FST ops) actual = SOME (n2w j)` by metis_tac[] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts st last)` by
    (irule abi_decoder_emitted_every_append >>
     qexists_tac `middle` >> asm_rewrite_tac[]) >>
  `isPREFIX st.cs_current_insts last.cs_current_insts` by
    (irule IS_PREFIX_TRANS >> qexists_tac `middle.cs_current_insts` >> asm_rewrite_tac[]) >>
  `abi_decode_frame (d+32+j*type_memory_bytes ce ty) (type_memory_bytes ce ty) s actual /\
   actual.vs_allocas = s.vs_allocas /\ actual.vs_alloca_next = s.vs_alloca_next` by
    (gvs[abi_decode_frame_def, abi_decoder_address_frame_def] >>
     rpt strip_tac >> first_x_assum irule >> asm_rewrite_tac[]) >>
  `actual.vs_halted = s.vs_halted /\ actual.vs_current_bb = s.vs_current_bb` by
    (conj_tac >> irule run_inst_seq_preserves_field >>
     qexists_tac `emitted_insts st last` >> asm_rewrite_tac[] >> rpt strip_tac >>
     fs[EVERY_MEM] >> metis_tac[step_preserves_halted, step_preserves_control_flow,
                              step_inst_non_invoke]) >>
  `!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
     eval_operand op actual = SOME w` by
    (rpt strip_tac >>
     `st.cs_next_var <= middle.cs_next_var` by
       (qpat_x_assum `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ = _` mp_tac >>
        simp[abi_decode_array_element_setup_def, compile_abi_decode_dyn_elem_ptr_def,
          abi_decode_indexed_address_def, dec_info_needs_offset_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def,
          emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
        rpt strip_tac >> gvs[]) >>
     `abi_decoder_operand_live middle.cs_next_var op` by
       (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
     fs[abi_decoder_address_frame_def]) >>
  `entry_decode_path ctx fn s (actual with vs_inst_idx := LENGTH last.cs_current_insts) /\
   entry_loop_fields s (actual with vs_inst_idx := LENGTH last.cs_current_insts) /\
   fresh_vars_wrt limit_st (actual with vs_inst_idx := LENGTH last.cs_current_insts) /\
   abi_encoder_registered_effect {} [(d+32+j*type_memory_bytes ce ty,type_memory_bytes ce ty)]
     s (actual with vs_inst_idx := LENGTH last.cs_current_insts) /\
   entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d cap
     (actual with vs_inst_idx := LENGTH last.cs_current_insts)` by
    (irule owned_sequence_endpoint >> asm_rewrite_tac[] >>
     goal_assum (drule_at Any) >> asm_rewrite_tac[]) >>
  qexists_tac `actual with vs_inst_idx := LENGTH last.cs_current_insts` >>
  asm_simp_tac (srw_ss()) [eval_operand_def, lookup_var_def] >>
  fs[abi_decode_frame_def] >> first_assum ACCEPT_TAC
QED
Finalise entry_owned_bytes_child
