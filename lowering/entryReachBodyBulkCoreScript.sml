(* Metadata-free execution core, shared by canonical and source callers. *)
Theory entryReachBodyBulkCore
Ancestors
  abiDecoderBulk abiDecoderLayout abiDecoderContract abiDecoderCoherence
  abiDecoderTypedContract compileEnv exprLowering vyperABI vyperTyping
  valueEncoding vyperValue contractABI words list arithmetic byte venomState
  abiStaticDynarrayLayout abiStaticLayoutProps abiDecoderFrame abiDecoderFrameCompose
  entryReachBodySequenceObservations entryReachBodyExactArrayLoop
  abiEncoder emitHelper emitHelperProps exprLoweringProps venomInst rich_list venomExecSemantics
  abiDecoderBulkExecute abiDecoderArrayInitExec abiDecoderCounters calldataBulkLive
  entryReachBodyOperationalPath entrySinkExtraction entryReachBodyScratchSet
  entryReachBodyOwnedRegion abiEncoderRegisteredEffect abiAllocationHistory
  allocaFrontierBound allocaBudgetProps venomMemDefs

Theorem bulk_core_source[local]:
  static_layout_compatible ce env ty tv /\ all_have_type tv xs /\
  vyper_to_abi_same env ty xs = SOME avs /\ LENGTH xs <= maxn /\
  mem_sz = type_memory_size tv /\
  type_memory_bytes ce (ArrayT ty (Dynamic maxn)) = 32 + maxn * mem_sz /\
  sb + LENGTH (enc (vyper_to_abi_type env (ArrayT ty (Dynamic maxn))) (ListV avs)) < dimword (:256) /\
  d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) < dimword (:256) /\
  mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env (ArrayT ty (Dynamic maxn))) (ListV avs)))
    (abi_decode_source CALLDATALOAD s) =
    enc (vyper_to_abi_type env (ArrayT ty (Dynamic maxn))) (ListV avs) ==>
  abi_decode_load CALLDATALOAD (n2w sb : bytes32) s = n2w (LENGTH xs) /\
  sb + 32 < dimword (:256) /\ d + 32 < dimword (:256) /\
  LENGTH xs * mem_sz < dimword (:256) /\
  32 + LENGTH xs * mem_sz <= type_memory_bytes ce (ArrayT ty (Dynamic maxn))
Proof
  strip_tac >> drule_all static_same_canonical_layout >> strip_tac >>
  drule static_layout_compatible_properties >> strip_tac >>
  `LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) =
    32 + LENGTH xs * type_memory_size tv` by
    simp[static_dynarray_encoding, LENGTH_word_to_bytes, Excl "enc_def"] >>
  `mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    (abi_decode_source CALLDATALOAD s) = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)` by
    fs[vyper_to_abi_type_def] >>
  drule_all static_dynarray_source_windows >> strip_tac >>
  `LENGTH xs * mem_sz <= maxn * mem_sz` by simp[LE_MULT_RCANCEL] >>
  gvs[vyper_to_abi_type_def, abi_decode_load_def, abi_decode_source_def,
      mload_def, mem_word_at_def, mem_bytes_at_def, Excl "enc_def"] >> decide_tac
QED

Theorem bulk_core_sequence[local]:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w)
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),last) /\
  ~dec_info_needs_clamp ei /\
  static_layout_compatible ce env ty tv /\ all_have_type tv xs /\
  vyper_to_abi_same env ty xs = SOME avs /\ LENGTH xs <= maxn /\
  abi_sz = type_memory_size tv /\ mem_sz = type_memory_size tv /\ maxn < dimword (:256) /\
  type_memory_bytes ce (ArrayT ty (Dynamic maxn)) = 32 + maxn * mem_sz /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  sb + LENGTH (enc (vyper_to_abi_type env (ArrayT ty (Dynamic maxn))) (ListV avs)) < dimword (:256) /\
  d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) < dimword (:256) /\
  mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env (ArrayT ty (Dynamic maxn))) (ListV avs)))
    (abi_decode_source CALLDATALOAD s) =
    enc (vyper_to_abi_type env (ArrayT ty (Dynamic maxn))) (ListV avs) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst ==>
  ?t. run_inst_seq (emitted_insts st last) s = OK t /\
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV xs)) d t.vs_memory /\
    abi_decode_frame d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) s t /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w) /\ inst_extends st last
Proof
  strip_tac >> drule_all bulk_core_source >> strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  `LENGTH xs < dimword (:256)` by decide_tac >>
  `w2n (abi_decode_load CALLDATALOAD (n2w sb : bytes32) s) = LENGTH xs` by simp[] >>
  `w2n ((n2w sb : bytes32) + 32w) = sb + 32` by
    simp[wordsTheory.word_add_n2w, wordsTheory.w2n_n2w, wordsTheory.word_add_def] >>
  `w2n (abi_decode_load CALLDATALOAD (n2w sb : bytes32) s) <= maxn MOD dimword (:256)` by simp[] >>
  `w2n (abi_decode_load CALLDATALOAD (n2w sb : bytes32) s) * mem_sz < dimword (:256)` by
    (qpat_x_assum `LENGTH xs * mem_sz < _` mp_tac >> simp[]) >>
  drule_all calldata_bulk_accepted_live_mod >> strip_tac >>
  drule_all abi_decoder_bulk_shape >> strip_tac >>
  `inst_extends st last` by
    fs[inst_extends_def, emitted_insts_def, IS_PREFIX_APPEND, DROP_LENGTH_APPEND] >>
  `mem_bytes_at (d+32) (LENGTH xs * type_memory_size tv) t.vs_memory =
    mem_bytes_at (sb+32) (LENGTH xs * type_memory_size tv) (abi_decode_source CALLDATALOAD s)` by
    (qpat_x_assum `mem_bytes_at (d+32) _ t.vs_memory = _` mp_tac >> simp[abi_decode_source_def]) >>
  `mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    (abi_decode_source CALLDATALOAD s) = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)` by
    fs[vyper_to_abi_type_def] >>
  `val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV xs)) d t.vs_memory` by
    (irule static_dynarray_copied_layout >> simp[Excl "enc_def"] >>
     goal_assum (drule_at Any) >> simp[Excl "enc_def"] >>
     goal_assum (drule_at Any) >> simp[Excl "enc_def"] >>
     qexistsl_tac [`sb`, `abi_decode_source CALLDATALOAD s`] >> simp[Excl "enc_def"]) >>
  qexists_tac `t` >> simp[] >>
  irule abi_decode_frame_widen >> qexistsl_tac [`d`, `32 + LENGTH xs * mem_sz`] >> simp[] >>
  qpat_x_assum `abi_decode_frame d _ s t` mp_tac >> simp[]
QED

Theorem bulk_core_store_code[local]:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w)
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),last) /\
  ~dec_info_needs_clamp ei /\ last.cs_next_var <= limit_st.cs_next_var ==>
  ?pre store post.
    emitted_insts st last = pre ++ [store] ++ post /\
    store.inst_opcode = MSTORE /\ store.inst_outputs = [] /\
    EVERY (\i. MEM i.inst_opcode
      [MLOAD; ADD; MUL; CALLDATALOAD; GT; ISZERO; ASSERT; CALLDATACOPY] /\
      EVERY (\x. ?k. x = STRING #"%" (toString k) /\ k < limit_st.cs_next_var)
        i.inst_outputs) pre /\
    EVERY (\i. MEM i.inst_opcode
      [MLOAD; ADD; MUL; CALLDATALOAD; GT; ISZERO; ASSERT; CALLDATACOPY] /\
      EVERY (\x. ?k. x = STRING #"%" (toString k) /\ k < limit_st.cs_next_var)
        i.inst_outputs) post
Proof
  simp[compile_abi_decode_to_buf_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def, emitted_insts_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def,
      emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >> gvs[DROP_LENGTH_APPEND] >>
  qmatch_goalsub_abbrev_tac `code = _ ++ [_] ++ _` >>
  qexistsl_tac [`TAKE 5 code`, `EL 5 code`, `DROP 6 code`] >>
  simp[Abbr `code`, mk_inst_def]
QED

Theorem bulk_core_observations[local]:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w)
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),last) /\
  ~dec_info_needs_clamp ei /\ last.cs_next_var <= limit_st.cs_next_var /\
  run_inst_seq (emitted_insts st last) s = OK t /\ fresh_vars_wrt limit_st s ==>
  entry_loop_fields s t /\ fresh_vars_wrt limit_st t
Proof
  strip_tac >> drule_all bulk_core_store_code >> strip_tac >>
  `?u. run_inst_seq pre s = OK u` by
    (spose_not_then assume_tac >> drule run_inst_seq_append_err >>
     disch_then (qspec_then `[store] ++ post` mp_tac) >> gvs[]) >>
  `run_inst_seq ([store] ++ post) u = OK t` by
    (drule run_inst_seq_append >> disch_then (qspec_then `[store] ++ post` mp_tac) >> gvs[]) >>
  drule_all entry_sequence_observations >> strip_tac >>
  qpat_x_assum `run_inst_seq ([store] ++ post) u = OK t` mp_tac >>
  simp[run_inst_seq_def, AllCaseEqs()] >> strip_tac >>
  rename1 `step_inst_base store u = OK v` >>
  `entry_loop_fields u v /\ fresh_vars_wrt limit_st v` by
    (qpat_x_assum `step_inst_base store u = OK v` mp_tac >>
     simp[step_inst_base_def, exec_write2_def, AllCaseEqs()] >> strip_tac >>
     gvs[entry_loop_fields_def, fresh_vars_wrt_def, mstore_def,
         write_memory_with_expansion_def]) >>
  drule_all entry_sequence_observations >> strip_tac >> fs[entry_loop_fields_def]
QED

Theorem entry_bulk_owned_core:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w)
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),last) /\
  ~dec_info_needs_clamp ei /\
  static_layout_compatible ce env ty tv /\ all_have_type tv xs /\
  vyper_to_abi_same env ty xs = SOME avs /\ LENGTH xs <= maxn /\
  abi_sz = type_memory_size tv /\ mem_sz = type_memory_size tv /\ maxn < dimword (:256) /\
  type_memory_bytes ce (ArrayT ty (Dynamic maxn)) = 32 + maxn * mem_sz /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  sb + LENGTH (enc (vyper_to_abi_type env (ArrayT ty (Dynamic maxn))) (ListV avs)) < dimword (:256) /\
  d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) < dimword (:256) /\
  mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env (ArrayT ty (Dynamic maxn))) (ListV avs)))
    (abi_decode_source CALLDATALOAD s) =
    enc (vyper_to_abi_type env (ArrayT ty (Dynamic maxn))) (ListV avs) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  last.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st last fn /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  alloca_inv s /\ abi_alloca_history (fn_insts fn) s /\ alloca_frontier_inv ctx fn site s /\
  entry_owned_region oid root extent d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) s /\
  entry_scratch_ready sites b cap s ==>
  ?t. val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV xs)) d t.vs_memory /\
    entry_decode_path ctx fn s t /\ entry_loop_fields s t /\ fresh_vars_wrt limit_st t /\
    entry_scratch_ready sites b cap t /\ alloca_inv t /\
    abi_alloca_history (fn_insts fn) t /\ alloca_frontier_inv ctx fn site t /\
    entry_owned_region oid root extent d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) t /\
    abi_encoder_registered_effect child_sites [(d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)))] s t /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w) /\
    ~t.vs_halted /\ t.vs_current_bb = last.cs_current_bb /\
    t.vs_inst_idx = LENGTH last.cs_current_insts /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> drule_all bulk_core_sequence >> strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bulk_allocation_shape >> strip_tac >>
  drule_all abi_decoder_guard_sequence_fields >> strip_tac >>
  drule_all bulk_core_observations >> strip_tac >>
  drule_all abi_decoder_bulk_shape >> strip_tac >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  `entry_decode_path ctx fn s (t with vs_inst_idx := LENGTH last.cs_current_insts)` by
    (irule entry_decode_emitted_path >> simp[] >> qexists_tac `st` >> simp[]) >>
  `entry_scratch_ready sites b cap (t with vs_inst_idx := LENGTH last.cs_current_insts)` by
    (qpat_x_assum `entry_scratch_ready sites b cap s` mp_tac >>
     pure_rewrite_tac[entry_scratch_ready_def, entry_scratch_missing_def,
       venom_state_accfupds] >> asm_rewrite_tac[]) >>
  qexists_tac `t with vs_inst_idx := LENGTH last.cs_current_insts` >>
  gvs[entry_loop_fields_def, fresh_vars_wrt_def, eval_operand_def,
      abi_alloca_history_def, alloca_frontier_inv_def, remaining_alloca_budget_def,
      entry_owned_region_def, alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
      abi_encoder_registered_effect_def, abi_decode_frame_def, Excl "enc_def"] >>
  conj_tac >- asm_rewrite_tac[] >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED
