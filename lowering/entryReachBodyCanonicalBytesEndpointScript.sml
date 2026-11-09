(* Bytes/String metadata and actual canonical decoder endpoints. *)
Theory entryReachBodyCanonicalBytesEndpoint
Ancestors
  valueEncodingDefs loweringStateRelDefs entryReachBodyCanonicalBytes abiDecoderBytes abiDecoderBytestring abiDecoderBytestringCases abiDecoderString
  abiDecoderCoherence abiDecoderTypedContract abiDecoderBytesTyped
  abiDecoderContract compileEnv exprLowering vyperABI vyperTyping
  valueEncoding vyperValue contractABI words list rich_list arithmetic
  abiEncoder emitHelper emitHelperProps exprLoweringProps venomInst venomState
  entryReachBodySequenceObservations entryReachBodyExactArrayLoop
  entryReachBodyOperationalPath entrySinkExtraction entryReachBodyScratchSet
  entryReachBodyOwnedRegion abiEncoderRegisteredEffect abiAllocationHistory
  allocaFrontierBound allocaBudgetProps venomMemDefs

Theorem bytes_metadata_payload[local]:
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecBytestring n /\
  abi_decoder_metadata ce env ty tv (DecBytestring n) av v ==>
  ?bs. av = contractABI$BytesV bs /\ LENGTH bs <= n /\
    type_memory_bytes ce ty = abi_decode_bytes_copy_size n /\
    enc (vyper_to_abi_type env ty) av = enc (Bytes NONE) (contractABI$BytesV bs) /\
    (!d mem. val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV bs) d mem ==>
      val_in_memory tv v d mem)
Proof
  strip_tac >> drule abi_decoder_bytestring_cases >>
  disch_then (qspec_then `n` mp_tac) >> simp[] >> strip_tac >> gvs[] >>
  Cases_on `av` >>
  gvs[abi_decoder_metadata_def, vyper_to_abi_type_def, vyper_base_to_abi_type_def,
      has_type_def, abi_to_vyper_def, AllCaseEqs(), type_memory_bytes_def,
      abi_decode_bytes_copy_size_def, abi_decoder_string_memory, enc_def, compatible_bound_def]
QED

Theorem bytes_observation_code[local]:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) (DecBytestring n) st = ((),last) /\
  last.cs_next_var <= limit_st.cs_next_var ==>
  EVERY (\i. MEM i.inst_opcode
    [MLOAD; ADD; MUL; CALLDATALOAD; GT; ISZERO; ASSERT; CALLDATACOPY] /\
    EVERY (\x. ?k. x = STRING #"%" (toString k) /\ k < limit_st.cs_next_var)
      i.inst_outputs) (emitted_insts st last)
Proof
  simp[compile_abi_decode_to_buf_def, compile_abi_dec_addr_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def, emitted_insts_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  gvs[DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem bytes_canonical_typed_sequence[local]:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) (DecBytestring n) st = ((),last) /\
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecBytestring n /\
  abi_decoder_metadata ce env ty tv (DecBytestring n) av v /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  n < dimword (:256) /\ sb+LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
  d+abi_decode_bytes_copy_size n < dimword (:256) /\
  mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av))
    (abi_decode_source CALLDATALOAD s) = enc (vyper_to_abi_type env ty) av ==>
  ?t. run_inst_seq (emitted_insts st last) s = OK t /\
    val_in_memory tv v d t.vs_memory /\
    abi_decode_frame d (type_memory_bytes ce ty) s t /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==> eval_operand op t = eval_operand op s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> drule_all bytes_metadata_payload >> strip_tac >>
  `mem_bytes_at sb (LENGTH (enc (Bytes NONE) (contractABI$BytesV bs)))
    s.vs_call_ctx.cc_calldata = enc (Bytes NONE) (contractABI$BytesV bs)` by
    fs[abi_decode_source_def] >>
  `sb+LENGTH (enc (Bytes NONE) (contractABI$BytesV bs)) < dimword (:256)` by metis_tac[] >>
  drule_all entry_canonical_bytes_sequence >> strip_tac >>
  qexists_tac `t` >> simp[]
QED

Theorem entry_canonical_bytes_owned_endpoint:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) (DecBytestring n) st = ((),last) /\
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecBytestring n /\
  abi_decoder_metadata ce env ty tv (DecBytestring n) av v /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  n < dimword (:256) /\ sb+LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
  d+abi_decode_bytes_copy_size n < dimword (:256) /\
  mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av))
    (abi_decode_source CALLDATALOAD s) = enc (vyper_to_abi_type env ty) av /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  last.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st last fn /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  alloca_inv s /\ abi_alloca_history (fn_insts fn) s /\ alloca_frontier_inv ctx fn site s /\
  entry_owned_region oid root extent d (type_memory_bytes ce ty) s /\
  entry_scratch_ready sites b cap s ==>
  ?t. val_in_memory tv v d t.vs_memory /\ entry_decode_path ctx fn s t /\
    entry_loop_fields s t /\ fresh_vars_wrt limit_st t /\ entry_scratch_ready sites b cap t /\
    alloca_inv t /\ abi_alloca_history (fn_insts fn) t /\ alloca_frontier_inv ctx fn site t /\
    entry_owned_region oid root extent d (type_memory_bytes ce ty) t /\
    abi_encoder_registered_effect child_sites [(d,type_memory_bytes ce ty)] s t /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w) /\
    ~t.vs_halted /\ t.vs_current_bb = last.cs_current_bb /\
    t.vs_inst_idx = LENGTH last.cs_current_insts /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> drule_all bytes_canonical_typed_sequence >> strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bytes_shape >> strip_tac >>
  `entry_loop_fields s t /\ fresh_vars_wrt limit_st t` by
    (drule_all bytes_observation_code >> strip_tac >>
     drule_all entry_sequence_observations >> simp[]) >>
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
      abi_encoder_registered_effect_def, abi_decode_frame_def] >>
  conj_tac >- (asm_rewrite_tac[]) >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED
