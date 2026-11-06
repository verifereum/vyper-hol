(* Same-witness resource endpoint for the actual nonbulk array decoder. *)
Theory calldataNonbulkOwnedEndpoint
Ancestors
  calldataValidHeaderLocalFrontier calldataCoherentOwnedEndpoint
  calldataNonbulkLoopEndpoint
  calldataSourceMemberFold calldataOwnedLoopClosure calldataArrayCompileBoundary
  calldataRecursiveProducers abiDecoderValidArray abiDecoderCoherence
  abiDecoderValidContract abiDecoderTypedContract calldataMemberResourceFrame
  abiDecoderLoopCode abiDecoderContract abiDecoderCode abiDecoderCounters
  abiDecoderCorrectPrimitiveArray abiEncoder exprLowering abiDecoderRecursiveArray
  abiDecoderArrayLoopInit allocaFrontierBound
  compileEnv valueEncoding list arithmetic

Theorem calldata_nonbulk_array_child_contract:
  unit_alloca_budget ctx < dimword (:256) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  (is_abi_dynamic ce.ce_struct_fields ty \/
    dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)) /\
  calldata_member_child_contract ce env sf ctx fn site limit_st ty tv ==>
  calldata_member_child_contract ce env sf ctx fn site limit_st
    (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rewrite_tac[calldata_member_child_contract_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `abi_decoder_valid_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_valid_pre_def]) >>
  drule abi_decoder_dynarray_metadata_shape >> strip_tac >>
  gnvs[Excl "enc_def", Excl "dec_def", Excl "valid_enc_def"] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [Once type_to_abi_dec_info_def] >> strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  `first.cs_blocks <> last.cs_blocks` by
    (drule abi_decoder_recursive_array_adds_blocks >>
     disch_then (qspec_then `fn` mp_tac) >> asm_rewrite_tac[]) >>
  `!bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0` by metis_tac[] >>
  drule calldata_nonbulk_parent_intervals >>
  disch_then (qspec_then `fn` mp_tac) >>
  asm_rewrite_tac[] >> strip_tac >>
  suspend "endpoint"
QED

Resume calldata_nonbulk_array_child_contract[endpoint]:
  drule abi_decode_loop_array_trace >>
  asm_rewrite_tac[] >> strip_tac >>
  qpat_x_assum `((_,_),_) = (_,_)`
    (map_every assume_tac o CONJUNCTS o SIMP_RULE bool_ss [pairTheory.PAIR_EQ]) >>
  gnvs[Excl "enc_def", Excl "dec_def", Excl "valid_enc_def"] >>
  drule_all calldata_array_compile_boundary >> strip_tac >>
  gnvs[Excl "enc_def", Excl "dec_def", Excl "valid_enc_def"] >>
  qpat_x_assum `(_ = labels) /\ _` (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `(ops = _) /\ _` (map_every assume_tac o CONJUNCTS) >>
  gnvs[Excl "enc_def", Excl "dec_def", Excl "valid_enc_def"] >>
  suspend "header"
QED

Resume calldata_nonbulk_array_child_contract[header]:
  drule abi_decoder_coherent_array_capacity >> strip_tac >>
  `s.vs_alloca_next < dimword (:256)` by
    (irule alloca_frontier_inv_bound >> goal_assum (drule_at Any) >> simp[]) >>
  `loop_st.cs_next_id <= last.cs_next_id /\
   loop_st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  qpat_assum `p + type_memory_size _ <= _`
    (assume_tac o SIMP_RULE bool_ss [type_memory_size_def]) >>
  drule_all (BETA_RULE (PURE_REWRITE_RULE [GSYM calldata_member_own_def]
    (SIMP_RULE (pure_ss ++ boolSimps.LET_ss) []
      calldata_valid_header_producer_local_frontier))) >>
  strip_tac >> suspend "loop"
QED
Resume calldata_nonbulk_array_child_contract[loop]:
  `calldata_member_resource_frame ctx fn site limit_st
    first.cs_next_id last.cs_next_id first.cs_next_var p
    (32+maxn*type_memory_size tv) s (jump_to hdr t) [(p',32)]` by
    (asm_rewrite_tac[calldata_member_resource_frame_def, calldata_member_wit_def]) >>
  `header_st' = header_st` by
    (qpat_assum `abi_decode_dynarray_prefix _ _ _ _ _ _ = ((),guard_st)` mp_tac >>
     qpat_assum `abi_decode_dynarray_prefix _ _ _ _ _ _ = ((),guard_st')` mp_tac >>
     qpat_assum `abi_decode_array_header _ _ _ guard_st = _` mp_tac >>
     qpat_assum `abi_decode_array_header _ _ _ guard_st' = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[]) >>
  qpat_assum `p + type_memory_size _ < _`
    (assume_tac o SIMP_RULE bool_ss [type_memory_size_def]) >>
  drule_at (Pat `calldata_member_resource_frame _ _ _ _ _ _ _ _ _ _ _ _`)
    (BETA_RULE (SIMP_RULE (pure_ss ++ boolSimps.LET_ss) []
      calldata_nonbulk_loop_endpoint)) >>
  disch_then (drule_at (Pat `abi_decoder_valid_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `abi_decode_loop_prefix _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `abi_decode_index_init _ = _`)) >>
  disch_then (drule_at (Pat `abi_decode_array_loop_init _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = SOME (n2w _)`)) >>
  disch_then (qspecl_then [`oid`,`cap`,`base_addr`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  strip_tac >> suspend "finish"
QED
Resume calldata_nonbulk_array_child_contract[finish]:
  qexistsl [`out`,`scratch`] >>
  asm_rewrite_tac[calldata_member_success_def, type_memory_size_def] >>
  qpat_assum `calldata_member_transfers _ _ _ out` mp_tac >>
  qpat_assum `!fuel r. run_from fuel ctx fn (jump_to hdr t) = r /\ _ ==> _` mp_tac >>
  qpat_assum `(!fuel. mem_safe_run fuel ctx fn (jump_to hdr t)) ==> _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  rewrite_tac[calldata_member_transfers_def] >>
  rpt strip_tac >> metis_tac[]
QED
Finalise calldata_nonbulk_array_child_contract
