(* Successful source-valued reentrant Bytes/String decoding with owned memory. *)
Theory calldataValidOwnedBytes
Ancestors
  abiDecoderValidBytesInput abiDecoderValidBytes abiDecoderReentry abiValidBytesReentry calldataBytesLive loweringStateRelDefs
  calldataBytesLeaf calldataFiniteTransport abiDecoderBytesTyped abiDecoderValidContract
  abiDecoderTypedContract abiDecoderContract abiDecoderBytes
  abiDecoderCoherence valueEncodingProps valueEncodingTyping safeSequence fragExecMem
  abiDecoderFrame abiCallerAllocation abiDecoderFootprint compileEnv venomState words list finite_map

Theorem valid_bytes_source_count[local]:
  abi_decoder_valid_bytes_pre n at bs payload st src dst CALLDATALOAD (Lit 0w) (Lit 0w) 0 sb d
    (abi_decoder_prune_vars st.cs_next_var initial) ==>
  w2n (abi_decode_load CALLDATALOAD (n2w sb:bytes32) initial) <= n
Proof
  strip_tac >> drule abi_decoder_valid_bytes_facts >>
  simp[abi_decode_load_def, abi_decoder_prune_source] >> strip_tac >>
  qpat_x_assum `abi_decoder_valid_bytes_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_valid_bytes_pre_def]) >>
  gvs[w2n_n2w]
QED

Theorem valid_bytes_owned_sequence[local]:
  (ty = BaseT (BytesT (Dynamic n)) \/ ty = BaseT (StringT n)) /\
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty) st = ((),last) /\
  abi_decoder_valid_pre ce env sf ty tv bs v st src dst CALLDATALOAD (Lit 0w) (Lit 0w)
    0 sb d b cap initial /\
  last.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  d + type_memory_size tv < dimword (:256) ==>
  type_to_abi_dec_info sf ce ty = DecBytestring n /\
  type_memory_size tv = abi_decode_bytes_copy_size n /\ val_wf tv v /\
  ?actual. run_inst_seq (emitted_insts st last) initial = OK actual /\
    val_in_memory tv v d actual.vs_memory /\
    abi_decode_frame d (type_memory_size tv) initial actual /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    fresh_vars_wrt limit_st actual /\ actual.vs_halted = initial.vs_halted /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op actual = eval_operand op initial)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all (SRULE [] (Q.INST [`base_op` |-> `Lit 0w`] abi_decoder_valid_bytes_input)) >>
  strip_tac >>
  qpat_assum `abi_decoder_valid_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_valid_pre_def]) >>
  qpat_assum `abi_decoder_metadata _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_metadata_def]) >>
  `val_wf tv v` by (drule_all (cj 1 value_has_type_val_wf) >> simp[]) >>
  `d + abi_decode_bytes_copy_size n < dimword (:256)` by metis_tac[] >>
  `n < dimword (:256)` by metis_tac[abi_decode_bytes_extent_capacity_bound] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >> disch_tac >>
  drule_all (SRULE [] (Q.INST [`base_op` |-> `Lit 0w`] abi_decoder_valid_bytes_reentry)) >>
  strip_tac >>
  qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_ranges_def]) >>
  drule valid_bytes_source_count >> disch_tac >>
  drule_all calldata_bytes_accepted_live >> strip_tac >>
  gvs[] >> qexists_tac `t` >> asm_rewrite_tac[] >> metis_tac[]
QED

Theorem valid_bytes_owned_fragment[local]:
  (ty = BaseT (BytesT (Dynamic n)) \/ ty = BaseT (StringT n)) /\
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty) st = ((),last) /\
  abi_decoder_valid_pre ce env sf ty tv bs v st src dst CALLDATALOAD (Lit 0w) (Lit 0w)
    0 sb d b cap initial /\
  last.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  d + type_memory_size tv < dimword (:256) /\
  d + type_memory_size tv <= initial.vs_alloca_next ==>
  frag_exec_mem ctx st last (\s. s = initial)
    (\t. val_wf tv v /\ val_in_memory tv v d t.vs_memory /\
      fresh_vars_wrt limit_st t /\
      abi_decode_frame d (type_memory_size tv) initial t /\
      t.vs_allocas = initial.vs_allocas /\ t.vs_alloca_next = initial.vs_alloca_next /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op t = eval_operand op initial)) (\r. F)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all valid_bytes_owned_sequence >> strip_tac >>
  qpat_assum `abi_decoder_valid_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_valid_pre_def]) >>
  qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_ranges_def]) >>
  `d + abi_decode_bytes_copy_size n < dimword (:256) /\
   d + abi_decode_bytes_copy_size n <= initial.vs_alloca_next /\
   n < dimword (:256)` by metis_tac[abi_decode_bytes_extent_capacity_bound] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >> disch_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bytes_shape >> strip_tac >>
  drule calldata_bytes_opcodes >> strip_tac >>
  irule safeSequenceTheory.frag_exec_mem_run_inst_seq >> asm_rewrite_tac[] >>
  gen_tac >> BETA_TAC >> disch_then SUBST1_TAC >> conj_tac
  >- (ho_match_mp_tac (GEN_ALL calldata_bytes_prefix_live) >>
      goal_assum (drule_at Any) >> asm_rewrite_tac[] >> metis_tac[]) >>
  qexists_tac `actual` >>
  gvs[abi_decode_frame_def, fresh_vars_wrt_def,
    instIdxIndepTheory.eval_op_inst_idx] >> first_assum ACCEPT_TAC
QED

Theorem calldata_valid_bytes_owned_success:
  let Own = \lo hi s.
    !id q k. lo <= id /\ id < hi /\ FLOOKUP s.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= s.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w];
      Safe = \s t. !fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx fn s = r /\
          (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s)
  in
  (ty = BaseT (BytesT (Dynamic n)) \/ ty = BaseT (StringT n)) /\
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty) st = ((),last) /\ fn_has_code st last fn /\
  abi_decoder_valid_pre ce env sf ty tv bs v st src dst CALLDATALOAD (Lit 0w) (Lit 0w)
    0 sb d b cap initial /\
  last.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  alloca_inv initial /\ alloca_frontier_inv ctx fn site initial /\
  Own st.cs_next_id last.cs_next_id initial /\
  FLOOKUP initial.vs_allocas oid = SOME (base_addr,capacity) /\
  (oid < st.cs_next_id \/ last.cs_next_id <= oid) /\
  base_addr <= d /\ d + type_memory_size tv <= base_addr+capacity /\
  d + type_memory_size tv < dimword (:256) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?child. ~child.vs_halted /\ child.vs_current_bb = last.cs_current_bb /\
    child.vs_inst_idx = LENGTH last.cs_current_insts /\
    val_wf tv v /\ val_in_memory tv v d child.vs_memory /\
    fresh_vars_wrt limit_st child /\
    child.vs_call_ctx = initial.vs_call_ctx /\ child.vs_data_section = initial.vs_data_section /\
    child.vs_allocas = initial.vs_allocas /\ child.vs_alloca_next = initial.vs_alloca_next /\
    alloca_inv child /\ alloca_frontier_inv ctx fn site child /\
    Own st.cs_next_id last.cs_next_id child /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op child = eval_operand op initial) /\
    abi_decode_footprint_frame [(d,type_memory_size tv)] initial child /\
    Safe initial child
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `d + type_memory_size tv <= initial.vs_alloca_next` by
    (irule abi_caller_allocation_end >> goal_assum (drule_at Any) >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  drule_all valid_bytes_owned_fragment >> disch_then (qspec_then `ctx` mp_tac) >>
  pure_rewrite_tac[frag_exec_mem_def] >>
  disch_then (qspecl_then [`fn`,`initial`] mp_tac) >>
  asm_simp_tac bool_ss [] >>
  disch_then (qx_choose_then `child` (map_every assume_tac o CONJUNCTS)) >>
  rule_assum_tac BETA_RULE >>
  `alloca_inv child` by
    (irule calldata_alloca_inv_fields >> qexists_tac `initial` >> asm_rewrite_tac[]) >>
  `alloca_frontier_inv ctx fn site child` by
    (irule calldata_alloca_frontier_inv_fields >> qexists_tac `initial` >> asm_rewrite_tac[]) >>
  qexists_tac `child` >> asm_rewrite_tac[] >>
  qpat_x_assum `abi_decode_frame _ _ _ _` mp_tac >>
  simp_tac std_ss [abi_decode_frame_def, abi_decode_footprint_frame_def,
    abi_footprint_disjoint_def] >> strip_tac >> asm_rewrite_tac[] >>
  simp_tac (srw_ss()) [] >> first_assum ACCEPT_TAC
QED
