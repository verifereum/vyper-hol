(* Source-valued finite decoders with unconditional memory pullback. *)
Theory calldataFiniteEndpoints
Ancestors
  successfulSequenceEndpoint calldataValidOwnedBytes abiDecoderValidBytesInput loweringStateRelDefs
  abiDecoderValidBytes abiDecoderReentry abiValidBytesReentry calldataBytesLive
  calldataBytesLeaf calldataFiniteTransport abiDecoderBytesTyped abiDecoderValidContract
  abiDecoderTypedContract abiDecoderContract abiDecoderBytes abiDecoderCoherence
  valueEncodingProps valueEncodingTyping safeSequence fragExecMem abiDecoderFrame
  abiCallerAllocation abiDecoderFootprint compileEnv emitHelperProps instIdxIndep
  venomState venomExecSemantics words list finite_map arithmetic rich_list
  exprLoweringProps venomMemDefs allocaFrontierBound
  calldataValidOwnedWord calldataValidOwnedBulk calldataWordLive calldataWordLeaf
  abiDecoderClampedWord calldataBulkLive calldataBulkLeaf abiDecoderBulk

Theorem calldata_valid_bytes_owned_endpoint:
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
    Safe initial child /\
    ((!fuel. mem_safe_run fuel ctx fn child) ==> !fuel. mem_safe_run fuel ctx fn initial)
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_valid_bytes_input >> strip_tac >>
  qpat_assum `abi_decoder_valid_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_valid_pre_def]) >>
  qpat_assum `abi_decoder_metadata _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_metadata_def]) >>
  `val_wf tv v` by (drule_all (cj 1 value_has_type_val_wf) >> simp[]) >>
  `d + abi_decode_bytes_copy_size n < dimword (:256)` by metis_tac[] >>
  `n < dimword (:256)` by metis_tac[abi_decode_bytes_extent_capacity_bound] >>
  `d + type_memory_size tv <= initial.vs_alloca_next` by
    (irule abi_caller_allocation_end >> goal_assum (drule_at Any) >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >> disch_tac >>
  drule_all abi_decoder_valid_bytes_reentry >> strip_tac >>
  qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_ranges_def]) >>
  suspend "sequence"
QED

Resume calldata_valid_bytes_owned_endpoint[sequence]:
  `w2n (abi_decode_load CALLDATALOAD (n2w sb:bytes32) initial) <= n` by
    (qpat_x_assum `abi_decoder_valid_bytes_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     drule abi_decoder_valid_bytes_facts >>
     simp[abi_decode_load_def, abi_decoder_prune_source] >> strip_tac >>
     qpat_x_assum `abi_decoder_valid_bytes_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_valid_bytes_pre_def]) >>
     gvs[w2n_n2w]) >>
  drule_all calldata_bytes_accepted_live >> strip_tac >>
  qpat_x_assum `run_inst_seq _ _ = OK _` mp_tac >>
  asm_rewrite_tac[] >> simp_tac (srw_ss()) [] >> disch_then SUBST_ALL_TAC >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bytes_shape >> strip_tac >>
  drule calldata_bytes_opcodes >> strip_tac >>
  `d + abi_decode_bytes_copy_size n <= initial.vs_alloca_next` by
    (qpat_x_assum `d + type_memory_size tv <= initial.vs_alloca_next` mp_tac >>
     asm_rewrite_tac[]) >>
  `run_inst_seq_mem_ok (emitted_insts st last) initial` by
    (irule run_inst_seq_mem_ok_of_prefix_safe >> reverse conj_tac
     >- (qpat_x_assum `EVERY _ (emitted_insts st last)`
           (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
         rpt (pop_assum kall_tac) >> simp[EVERY_MEM]) >>
     drule calldata_bytes_prefix_live >>
     disch_then (qspecl_then [`initial`, `n2w sb`, `d`] mp_tac) >>
     asm_rewrite_tac[]) >>
  suspend "endpoint"
QED

Resume calldata_valid_bytes_owned_endpoint[endpoint]:
  `inst_extends st last` by
    (qpat_assum `st.cs_current_insts <<= last.cs_current_insts` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[inst_extends_def, IS_PREFIX_APPEND, emitted_insts_def] >>
     strip_tac >>
     simp[DROP_LENGTH_APPEND]) >>
  mp_tac (Q.INST [`s` |-> `initial`, `ready` |-> `last`, `P` |-> `\s:venom_state. T`]
    (SPEC_ALL successful_sequence_endpoint)) >>
  asm_simp_tac (srw_ss()) [] >> strip_tac >>
  `alloca_inv t` by
    (irule calldata_alloca_inv_fields >> qexists_tac `initial` >> asm_rewrite_tac[]) >>
  `alloca_frontier_inv ctx fn site t` by
    (irule calldata_alloca_frontier_inv_fields >> qexists_tac `initial` >> asm_rewrite_tac[]) >>
  `val_in_memory tv v d t.vs_memory` by metis_tac[] >>
  qexists_tac `t with vs_inst_idx := LENGTH last.cs_current_insts` >>
  asm_simp_tac (srw_ss()) [eval_op_inst_idx, fresh_vars_wrt_def,
    alloca_inv_def, alloca_frontier_inv_def] >>
  suspend "frame"
QED
Resume calldata_valid_bytes_owned_endpoint[frame]:
  rule_assum_tac BETA_RULE >>
  qpat_x_assum `LET _ _` (strip_assume_tac o SIMP_RULE (srw_ss()) [LET_THM]) >>
  qpat_x_assum `fresh_vars_wrt limit_st t` mp_tac >>
  pure_rewrite_tac[fresh_vars_wrt_def] >> disch_tac >>
  asm_rewrite_tac[] >>
  qpat_x_assum `abi_decode_frame _ _ _ _` mp_tac >>
  simp_tac std_ss [abi_decode_frame_def, abi_decode_footprint_frame_def,
    abi_footprint_disjoint_def] >> strip_tac >> asm_rewrite_tac[] >>
  simp_tac (srw_ss()) [] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
Finalise calldata_valid_bytes_owned_endpoint

Theorem calldata_valid_word_owned_endpoint:
  let Own = \lo hi s.
    !id q k. lo <= id /\ id < hi /\ FLOOKUP s.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= s.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w];
      Safe = \s t. !fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx fn s = r /\
          (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s)
  in
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
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
    Safe initial child /\
    ((!fuel. mem_safe_run fuel ctx fn child) ==> !fuel. mem_safe_run fuel ctx fn initial)
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all valid_word_owned_sequence >> strip_tac >>
  `d + type_memory_size tv <= initial.vs_alloca_next` by
    (irule abi_caller_allocation_end >> goal_assum (drule_at Any) >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  qpat_assum `abi_decoder_valid_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_valid_pre_def]) >>
  qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_ranges_def]) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >> disch_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_clamped_word_shape >> strip_tac >>
  drule calldata_word_opcodes >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts st last)` by
    (qpat_assum `EVERY _ (emitted_insts st last)` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[EVERY_MEM] >> metis_tac[]) >>
  `d < dimword (:256) /\ d + 32 <= initial.vs_alloca_next` by decide_tac >>
  `run_inst_seq_mem_ok (emitted_insts st last) initial` by
    (irule run_inst_seq_mem_ok_of_prefix_safe >> reverse conj_tac
     >- (fs[EVERY_MEM] >> metis_tac[]) >>
     ho_match_mp_tac (GEN_ALL calldata_word_prefix_live) >>
     goal_assum (drule_at Any) >> asm_rewrite_tac[] >> metis_tac[]) >>
  suspend "endpoint"
QED

Resume calldata_valid_word_owned_endpoint[endpoint]:
  `inst_extends st last` by
    (qpat_assum `st.cs_current_insts <<= last.cs_current_insts` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[inst_extends_def, IS_PREFIX_APPEND, emitted_insts_def] >>
     strip_tac >> simp[DROP_LENGTH_APPEND]) >>
  mp_tac (Q.INST [`s` |-> `initial`, `t` |-> `actual`, `ready` |-> `last`,
    `P` |-> `\s:venom_state. T`] (SPEC_ALL successful_sequence_endpoint)) >>
  asm_simp_tac (srw_ss()) [] >> strip_tac >>
  `alloca_inv actual` by
    (irule calldata_alloca_inv_fields >> qexists_tac `initial` >> asm_rewrite_tac[]) >>
  `alloca_frontier_inv ctx fn site actual` by
    (irule calldata_alloca_frontier_inv_fields >> qexists_tac `initial` >> asm_rewrite_tac[]) >>
  qexists_tac `actual with vs_inst_idx := LENGTH last.cs_current_insts` >>
  asm_simp_tac (srw_ss()) [eval_op_inst_idx, fresh_vars_wrt_def,
    alloca_inv_def, alloca_frontier_inv_def] >>
  rule_assum_tac BETA_RULE >>
  qpat_x_assum `LET _ _` (strip_assume_tac o SIMP_RULE (srw_ss()) [LET_THM]) >>
  qpat_x_assum `fresh_vars_wrt limit_st actual` mp_tac >>
  pure_rewrite_tac[fresh_vars_wrt_def] >> disch_tac >>
  asm_rewrite_tac[] >>
  qpat_x_assum `abi_decode_frame _ _ _ _` mp_tac >>
  simp_tac std_ss [abi_decode_frame_def, abi_decode_footprint_frame_def,
    abi_footprint_disjoint_def] >> strip_tac >> asm_rewrite_tac[] >>
  simp_tac (srw_ss()) [] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
Finalise calldata_valid_word_owned_endpoint

Theorem calldata_valid_bulk_owned_endpoint:
  let Own = \lo hi s.
    !id q k. lo <= id /\ id < hi /\ FLOOKUP s.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= s.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w];
      Safe = \s t. !fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx fn s = r /\
          (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s)
  in
  abi_decoder_valid_pre ce env sf (ArrayT elem_ty (Dynamic maxn))
    (ArrayTV elem_tv (Dynamic maxn)) bs v st src dst CALLDATALOAD (Lit 0w) (Lit 0w)
    0 sb d b cap initial /\
  type_to_abi_dec_info sf ce (ArrayT elem_ty (Dynamic maxn)) =
    DecDynArray ei abi_sz mem_sz F maxn /\ ~dec_info_needs_clamp ei /\
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce (ArrayT elem_ty (Dynamic maxn))) st = ((),last) /\
  fn_has_code st last fn /\
  last.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  alloca_inv initial /\ alloca_frontier_inv ctx fn site initial /\
  Own st.cs_next_id last.cs_next_id initial /\
  FLOOKUP initial.vs_allocas oid = SOME (base_addr,capacity) /\
  (oid < st.cs_next_id \/ last.cs_next_id <= oid) /\
  base_addr <= d /\
  d + type_memory_bytes ce (ArrayT elem_ty (Dynamic maxn)) <= base_addr+capacity /\
  initial.vs_alloca_next < dimword (:256) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?child. ~child.vs_halted /\ child.vs_current_bb = last.cs_current_bb /\
    child.vs_inst_idx = LENGTH last.cs_current_insts /\
    val_wf (ArrayTV elem_tv (Dynamic maxn)) v /\
    val_in_memory (ArrayTV elem_tv (Dynamic maxn)) v d child.vs_memory /\
    fresh_vars_wrt limit_st child /\
    child.vs_call_ctx = initial.vs_call_ctx /\ child.vs_data_section = initial.vs_data_section /\
    child.vs_allocas = initial.vs_allocas /\ child.vs_alloca_next = initial.vs_alloca_next /\
    alloca_inv child /\ alloca_frontier_inv ctx fn site child /\
    Own st.cs_next_id last.cs_next_id child /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op child = eval_operand op initial) /\
    abi_decode_footprint_frame [(d,type_memory_bytes ce (ArrayT elem_ty (Dynamic maxn)))]
      initial child /\ Safe initial child /\
    ((!fuel. mem_safe_run fuel ctx fn child) ==> !fuel. mem_safe_run fuel ctx fn initial)
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `d + type_memory_bytes ce (ArrayT elem_ty (Dynamic maxn)) <= initial.vs_alloca_next` by
    (irule abi_caller_allocation_end >> goal_assum (drule_at Any) >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  drule_all valid_bulk_owned_sequence >> strip_tac >>
  qpat_assum `abi_decoder_valid_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_valid_pre_def]) >>
  qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_ranges_def]) >>
  `DecDynArray ei abi_sz mem_sz F maxn =
    type_to_abi_dec_info sf ce (ArrayT elem_ty (Dynamic maxn))` by asm_rewrite_tac[] >>
  drule_all abi_decoder_bulk_metadata >> strip_tac >>
  qpat_x_assum `DecDynArray _ _ _ _ _ = type_to_abi_dec_info _ _ _` kall_tac >>
  `d+(32+maxn*mem_sz) < dimword (:256) /\
   d+(32+maxn*mem_sz) <= initial.vs_alloca_next` by metis_tac[LESS_EQ_LESS_TRANS] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  qpat_assum `type_to_abi_dec_info sf ce (ArrayT _ _) = _`
    (fn th => pure_rewrite_tac[th]) >> disch_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bulk_shape >> strip_tac >>
  drule_all calldata_bulk_opcodes >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts st last) initial` by
    (irule run_inst_seq_mem_ok_of_prefix_safe >> reverse conj_tac
     >- (qpat_assum `EVERY _ (emitted_insts st last)` mp_tac >>
         rpt (pop_assum kall_tac) >> simp[EVERY_MEM] >> metis_tac[]) >>
     ho_match_mp_tac (GEN_ALL calldata_bulk_live_prefix_safe) >>
     goal_assum (drule_at Any) >> asm_rewrite_tac[] >> metis_tac[]) >>
  suspend "endpoint"
QED

Resume calldata_valid_bulk_owned_endpoint[endpoint]:
  `inst_extends st last` by
    (qpat_assum `st.cs_current_insts <<= last.cs_current_insts` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[inst_extends_def, IS_PREFIX_APPEND, emitted_insts_def] >>
     strip_tac >> simp[DROP_LENGTH_APPEND]) >>
  mp_tac (Q.INST [`s` |-> `initial`, `t` |-> `actual`, `ready` |-> `last`,
    `P` |-> `\s:venom_state. T`] (SPEC_ALL successful_sequence_endpoint)) >>
  asm_simp_tac (srw_ss()) [] >> strip_tac >>
  `alloca_inv actual` by
    (irule calldata_alloca_inv_fields >> qexists_tac `initial` >> asm_rewrite_tac[]) >>
  `alloca_frontier_inv ctx fn site actual` by
    (irule calldata_alloca_frontier_inv_fields >> qexists_tac `initial` >> asm_rewrite_tac[]) >>
  qexists_tac `actual with vs_inst_idx := LENGTH last.cs_current_insts` >>
  asm_simp_tac (srw_ss()) [eval_op_inst_idx, fresh_vars_wrt_def,
    alloca_inv_def, alloca_frontier_inv_def] >>
  rule_assum_tac BETA_RULE >>
  qpat_x_assum `LET _ _` (strip_assume_tac o SIMP_RULE (srw_ss()) [LET_THM]) >>
  qpat_x_assum `fresh_vars_wrt limit_st actual` mp_tac >>
  pure_rewrite_tac[fresh_vars_wrt_def] >> disch_tac >>
  asm_rewrite_tac[] >>
  qpat_x_assum `abi_decode_frame _ _ _ _` mp_tac >>
  simp_tac std_ss [abi_decode_frame_def, abi_decode_footprint_frame_def,
    abi_footprint_disjoint_def] >> strip_tac >> asm_rewrite_tac[] >>
  simp_tac (srw_ss()) [] >> conj_tac
  >- (qpat_x_assum `!p k. _ ==> mem_bytes_at p k actual.vs_memory = _` mp_tac >>
      asm_simp_tac (srw_ss()) []) >> asm_rewrite_tac[]
QED
Finalise calldata_valid_bulk_owned_endpoint
