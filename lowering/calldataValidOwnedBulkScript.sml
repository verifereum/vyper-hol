(* Successful source-valued bulk dynamic-array decoding over actual calldata. *)
Theory calldataValidOwnedBulk
Ancestors
  abiDecoderValidContract abiDecoderBulk abiDecoderBulkReentry abiDecoderBulkExecute loweringStateRelDefs
  abiDecoderCoherence abiDecoderTypedContract abiDecoderContract abiDecoderReentry
  abiValidStatic vyperABIValid abiStaticLayoutProps abiDecodeRanges
  compileEnv valueEncoding vyperABI contractABI venomState words list arithmetic
  abiDecoderCorrectPrimitiveArray abiDecoderPrefixPre abiDecoderReentryPointer
  abiDecoderVarExtend valueEncodingTyping valueEncodingProps calldataBulkLeaf calldataBulkLive
  safeSequence fragExecMem calldataFiniteTransport abiDecoderFootprint abiCallerAllocation finite_map
  abiDecoderFrame

Theorem valid_bulk_canonical_prefix[local]:
  abi_decoder_valid_pre ce env sf (ArrayT elem_ty (Dynamic maxn))
    (ArrayTV elem_tv (Dynamic maxn)) bs v st src dst opc (Lit 0w) hi 0 sb d b cap initial /\
  type_to_abi_dec_info sf ce (ArrayT elem_ty (Dynamic maxn)) =
    DecDynArray ei abi_sz mem_sz F maxn /\ ~dec_info_needs_clamp ei ==>
  LENGTH (enc (vyper_to_abi_type env (ArrayT elem_ty (Dynamic maxn)))
    (dec (vyper_to_abi_type env (ArrayT elem_ty (Dynamic maxn))) bs)) <= LENGTH bs /\
  TAKE (LENGTH (enc (vyper_to_abi_type env (ArrayT elem_ty (Dynamic maxn)))
    (dec (vyper_to_abi_type env (ArrayT elem_ty (Dynamic maxn))) bs))) bs =
    enc (vyper_to_abi_type env (ArrayT elem_ty (Dynamic maxn)))
      (dec (vyper_to_abi_type env (ArrayT elem_ty (Dynamic maxn))) bs)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `abi_decoder_valid_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_valid_pre_def]) >>
  `DecDynArray ei abi_sz mem_sz F maxn =
     type_to_abi_dec_info sf ce (ArrayT elem_ty (Dynamic maxn))` by asm_rewrite_tac[] >>
  drule_all abi_decoder_bulk_metadata >> strip_tac >>
  drule static_layout_compatible_properties >> strip_tac >>
  `vyper_decode_valid_enc (Array NONE (vyper_to_abi_type env elem_ty)) bs` by
    (qpat_x_assum `vyper_decode_valid_enc _ _` mp_tac >>
     simp_tac bool_ss [vyper_to_abi_type_def]) >>
  `valid_enc (Array NONE (vyper_to_abi_type env elem_ty)) bs` by
    (qpat_x_assum `vyper_decode_valid_enc (Array NONE _) bs` mp_tac >>
     simp_tac bool_ss [Once vyper_decode_valid_enc_def, Once valid_enc_def, LET_THM] >>
     strip_tac >> gvs[] >>
     irule (cj 2 vyper_decode_valid_enc_static_mutual) >> simp[]) >>
  drule_all abi_valid_static_array_prefix >>
  asm_simp_tac bool_ss [vyper_to_abi_type_def]
QED

Theorem valid_bulk_empty_window_pre[local]:
  abi_decoder_valid_pre ce env sf (ArrayT elem_ty (Dynamic maxn))
    (ArrayTV elem_tv (Dynamic maxn)) bs v st src dst CALLDATALOAD (Lit 0w) (Lit 0w)
    0 sb d b cap initial /\
  type_to_abi_dec_info sf ce (ArrayT elem_ty (Dynamic maxn)) =
    DecDynArray ei abi_sz mem_sz F maxn /\ ~dec_info_needs_clamp ei /\
  d + type_memory_bytes ce (ArrayT elem_ty (Dynamic maxn)) <= initial.vs_alloca_next /\
  initial.vs_alloca_next < dimword (:256) ==>
  abi_decoder_recursive_pre ce env sf (ArrayT elem_ty (Dynamic maxn))
    (ArrayTV elem_tv (Dynamic maxn)) (DecDynArray ei abi_sz mem_sz F maxn)
    (dec (vyper_to_abi_type env (ArrayT elem_ty (Dynamic maxn))) bs) v
    st st.cs_next_id src dst CALLDATALOAD (Lit 0w) (Lit 0w) 0 sb d initial.vs_alloca_next 0
    (abi_decoder_prune_vars st.cs_next_var initial)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all valid_bulk_canonical_prefix >> strip_tac >>
  `abi_decoder_valid_pre ce env sf (ArrayT elem_ty (Dynamic maxn))
    (ArrayTV elem_tv (Dynamic maxn)) bs v st src dst CALLDATALOAD (Lit 0w) (Lit 0w)
    0 sb d initial.vs_alloca_next 0 initial` by
    (qpat_x_assum `abi_decoder_valid_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[abi_decoder_valid_pre_def, abi_decoder_ranges_def] >>
     disch_then (map_every assume_tac o CONJUNCTS) >> asm_simp_tac (srw_ss()) []) >>
  `abi_decoder_reservation (abi_decoder_entry_floor st) st.cs_next_id
     initial.vs_alloca_next 0 initial` by
    simp[abi_decoder_reservation_def, abi_decoder_entry_floor_def] >>
  drule_all abi_decoder_valid_pre_prefix >> asm_rewrite_tac[]
QED

Theorem valid_bulk_owned_sequence:
  abi_decoder_valid_pre ce env sf (ArrayT elem_ty (Dynamic maxn))
    (ArrayTV elem_tv (Dynamic maxn)) bs v st src dst CALLDATALOAD (Lit 0w) (Lit 0w)
    0 sb d b cap initial /\
  type_to_abi_dec_info sf ce (ArrayT elem_ty (Dynamic maxn)) =
    DecDynArray ei abi_sz mem_sz F maxn /\ ~dec_info_needs_clamp ei /\
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce (ArrayT elem_ty (Dynamic maxn))) st = ((),last) /\
  last.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  d + type_memory_bytes ce (ArrayT elem_ty (Dynamic maxn)) <= initial.vs_alloca_next /\
  initial.vs_alloca_next < dimword (:256) ==>
  val_wf (ArrayTV elem_tv (Dynamic maxn)) v /\
  ?actual. run_inst_seq (emitted_insts st last) initial = OK actual /\
    val_in_memory (ArrayTV elem_tv (Dynamic maxn)) v d actual.vs_memory /\
    abi_decode_frame d (type_memory_bytes ce (ArrayT elem_ty (Dynamic maxn))) initial actual /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    fresh_vars_wrt limit_st actual /\ actual.vs_halted = initial.vs_halted /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op actual = eval_operand op initial)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all valid_bulk_empty_window_pre >> strip_tac >>
  qpat_assum `abi_decoder_valid_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_valid_pre_def]) >>
  drule abi_decoder_dynarray_metadata_shape >> strip_tac >>
  qpat_assum `abi_decoder_metadata _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_metadata_def]) >>
  `val_wf (ArrayTV elem_tv (Dynamic maxn)) v` by
    (drule_all (cj 1 value_has_type_val_wf) >> simp[]) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >> disch_tac >>
  qpat_assum `dec _ bs = ListV _`
    (fn th => rule_assum_tac (PURE_REWRITE_RULE [th])) >>
  qpat_x_assum `v = _` SUBST_ALL_TAC >>
  drule_all abi_decoder_bulk_reentry_sequence >> strip_tac >>
  drule_all abi_decoder_bulk_pre_facts >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
   abi_decode_load CALLDATALOAD (n2w sb : bytes32) initial = n2w (LENGTH vs)` by
    gvs[abi_decoder_prune_eval, abi_decoder_prune_source, abi_decode_load_def] >>
  `w2n (abi_decode_load CALLDATALOAD (n2w sb : bytes32) initial) = LENGTH vs` by
    (asm_rewrite_tac[] >> simp[w2n_n2w]) >>
  `w2n (abi_decode_load CALLDATALOAD (n2w sb : bytes32) initial) * mem_sz < dimword (:256) /\
   w2n (abi_decode_load CALLDATALOAD (n2w sb : bytes32) initial) <= maxn` by
    (qpat_assum `w2n (abi_decode_load _ _ initial) = LENGTH vs`
       (fn th => pure_rewrite_tac[th]) >>
     conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC) >>
  drule_all calldata_bulk_accepted_live >> strip_tac >>
  gvs[] >> qexists_tac `actual` >> asm_rewrite_tac[]
QED

Theorem valid_bulk_owned_fragment[local]:
  abi_decoder_valid_pre ce env sf (ArrayT elem_ty (Dynamic maxn))
    (ArrayTV elem_tv (Dynamic maxn)) bs v st src dst CALLDATALOAD (Lit 0w) (Lit 0w)
    0 sb d b cap initial /\
  type_to_abi_dec_info sf ce (ArrayT elem_ty (Dynamic maxn)) =
    DecDynArray ei abi_sz mem_sz F maxn /\ ~dec_info_needs_clamp ei /\
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce (ArrayT elem_ty (Dynamic maxn))) st = ((),last) /\
  last.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  d + type_memory_bytes ce (ArrayT elem_ty (Dynamic maxn)) <= initial.vs_alloca_next /\
  initial.vs_alloca_next < dimword (:256) ==>
  frag_exec_mem ctx st last (\s. s = initial)
    (\t. val_wf (ArrayTV elem_tv (Dynamic maxn)) v /\
      val_in_memory (ArrayTV elem_tv (Dynamic maxn)) v d t.vs_memory /\
      fresh_vars_wrt limit_st t /\
      abi_decode_frame d (type_memory_bytes ce (ArrayT elem_ty (Dynamic maxn))) initial t /\
      t.vs_allocas = initial.vs_allocas /\ t.vs_alloca_next = initial.vs_alloca_next /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op t = eval_operand op initial)) (\r. F)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
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
  irule safeSequenceTheory.frag_exec_mem_run_inst_seq >> asm_rewrite_tac[] >>
  gen_tac >> BETA_TAC >> disch_then SUBST1_TAC >> conj_tac
  >- (ho_match_mp_tac (GEN_ALL calldata_bulk_live_prefix_safe) >>
      goal_assum (drule_at Any) >> asm_rewrite_tac[] >> metis_tac[]) >>
  qexists_tac `actual` >>
  gvs[abi_decode_frame_def, fresh_vars_wrt_def,
    instIdxIndepTheory.eval_op_inst_idx] >> first_assum ACCEPT_TAC
QED

Theorem calldata_valid_bulk_owned_success:
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
      initial child /\ Safe initial child
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `d + type_memory_bytes ce (ArrayT elem_ty (Dynamic maxn)) <= initial.vs_alloca_next` by
    (irule abi_caller_allocation_end >> goal_assum (drule_at Any) >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  drule_all valid_bulk_owned_fragment >> disch_then (qspec_then `ctx` mp_tac) >>
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
