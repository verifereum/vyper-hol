(* Consumer boundary for the owned nonbulk calldata loop. *)
Theory calldataNonbulkLoopEndpoint
Ancestors
  calldataOwnedLoopClosure calldataCoherentOwnedEndpoint calldataSourceMemberFold
  calldataArrayCompileBoundary calldataValidArrayCode calldataMemberResourceFrame
  calldataValidArrayInputs abiDecoderExecution abiDecoderReentry abiDecoderArrayBackedge
  venomMemDefs
  abiDecoderRecursiveArray abiDecoderArrayLoopInit abiDecoderIndexInit
  abiDecoderLoopCode abiDecoderLoopRegisters abiDecoderContract abiDecoderCoherence
  abiDecoderRecursiveLoopLayout abiDecoderArrayInit abiDecoderArrayInitReentry
  abiDecoderValidContract abiDecoderTypedContract abiEncoder exprLoweringProps
  compileEnv vyperABI venomState venomExecSemantics list arithmetic

Theorem calldata_nonbulk_loop_endpoint:
  let Head = \u.
    ~u.vs_halted /\ u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 /\
    LENGTH vs <= maxn /\
    eval_operand src u = SOME (n2w sb) /\ eval_operand dst u = SOME (n2w d) /\
    eval_operand ip u = SOME (n2w ix) /\ mload ix u = 0w /\
    abi_decode_load CALLDATALOAD (n2w sb : bytes32) u = n2w (LENGTH vs) /\
    mem_word_at d u.vs_memory = n2w (LENGTH vs) /\
    FLOOKUP u.vs_allocas index_st.cs_next_id = SOME (ix,32) /\
    FLOOKUP u.vs_allocas oid = SOME (base_addr,cap) /\ MEM (ix,32) old /\
    abi_decoder_ranges CALLDATALOAD (Lit 0w) src dst sb (LENGTH bs)
      d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b reserve_cap u /\
    mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD u) = bs
  in
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) maxn
    (abi_embedded_static_size ce.ce_struct_fields ty) first = ((ip,cnt),loop_st) /\
  abi_decode_index_init index_st = (ip,loop_st) /\
  abi_decode_loop_prefix ip src CALLDATALOAD loop_st = ((hdr,body_lbl,exit_lbl),st0) /\
  compile_abi_decode_dyn_loop dst src CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce ty) (abi_embedded_static_size ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) ip cnt loop_st = ((),last) /\
  fn_has_code first loop_st fn /\ fn_has_code loop_st last fn /\
  (!bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  last.cs_next_var <= limit_st.cs_next_var /\
  first.cs_next_id <= index_st.cs_next_id /\
  (oid < first.cs_next_id \/ last.cs_next_id <= oid) /\
  base_addr <= d /\ d+(32+maxn*type_memory_size tv) <= base_addr+cap /\
  d+(32+maxn*type_memory_size tv) < dimword (:256) /\
  abi_decoder_valid_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    bs (ArrayV (DynArrayV vs)) first src dst CALLDATALOAD (Lit 0w) sb d b reserve_cap initial /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  (is_abi_dynamic ce.ce_struct_fields ty \/
    dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)) /\
  calldata_member_child_contract ce env sf ctx fn site limit_st ty tv /\
  Head header /\
  calldata_member_resource_frame ctx fn site limit_st first.cs_next_id last.cs_next_id
    first.cs_next_var d (32+maxn*type_memory_size tv) initial header old ==>
  ?out scratch.
    ~out.vs_halted /\ out.vs_current_bb = last.cs_current_bb /\
    out.vs_inst_idx = LENGTH last.cs_current_insts /\
    val_wf (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) /\
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d out.vs_memory /\
    calldata_member_resource_frame ctx fn site limit_st first.cs_next_id last.cs_next_id
      first.cs_next_var d (32+maxn*type_memory_size tv) initial out scratch /\
    calldata_member_transfers ctx fn header out
Proof
  qmatch_goalsub_abbrev_tac `LET _ Head` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all calldata_array_compile_boundary >> strip_tac >>
  gnvs[Excl "enc_def", Excl "dec_def", Excl "valid_enc_def"] >>
  suspend "layout"
QED

Resume calldata_nonbulk_loop_endpoint[layout]:
  qpat_x_assum `(_ /\ _) /\ _` (map_every assume_tac o CONJUNCTS) >>
  gnvs[Excl "enc_def", Excl "dec_def", Excl "valid_enc_def"] >>
  drule abi_decoder_loop_suffix_facts >> strip_tac >>
  qpat_x_assum `last.cs_next_id = _` kall_tac >>
  qpat_x_assum `last.cs_next_var = _` kall_tac >>
  gnvs[Excl "enc_def", Excl "dec_def", Excl "valid_enc_def"] >>
  suspend "prepare"
QED

Resume calldata_nonbulk_loop_endpoint[prepare]:
  qpat_x_assum `Head header` mp_tac >>
  simp[Abbr `Head`] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `calldata_member_resource_frame _ _ _ _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE
      [calldata_member_resource_frame_def, calldata_member_wit_def]) >>
  qpat_assum `abi_decoder_valid_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_valid_pre_def]) >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule calldata_valid_array_inputs >> strip_tac >>
  drule_all abi_decode_array_loop_init_shape >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  drule abi_decode_array_loop_index_live >> simp_tac bool_ss [pairTheory.FST] >> strip_tac >>
  suspend "apply"
QED

Resume calldata_nonbulk_loop_endpoint[apply]:
  simp_tac bool_ss [calldata_member_resource_frame_def, calldata_member_wit_def,
    calldata_member_transfers_def, LENGTH, GSYM CONJ_ASSOC,
    AC ADD_ASSOC ADD_COMM] >>
  irule (SIMP_RULE bool_ss [GSYM CONJ_ASSOC, AC ADD_ASSOC ADD_COMM]
    (BETA_RULE (PURE_REWRITE_RULE [GSYM calldata_member_own_def]
      (SIMP_RULE (pure_ss ++ boolSimps.LET_ss) [] calldata_owned_loop_from_header)))) >>
  simp_tac (srw_ss()) [Excl "dec_def", Excl "valid_enc_def"] >>
  qpat_assum `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ = _`
    (irule_at Any) >>
  qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qexists_tac `st1` >>
  qpat_assum `abi_decode_footprint_frame _ initial header` (irule_at Any) >>
  qpat_assum `FLOOKUP header.vs_allocas oid = _` (irule_at Any) >>
  qpat_assum `FLOOKUP header.vs_allocas index_st.cs_next_id = _` (irule_at Any) >>
  qpat_assum `mload ix header = _` (irule_at Any) >>
  qpat_assum `abi_decoder_metadata _ _ _ _ _ _ _`
    (irule_at Any o PURE_REWRITE_RULE [Once vyper_to_abi_type_def]) >>
  qpat_assum `lookup_block last.cs_current_bb _ = _` (irule_at Any) >>
  qpat_assum `header.vs_current_bb = _` (fn th => rewrite_tac [th]) >>
  qpat_assum `lookup_block st1.cs_current_bb _ = _` (irule_at Any) >>
  qpat_assum `abi_decode_load CALLDATALOAD _ header = _` (irule_at Any) >>
  qpat_x_assum `abi_decode_loop_cfg _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_decode_loop_cfg_def]) >>
  qpat_assum `lookup_block hdr _ = _` (irule_at Any) >>
  qpat_assum `lookup_block st0.cs_current_bb _ = _` (irule_at Any) >>
  simp_tac (srw_ss()) [Excl "dec_def", Excl "valid_enc_def"] >>
  suspend "sideconditions"
QED
Resume calldata_nonbulk_loop_endpoint[sideconditions]:
  `first.cs_next_id <= ready.cs_next_id /\
   st1.cs_next_id <= last.cs_next_id /\
   loop_st.cs_next_var <= ready.cs_next_var /\
   ready.cs_next_var <= limit_st.cs_next_var /\
   st1.cs_next_var < limit_st.cs_next_var /\
   loop_st.cs_next_var+4 <= limit_st.cs_next_var /\
   index_st.cs_next_id < ready.cs_next_id` by decide_tac >>
  `ix < dimword (:256)` by
    (qpat_assum `calldata_member_own fn first.cs_next_id last.cs_next_id header`
       (mp_tac o PURE_REWRITE_RULE [calldata_member_own_def]) >>
     disch_then (qspecl_then [`index_st.cs_next_id`,`ix`,`32`] mp_tac) >>
     simp[] >> (impl_tac >- decide_tac) >> simp[]) >>
  `index_st.cs_next_id <> oid` by decide_tac >>
  Q.SUBGOAL_THEN `d+(32+maxn*type_memory_size tv) <= ix \/ ix+32 <= d`
    assume_tac >-
    (qpat_assum `alloca_inv header`
       (strip_assume_tac o PURE_REWRITE_RULE [alloca_inv_def]) >>
     qpat_x_assum `allocas_non_overlapping header`
       (drule_all o PURE_REWRITE_RULE [allocas_non_overlapping_def]) >>
     decide_tac) >>
  `abi_decoder_operand_live loop_st.cs_next_var src /\
   abi_decoder_operand_live loop_st.cs_next_var dst` by
    metis_tac[abi_decoder_operand_live_mono] >>
  `!op. abi_decoder_operand_live loop_st.cs_next_var op ==>
    abi_decoder_operand_live ready.cs_next_var op` by
    metis_tac[abi_decoder_operand_live_mono] >>
  `!op. op = src \/ op = dst \/ op = ip \/
      abi_decoder_operand_live first.cs_next_var op ==>
    op <> Var (STRING #"%" (toString st1.cs_next_var)) /\
    abi_decoder_operand_live loop_st.cs_next_var op` by
    (POP_ASSUM_LIST (fn ths => map_every assume_tac
       (List.filter (fn th =>
         mem (fst (dest_const (fst (strip_comb (concl th)))))
           ["abi_decoder_operand_live", "<=", "<"]) ths)) >>
     gen_tac >> strip_tac >>
     `abi_decoder_operand_live loop_st.cs_next_var op` by
       metis_tac[abi_decoder_operand_live_mono] >>
     (conj_tac >-
       (irule abi_decoder_live_excludes_output >>
        qexists_tac `loop_st.cs_next_var` >> simp[]) >> simp[])) >>
  qpat_assum `vyper_decode_valid_enc _ _`
    (assume_tac o PURE_REWRITE_RULE [Once vyper_to_abi_type_def]) >>
  asm_rewrite_tac [] >>
  suspend "remaining"
QED
Resume calldata_nonbulk_loop_endpoint[remaining]:
  qpat_assum `loop_st.cs_next_var = index_st.cs_next_var + 1`
    (fn th => rewrite_tac [GSYM th]) >>
  qpat_assum `type_memory_size tv = type_memory_bytes ce ty`
    (fn th => rewrite_tac [GSYM th]) >>
  simp[] >> conj_tac >- suspend "child" >> suspend "admissible"
QED
Resume calldata_nonbulk_loop_endpoint[child]:
  rpt gen_tac >> strip_tac >>
  `st1.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  Q.SUBGOAL_THEN `oid < ready.cs_next_id \/ st1.cs_next_id <= oid`
    assume_tac >- decide_tac >>
  Q.SUBGOAL_THEN `ready.cs_blocks = st1.cs_blocks \/
   !bb. lookup_block st1.cs_current_bb fn.fn_blocks = SOME bb ==>
     phi_prefix_length bb.bb_instructions = 0` assume_tac >-
    (disj2_tac >> rpt strip_tac >>
     qpat_x_assum `lookup_block _ _ = SOME _` mp_tac >>
     qpat_assum `lookup_block _ _ = SOME <| bb_label := _; bb_instructions := _ ++ _ |>` mp_tac >>
     qpat_assum `phi_prefix_length (_ ++ _) = 0` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[]) >>
  qpat_assum `type_memory_size tv = type_memory_bytes ce ty`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM th]) >>
      assume_tac (SYM th)) >>
  `base_addr <= d+32+j*type_memory_size tv` by decide_tac >>
  `d+32+j*type_memory_size tv+type_memory_size tv <= base_addr+cap /\
   d+32+j*type_memory_size tv+type_memory_size tv < dimword (:256)` by
    decide_tac >>
  drule_all calldata_array_child_success >>
  qpat_assum `type_memory_bytes ce ty = type_memory_size tv` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> disch_tac >>
  disch_then (qx_choose_then `child` (qx_choose_then `scratch` assume_tac)) >>
  qexistsl [`child`,`scratch`] >>
  gvs[calldata_member_success_def, calldata_member_resource_frame_def,
    calldata_member_wit_def, calldata_member_transfers_def, AC ADD_ASSOC ADD_COMM] >>
  first_assum ACCEPT_TAC
QED
Resume calldata_nonbulk_loop_endpoint[admissible]:
  conj_tac
  >- (Cases_on `is_abi_dynamic ce.ce_struct_fields ty`
      >- (drule_all calldata_dynamic_array_child_admissible >> simp[]) >>
      qpat_x_assum `is_abi_dynamic _ _ \/ dec_info_needs_clamp _` mp_tac >>
      asm_rewrite_tac[] >> disch_tac >>
      drule_all calldata_static_clamped_child_exclusion >> simp[]) >>
  qpat_assum `type_memory_size tv = type_memory_bytes ce ty` mp_tac >>
  qpat_assum `d + (32 + maxn * type_memory_size tv) <= ix \/ ix + 32 <= d` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  gvs[AC ADD_ASSOC ADD_COMM]
QED
Finalise calldata_nonbulk_loop_endpoint
