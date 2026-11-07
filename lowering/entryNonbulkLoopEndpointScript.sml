(* Joint entry endpoint for an initialized nonbulk array decoder. *)
Theory entryNonbulkLoopEndpoint
Ancestors
  entryNonbulkConfig entryDecoderLoopEndpoint entryDecoderJointLoop
  entryDecoderMemberEndpoint entryDecoderStateFrame calldataMemberResourceFrame
  calldataSourceMemberFold abiDecoderValidArrayEntry abiDecoderContract
  abiDecoderCoherence abiDecoderTypedContract compileEnv abiEncoder
  venomState venomExecSemantics list arithmetic

Theorem entry_nonbulk_loop_endpoint:
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
  entry_member_child_contract ce env sf ctx fn site limit_st ty tv /\
  Head header /\
  calldata_member_resource_frame ctx fn site limit_st first.cs_next_id last.cs_next_id
    first.cs_next_var d (32+maxn*type_memory_size tv) initial header old /\
  fn_inst_ids_distinct fn /\ alloca_history fn header /\ entry_decoder_obs initial header /\
  EntryLoopSafe ctx fn initial header /\ EntryLoopPull ctx fn initial header ==>
  ?out scratch.
    calldata_member_success ctx fn site limit_st first last d
      (type_memory_size (ArrayTV tv (Dynamic maxn))) (ArrayTV tv (Dynamic maxn))
      (ArrayV (DynArrayV vs)) initial out scratch /\
    entry_decoder_obs initial out /\ alloca_history fn out
Proof
  qmatch_goalsub_abbrev_tac `LET _ Head` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `Head header` mp_tac >>
  simp_tac bool_ss [Abbr `Head`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all (BETA_RULE (SIMP_RULE (pure_ss ++ boolSimps.LET_ss) []
    entry_nonbulk_loop_config)) >>
  strip_tac >>
  suspend "initialize"
QED
Resume entry_nonbulk_loop_endpoint[initialize]:
  qpat_assum `calldata_member_resource_frame _ _ _ _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE
      [calldata_member_resource_frame_def, calldata_member_wit_def,
       calldata_member_transfers_def]) >>
  `EntryLoopInv ctx fn site first last limit_st ce ty tv vs maxn hdr
    src (n2w sb) dst ip d ix index_st.cs_next_id oid base_addr cap sb bs b reserve_cap
    initial 0 header old` by
    (simp_tac bool_ss [EntryLoopInv_def, EntryLoopHeader_def, EntryLoopOwn_def,
       GSYM calldata_member_own_def] >> asm_rewrite_tac [] >> simp[]) >>
  suspend "child"
QED
Resume entry_nonbulk_loop_endpoint[child]:
  `!bytes v child_src child_dst child_sb addr b reserve_cap oid base_addr cap first last s.
    compile_abi_decode_to_buf child_dst child_src CALLDATALOAD (Lit 0w)
      (type_to_abi_dec_info sf ce ty) first = ((),last) /\
    fn_has_code first last fn /\
    (first.cs_blocks = last.cs_blocks \/
      !bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    last.cs_next_var <= limit_st.cs_next_var /\
    (oid < first.cs_next_id \/ last.cs_next_id <= oid) /\
    base_addr <= addr /\ addr+type_memory_size tv <= base_addr+cap /\
    addr+type_memory_size tv < dimword (:256) /\
    abi_decoder_valid_pre ce env sf ty tv bytes v first child_src child_dst
      CALLDATALOAD (Lit 0w) child_sb addr b reserve_cap s /\
    fresh_vars_wrt limit_st s /\ alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
    calldata_member_own fn first.cs_next_id last.cs_next_id s /\
    FLOOKUP s.vs_allocas oid = SOME (base_addr,cap) /\
    ~s.vs_halted /\ s.vs_current_bb = first.cs_current_bb /\
    s.vs_inst_idx = LENGTH first.cs_current_insts /\ alloca_history fn s ==>
    ?child scratch. calldata_member_success ctx fn site limit_st first last addr
      (type_memory_size tv) tv v s child scratch /\
      entry_decoder_obs s child /\ alloca_history fn child` by
    (qhdtm_x_assum `entry_member_child_contract` mp_tac >>
     qpat_assum `fn_inst_ids_distinct fn` mp_tac >>
     rpt (pop_assum kall_tac) >>
     rewrite_tac[entry_member_child_contract_def] >> metis_tac[]) >>
  suspend "callback"
QED
Resume entry_nonbulk_loop_endpoint[callback]:
  `first.cs_next_id <= ready.cs_next_id /\ st1.cs_next_id <= last.cs_next_id` by
    (qhdtm_assum `EntryLoopConfig` mp_tac >>
     rpt (pop_assum kall_tac) >> rewrite_tac[EntryLoopConfig_def] >>
     rpt strip_tac >> asm_rewrite_tac[]) >>
  Q.SUBGOAL_THEN `oid < ready.cs_next_id \/ st1.cs_next_id <= oid`
    assume_tac >- decide_tac >>
  `!k header entry.
    k < LENGTH vs /\
    abi_decoder_valid_array_entry ce env sf ty tv bs vs k ready ops CALLDATALOAD
      (Lit 0w) sb d b reserve_cap st0.cs_next_var limit_st header entry /\
    ~entry.vs_halted /\ entry.vs_current_bb = ready.cs_current_bb /\
    entry.vs_inst_idx = LENGTH ready.cs_current_insts /\ fresh_vars_wrt limit_st entry /\
    alloca_inv entry /\ alloca_frontier_inv ctx fn site entry /\
    EntryLoopOwn fn ready.cs_next_id st1.cs_next_id entry /\
    FLOOKUP entry.vs_allocas oid = SOME (base_addr,cap) /\
    base_addr <= d+32+k*type_memory_size tv /\
    d+32+k*type_memory_size tv+type_memory_size tv <= base_addr+cap /\
    d+32+k*type_memory_size tv+type_memory_size tv < dimword (:256) /\
    alloca_history fn entry ==>
    ?child new. EntryChildResources ctx fn site ready st1 limit_st tv vs d k entry child new /\
      EntryLoopSafe ctx fn entry child /\ EntryLoopPull ctx fn entry child /\
      entry_decoder_obs entry child /\ alloca_history fn child` by
    (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     Q.SUBGOAL_THEN `ready.cs_blocks = st1.cs_blocks \/
       !bb. lookup_block st1.cs_current_bb fn.fn_blocks = SOME bb ==>
         phi_prefix_length bb.bb_instructions = 0` assume_tac >- simp[] >>
     drule_all entry_valid_array_child_resources >> simp[]) >>
  drule_all entry_joint_initialized_loop_endpoint >> strip_tac >>
  suspend "package"
QED
Resume entry_nonbulk_loop_endpoint[package]:
  qexistsl [`t`,`scratch`] >>
  qpat_x_assum `EntryLoopOwn fn first.cs_next_id last.cs_next_id t` mp_tac >>
  qpat_x_assum `EntryLoopSafe ctx fn initial t` mp_tac >>
  qpat_x_assum `EntryLoopPull ctx fn initial t` mp_tac >>
  rewrite_tac[EntryLoopOwn_def, EntryLoopSafe_def, EntryLoopPull_def] >>
  disch_tac >> disch_tac >> disch_tac >>
  pure_rewrite_tac[calldata_member_success_def, calldata_member_resource_frame_def,
    calldata_member_wit_def, calldata_member_own_def, calldata_member_transfers_def,
    valueEncodingTheory.type_memory_size_def] >>
  asm_rewrite_tac[listTheory.LENGTH]
QED
Finalise entry_nonbulk_loop_endpoint

val () =
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag entry_nonbulk_loop_endpoint)
  in if null axioms andalso null (Thm.hyp entry_nonbulk_loop_endpoint) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then () else raise Fail "entry nonbulk loop endpoint inherited admission"
  end;
