(* Live member navigation indexed by the actual descending descriptor map. *)
Theory entryReachBodyDescendingMemberEntry
Ancestors
  entryReachBodyDescendingMetadata entryReachBodyMemberSetup
  abiDecoderMemberBody abiDecoderOffset abiDecoderArraySetupInputs
  abiDecoderMembers abiDecoderMemberSlice entryReachBodyOwnedRegion
  entryReachBodyScratchSet abiAllocationHistory allocaFrontierBound
  abiEncoder abiDecoderContract entryReachBodyExactArrayLoop
  entryReachBodyOperationalPath exprLoweringProps compileEnv
  contractABI valueEncoding venomState words list rich_list arithmetic

Theorem entry_descending_member_owned_entry:
  !ats vals off ao vo outsz ei.
  entry_descending_members ce env sf pretys pretvs preavs prevs /\
  entry_descending_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) /\
  ats = MAP (vyper_to_abi_type env) (pretys ++ ty::tys) /\ vals = preavs ++ av::avs /\
  off = abi_tuple_child_offset ats vals (LENGTH pretys) /\
  ao = SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys)) /\
  vo = SUM (MAP (type_memory_bytes ce) pretys) /\
  outsz = SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys)) /\
  ei = type_to_abi_dec_info sf ce ty /\
  dec_info_needs_offset ei = is_dynamic (vyper_to_abi_type env ty) /\
  mem_bytes_at sb (LENGTH (enc (Tuple ats) (ListV vals)))
    (abi_decode_source CALLDATALOAD s) = enc (Tuple ats) (ListV vals) /\
  sb + LENGTH (enc (Tuple ats) (ListV vals)) < dimword (:256) /\
  d + outsz < dimword (:256) /\ entry_owned_region oid root extent d outsz s /\
  entry_scratch_ready sites b cap s /\ alloca_inv s /\
  abi_alloca_history (fn_insts fn) s /\ alloca_frontier_inv ctx fn site s /\
  abi_decode_member_setup dst src CALLDATALOAD (Lit 0w) (dec_info_needs_offset ei) ao vo st = (ops,mid) /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  mid.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st mid fn /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?u. entry_decode_path ctx fn s u /\ entry_loop_fields s u /\
    abi_decoder_address_frame st.cs_next_var s u /\ fresh_vars_wrt limit_st u /\
    eval_operand (FST ops) u = SOME (n2w (sb+off)) /\
    eval_operand (SND ops) u = SOME (n2w (d+vo)) /\
    abi_decoder_operand_live mid.cs_next_var (FST ops) /\
    abi_decoder_operand_live mid.cs_next_var (SND ops) /\
    u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
    u.vs_alloca_next = s.vs_alloca_next /\ ~u.vs_halted /\
    u.vs_current_bb = mid.cs_current_bb /\ u.vs_inst_idx = LENGTH mid.cs_current_insts /\
    mem_bytes_at (sb+off) (LENGTH (enc (vyper_to_abi_type env ty) av))
      (abi_decode_source CALLDATALOAD u) = enc (vyper_to_abi_type env ty) av /\
    sb+off+LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
    d+vo+type_memory_size tv < dimword (:256) /\
    abi_decoder_coherent ce env sf ty tv /\
    entry_descending_metadata ce env sf ty tv ei av v /\
    entry_owned_region oid root extent (d+vo) (type_memory_size tv) u /\
    entry_scratch_ready sites b cap u /\ alloca_inv u /\
    abi_alloca_history (fn_insts fn) u /\ alloca_frontier_inv ctx fn site u
Proof
  rpt gen_tac >> rewrite_tac[entry_descending_members_equiv] >> strip_tac >>
  mp_tac abi_decoder_members_child_facts >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  `mem_bytes_at (sb+off) (LENGTH (enc (vyper_to_abi_type env ty) av))
     (abi_decode_source CALLDATALOAD s) = enc (vyper_to_abi_type env ty) av /\
   off + LENGTH (enc (vyper_to_abi_type env ty) av) <= LENGTH (enc (Tuple ats) (ListV vals)) /\
   vo + type_memory_size tv <= outsz` by
    (mp_tac (Q.INST [`opc` |-> `CALLDATALOAD`] abi_decoder_member_source) >>
     (impl_tac >- gvs[Excl "enc_def"]) >> asm_rewrite_tac[]) >>
  mp_tac (Q.INST [`pre` |-> `MAP (vyper_to_abi_type env) pretys`,
    `aty` |-> `vyper_to_abi_type env ty`, `post` |-> `MAP (vyper_to_abi_type env) tys`,
    `pvs` |-> `preavs`, `opc` |-> `CALLDATALOAD`] abi_decoder_canonical_member_inputs) >>
  (impl_tac >- (gvs[MAP_APPEND, Excl "enc_def"] >>
    rule_assum_tac (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >> asm_rewrite_tac[])) >> strip_tac >>
  rule_assum_tac (PURE_REWRITE_RULE [LENGTH_MAP]) >>
  qpat_x_assum `dec_info_needs_offset ei = _` SUBST_ALL_TAC >>
  qpat_x_assum `ao = _` SUBST_ALL_TAC >>
  drule_all entry_member_setup_endpoint >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `entry_scratch_ready sites b cap u /\
   entry_owned_region oid root extent d outsz u /\ alloca_inv u /\
   abi_alloca_history (fn_insts fn) u /\ alloca_frontier_inv ctx fn site u` by
    (irule entry_member_resource_frame >> qexists_tac `s` >> simp[]) >>
  `abi_decode_source CALLDATALOAD u = abi_decode_source CALLDATALOAD s` by
    (irule abi_decoder_address_frame_source >> goal_assum (drule_at Any)) >>
  `eval_operand (FST ops) u = SOME (n2w (sb+off))` by
    (qpat_x_assum `LENGTH pretys = LENGTH preavs` kall_tac >>
     qpat_x_assum `eval_operand (FST ops) u = _` mp_tac >>
     simp[MAP_APPEND, ADD_COMM, Excl "enc_def"]) >>
  `sb+off+LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
   d+vo+type_memory_size tv < dimword (:256)` by decide_tac >>
  `entry_owned_region oid root extent (d+vo) (type_memory_size tv) u` by
    (qpat_x_assum `entry_owned_region oid root extent d outsz u` mp_tac >>
     simp_tac bool_ss [entry_owned_region_def] >> strip_tac >>
     asm_rewrite_tac[] >> decide_tac) >>
  `entry_descending_metadata ce env sf ty tv ei av v` by
    gvs[entry_descending_metadata_transport] >>
  qexists_tac `u` >> asm_rewrite_tac[] >>
  qpat_x_assum `mem_bytes_at (sb+off) _ _ = _` mp_tac >> asm_rewrite_tac[]
QED
