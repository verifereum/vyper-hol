(* Source-member composition at a single framed recursive child endpoint. *)
Theory entrySourceMemberChild
Ancestors
  entrySourceMemberNavigation entryDecoderMemberEndpoint entryDecoderStateFrame
  calldataSourceMemberFold calldataMemberResourceFrame calldataSafeIteration
  abiDecoderMemberSetup abiDecoderMemberCode abiDecoderOffsetHead fragExec
  abiDecoderCode abiDecoderCounters abiDecoderAppend
  abiDecoderCoherence abiDecoderTypedContract abiDecoderContract abiDecoderReentry
  abiDecoderValidMemberCons abiEncoder compileEnv exprLoweringProps
  venomState venomExecSemantics words list arithmetic

Theorem entry_source_member_success:
  let at = vyper_to_abi_type env ty;
      ao = SUM (MAP abi_member_head_size pre);
      childbs = abi_decode_member_bytes at bs (DROP ao bs) in
  abi_decode_member_setup dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (dec_info_needs_offset (type_to_abi_dec_info sf ce ty)) ao vo st = (ops,ready) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty) ready = ((),last) /\
  fn_has_code st last fn /\
  (ready.cs_blocks = last.cs_blocks \/
    !bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_coherent ce env sf ty tv /\
  vyper_decode_valid_enc_tuple (pre ++ at::ats) bs bs /\
  abi_to_vyper env ty (dec at childbs) = SOME v /\ val_wf tv v /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) (Lit 0w) src dst 0 sb (LENGTH bs) d outsz b reserve_cap s /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD s) = bs /\
  vo + type_memory_bytes ce ty <= outsz /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  last.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
  calldata_member_own fn st.cs_next_id last.cs_next_id s /\
  FLOOKUP s.vs_allocas oid = SOME (base_addr,cap) /\
  (oid < ready.cs_next_id \/ last.cs_next_id <= oid) /\
  base_addr <= d+vo /\ d+vo+type_memory_size tv <= base_addr+cap /\
  d+vo+type_memory_size tv < dimword (:256) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  entry_member_child_contract ce env sf ctx fn site limit_st ty tv /\
  fn_inst_ids_distinct fn /\ alloca_history fn s ==>
  ?t scratch. calldata_member_success ctx fn site limit_st st last (d+vo)
    (type_memory_size tv) tv v s t scratch /\
    entry_decoder_obs s t /\ alloca_history fn t
Proof
  pure_rewrite_tac[LET_THM] >> CONV_TAC (REDEPTH_CONV BETA_CONV) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_member_setup_shape >> strip_tac >>
  drule abi_decode_member_setup_counters >> strip_tac >>
  drule cs_extends_abi_decode >> strip_tac >>
  drule_all abi_decoder_to_buf_code >> strip_tac >>
  drule abi_decoder_variable_counter >> strip_tac >>
  `cs_extends st ready` by (irule cs_extends_same_block >> simp[]) >>
  `st.cs_next_id <= ready.cs_next_id /\ ready.cs_next_id <= last.cs_next_id /\
   st.cs_next_var <= ready.cs_next_var /\ ready.cs_next_var <= limit_st.cs_next_var` by
    (Cases_on `dec_info_needs_offset (type_to_abi_dec_info sf ce ty)` >>
     fs[abi_decoder_code_def]) >>
  drule_all fn_has_code_split >> strip_tac >>
  Cases_on `type_to_abi_dec_info sf ce ty = DecComplex T []`
  >- suspend "empty" >>
  `(is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem)` by
    (strip_tac >> drule_all abi_decoder_nonempty_readable_head >> simp[]) >>
  drule_all (SIMP_RULE bool_ss [LET_THM] entry_source_member_navigation) >>
  strip_tac >> suspend "child"
QED

Resume entry_source_member_success[empty]:
  `eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d)` by
    fs[abi_decoder_ranges_def] >>
  drule_all entry_source_empty_member_resources >> strip_tac >>
  qexistsl_tac [`t`,`[]`] >>
  simp[calldata_member_success_def, calldata_member_transfers_def]
QED

Resume entry_source_member_success[child]:
  qhdtm_x_assum `abi_decode_member_setup` kall_tac >>
  qhdtm_x_assum `abi_decoder_coherent` kall_tac >>
  qhdtm_x_assum `vyper_decode_valid_enc_tuple` kall_tac >>
  qhdtm_x_assum `abi_to_vyper` kall_tac >>
  qhdtm_x_assum `abi_decoder_ranges` kall_tac >>
  qhdtm_x_assum `mem_bytes_at` kall_tac >>
  rename1 `calldata_member_resource_frame _ _ _ _ _ _ _ _ _ s u []` >>
  drule calldata_member_resource_endpoint >> strip_tac >>
  drule calldata_member_resource_observations >> strip_tac >>
  `calldata_member_own fn ready.cs_next_id last.cs_next_id u` by
    (irule calldata_member_own_nested >> goal_assum (drule_at Any) >> simp[]) >>
  `FLOOKUP u.vs_allocas oid = SOME (base_addr,cap)` by metis_tac[] >>
  drule_all entry_member_child_contract_apply >> strip_tac >>
  drule calldata_member_success_observations >> strip_tac >>
  `calldata_member_resource_frame ctx fn site limit_st st.cs_next_id last.cs_next_id
    st.cs_next_var (d+vo) (type_memory_size tv) s t ([] ++ scratch)` by
    (irule calldata_member_resource_extend >>
     qpat_assum `calldata_member_resource_frame _ _ _ _ _ _ _ _ _ s u []` (irule_at Any) >>
     qpat_assum `calldata_member_resource_frame _ _ _ _ _ _ _ _ _ u t scratch` (irule_at Any) >>
     simp[]) >>
  `entry_decoder_obs s t` by metis_tac[entry_decoder_obs_trans] >>
  qhdtm_x_assum `calldata_member_transfers`
    (strip_assume_tac o REWRITE_RULE [calldata_member_transfers_def]) >>
  qexistsl_tac [`t`,`scratch`] >>
  gnvs[calldata_member_success_def, calldata_member_transfers_def, APPEND] >>
  qpat_x_assum `!fuel. (!e. run_from fuel ctx fn u <> Error e) ==> _` mp_tac >>
  qpat_x_assum `!fuel. (!e. run_from fuel ctx fn t <> Error e) ==> _` mp_tac >>
  rpt (pop_assum kall_tac) >> metis_tac[calldata_safe_transfer_trans]
QED
Finalise entry_source_member_success

val () =
  List.app (fn th =>
    let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
    in if null axioms andalso null (Thm.hyp th) andalso
          List.all (fn name => name = "DISK_THM") oracles
       then () else raise Fail "entry source member child inherited admission"
    end) [entry_source_member_success];
