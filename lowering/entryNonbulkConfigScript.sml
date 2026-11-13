(* Compile-time boundary for the joint nonbulk entry decoder loop. *)
Theory entryNonbulkConfig
Ancestors
  entryDecoderJointLoop calldataCoherentOwnedEndpoint
  calldataArrayCompileBoundary calldataValidArrayInputs calldataMemberResourceFrame
  abiDecoderRecursiveLoopLayout abiDecoderArrayLoopInit abiDecoderIndexInit
  abiDecoderLoopCode abiDecoderLoopRegisters abiDecoderContract abiDecoderCoherence
  abiDecoderArrayInit abiDecoderArrayInitReentry abiDecoderValidContract
  abiDecoderTypedContract abiEncoder exprLoweringProps compileEnv vyperABI
  venomState venomExecSemantics venomMemDefs abiDecoderReentry
  abiDecoderArrayBackedge abiDecoderExecution list arithmetic

Theorem entry_nonbulk_loop_config:
  let Head = \u.
    ~u.vs_halted /\ u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 /\
    LENGTH vs <= maxn /\
    eval_operand src u = SOME (n2w sb) /\ eval_operand dst u = SOME (n2w d) /\
    eval_operand ip u = SOME (n2w ix) /\ mload ix u = 0w /\
    abi_decode_load CALLDATALOAD (n2w sb : bytes32) u = n2w (LENGTH vs) /\
    mem_word_at d u.vs_memory = n2w (LENGTH vs) /\
    FLOOKUP u.vs_allocas index_st.cs_next_id = SOME (ix,32) /\
    FLOOKUP u.vs_allocas oid = SOME (base_addr,cap) /\ MEM (ix,32) old /\
    abi_decoder_ranges CALLDATALOAD (Lit 0w) (Lit 0w) src dst 0 sb (LENGTH bs)
      d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b reserve_cap u /\
    mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD u) = bs
  in
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) (Lit 0w) maxn
    (abi_embedded_static_size ce.ce_struct_fields ty) first = ((ip,cnt),loop_st) /\
  abi_decode_index_init index_st = (ip,loop_st) /\
  abi_decode_loop_prefix ip src CALLDATALOAD (Lit 0w) loop_st = ((hdr,body_lbl,exit_lbl),st0) /\
  compile_abi_decode_dyn_loop dst src CALLDATALOAD (Lit 0w) (Lit 0w)
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
    bs (ArrayV (DynArrayV vs)) first src dst CALLDATALOAD (Lit 0w) (Lit 0w) 0 sb d b reserve_cap initial /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  (is_abi_dynamic ce.ce_struct_fields ty \/
    dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)) /\
  Head header /\
  calldata_member_resource_frame ctx fn site limit_st first.cs_next_id last.cs_next_id
    first.cs_next_var d (32+maxn*type_memory_size tv) initial header old ==>
  ?ready st1 ops di hid body_bb next nvar biv exit_bb.
    EntryLoopConfig fn first st0 ready st1 last limit_st ce env sf ty tv vs maxn
      hdr hid body_lbl body_bb exit_lbl next nvar biv ip src dst ops di bs ix d
      index_st.cs_next_id oid base_addr cap /\
    compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) CALLDATALOAD (Lit 0w) (Lit 0w)
      (type_to_abi_dec_info sf ce ty) ready = ((),st1) /\
    fn_has_code ready st1 fn /\
    (!bb. lookup_block st1.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
    st1.cs_next_var <= limit_st.cs_next_var /\
    type_memory_bytes ce ty = type_memory_size tv /\
    lookup_block exit_lbl fn.fn_blocks = SOME exit_bb /\
    phi_prefix_length exit_bb.bb_instructions = 0 /\
    last.cs_current_bb = exit_lbl /\ last.cs_current_insts = []
Proof
  qmatch_goalsub_abbrev_tac `LET _ Head` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all calldata_array_compile_boundary >> strip_tac >>
  gnvs[Excl "enc_def", Excl "dec_def", Excl "valid_enc_def"] >>
  qpat_x_assum `(_ /\ _) /\ _` (map_every assume_tac o CONJUNCTS) >>
  gnvs[Excl "enc_def", Excl "dec_def", Excl "valid_enc_def"] >>
  drule abi_decoder_loop_suffix_facts >> strip_tac >>
  qpat_x_assum `last.cs_next_id = _` kall_tac >>
  qpat_x_assum `last.cs_next_var = _` kall_tac >>
  gnvs[Excl "enc_def", Excl "dec_def", Excl "valid_enc_def"] >>
  suspend "prepare"
QED

Resume entry_nonbulk_loop_config[prepare]:
  qpat_x_assum `Head header` mp_tac >>
  simp[Abbr `Head`] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `calldata_member_resource_frame _ _ _ _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE
      [calldata_member_resource_frame_def, calldata_member_wit_def]) >>
  qpat_assum `abi_decoder_valid_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_valid_pre_def]) >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule calldata_valid_array_inputs >> strip_tac >>
  drule_all abi_decode_array_loop_init_shape >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  drule abi_decode_array_loop_index_live >> simp_tac bool_ss [pairTheory.FST] >> strip_tac >>
  suspend "config"
QED

Resume entry_nonbulk_loop_config[config]:
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
  suspend "package"
QED
Resume entry_nonbulk_loop_config[package]:
  qpat_x_assum `abi_decode_loop_cfg _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_decode_loop_cfg_def]) >>
  qpat_assum `lookup_block st0.cs_current_bb _ = SOME _` (fn th =>
    rename1 `lookup_block st0.cs_current_bb fn.fn_blocks = SOME body_block`) >>
  qexistsl [`ready`, `st1`, `ops`,
    `type_to_abi_dec_info ce.ce_struct_fields ce (ArrayT ty (Dynamic maxn))`,
    `loop_st.cs_next_id+1`,
    `body_block`, `loop_st.cs_next_var`, `st1.cs_next_var`,
    `STRING #"%" (toString (loop_st.cs_next_var+4))`] >>
  simp_tac bool_ss [EntryLoopConfig_def] >>
  qpat_assum `vyper_decode_valid_enc _ _`
    (assume_tac o PURE_REWRITE_RULE [Once vyper_to_abi_type_def]) >>
  qpat_assum `abi_decoder_metadata _ _ _ _ _ _ _`
    (assume_tac o PURE_REWRITE_RULE [Once vyper_to_abi_type_def]) >>
  qpat_x_assum `loop_st.cs_next_var = index_st.cs_next_var + 1`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM th]) >>
      rewrite_tac [GSYM th]) >>
  qpat_assum `type_memory_size tv = type_memory_bytes ce ty`
    (fn th => rewrite_tac [GSYM th]) >>
  asm_rewrite_tac [] >> simp[] >>
  suspend "admissible"
QED
Resume entry_nonbulk_loop_config[admissible]:
  gnvs[Excl "enc_def", Excl "dec_def", Excl "valid_enc_def"] >>
  Cases_on `is_abi_dynamic ce.ce_struct_fields ty`
  >- (drule_all calldata_dynamic_array_child_admissible >> simp[]) >>
  qpat_x_assum `is_abi_dynamic _ _ \/ dec_info_needs_clamp _` mp_tac >>
  asm_rewrite_tac[] >> disch_tac >>
  drule_all calldata_static_clamped_child_exclusion >> simp[]
QED
Finalise entry_nonbulk_loop_config

val () =
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag entry_nonbulk_loop_config)
  in if null axioms andalso null (Thm.hyp entry_nonbulk_loop_config) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then () else raise Fail "entry nonbulk config inherited admission"
  end;
