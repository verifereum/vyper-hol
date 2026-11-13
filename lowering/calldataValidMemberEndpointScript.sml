(* Source-valid child windows at supplied actual navigation endpoints. *)
Theory calldataValidMemberEndpoint
Ancestors
  calldataMemberEndpoint calldataValidObservations abiDecoderValidMemberCons
  abiValidMember abiValidDecodedMetadata abiDecoderValidContract
  abiDecoderTypedContract abiDecoderContract abiDecoderMemberSetup
  abiDecoderCoherence abiDecoderReentry abiDecoderArraySetupInputs
  abiDecoderOffset abiDecoderDynamic abiDecoderDynamicLoopSetup
  abiDecoderEmpty abiDecoderComplexHead
  abiEncoder compileEnv venomState venomExecSemantics words list

Theorem member_valid_pre_at_observed_endpoint[local]:
  let at = vyper_to_abi_type env ty;
      ao = SUM (MAP abi_member_head_size pre);
      off = abi_decode_member_offset at bs ao;
      childbs = abi_decode_member_bytes at bs (DROP ao bs) in
  abi_decoder_coherent ce env sf ty tv /\
  vyper_decode_valid_enc_tuple (pre ++ at::ats) bs bs /\
  (is_dynamic at ==> !elem. at <> Array (SOME 0) elem) /\
  abi_to_vyper env ty (dec at childbs) = SOME v /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) (Lit 0w) src dst 0 sb (LENGTH bs) d outsz b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD initial) = bs /\
  vo + type_memory_bytes ce ty <= outsz /\
  abi_decoder_address_frame st.cs_next_var initial endpoint /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  eval_operand ep endpoint = SOME (n2w (sb+off)) /\
  eval_operand dp endpoint = SOME (n2w (d+vo)) /\
  abi_decoder_operand_live ready.cs_next_var ep /\
  abi_decoder_operand_live ready.cs_next_var dp ==>
  abi_decoder_valid_pre ce env sf ty tv childbs v ready ep dp CALLDATALOAD
    (Lit 0w) (Lit 0w) 0 (sb+off) (d+vo) b cap endpoint
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `sb + LENGTH bs < dimword (:256)` by fs[abi_decoder_ranges_def] >>
  drule_all abi_valid_member_window >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all abi_valid_decoded_metadata >> strip_tac >>
  drule_all abi_decoder_valid_member_readable >> strip_tac >>
  `abi_decoder_operand_live st.cs_next_var (Lit 0w)` by
    simp[abi_decoder_operand_live_def] >>
  drule_all abi_valid_member_child_ranges >> strip_tac >>
  drule_all abi_decoder_address_frame_source >>
  disch_then (qspec_then `CALLDATALOAD` assume_tac) >>
  simp[abi_decoder_valid_pre_def, abi_decoder_operand_live_def]
QED

Theorem member_nonempty_offset[local]:
  abi_decoder_coherent ce env sf ty tv /\
  (is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) ==>
  dec_info_needs_offset (type_to_abi_dec_info sf ce ty) =
    is_dynamic (vyper_to_abi_type env ty)
Proof
  strip_tac >> Cases_on `is_dynamic (vyper_to_abi_type env ty)`
  >- (irule abi_decoder_nonempty_type_offset >> metis_tac[]) >>
  drule abi_decoder_coherent_dynamic >> strip_tac >>
  simp[abi_decoder_static_needs_no_offset]
QED

Theorem calldata_valid_member_address_endpoint:
  let at = vyper_to_abi_type env ty;
      ao = SUM (MAP abi_member_head_size pre);
      off = abi_decode_member_offset at bs ao;
      childbs = abi_decode_member_bytes at bs (DROP ao bs) in
  abi_decode_member_setup dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (dec_info_needs_offset (type_to_abi_dec_info sf ce ty)) ao vo st = (ops,ready) /\
  fn_has_code st ready fn /\ abi_decoder_coherent ce env sf ty tv /\
  vyper_decode_valid_enc_tuple (pre ++ at::ats) bs bs /\
  (is_dynamic at ==> !elem. at <> Array (SOME 0) elem) /\
  abi_to_vyper env ty (dec at childbs) = SOME v /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) (Lit 0w) src dst 0 sb (LENGTH bs) d outsz b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD initial) = bs /\
  vo + type_memory_bytes ce ty <= outsz /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  ready.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?endpoint.
    abi_decoder_valid_pre ce env sf ty tv childbs v ready (FST ops) (SND ops)
      CALLDATALOAD (Lit 0w) (Lit 0w) 0 (sb+off) (d+vo) b cap endpoint /\
    ~endpoint.vs_halted /\ endpoint.vs_current_bb = ready.cs_current_bb /\
    endpoint.vs_inst_idx = LENGTH ready.cs_current_insts /\
    eval_operand (SND ops) endpoint = SOME (n2w (d+vo)) /\
    eval_operand (FST ops) endpoint = SOME (n2w (sb+off)) /\
    fresh_vars_wrt limit_st endpoint /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op endpoint = eval_operand op initial) /\
    endpoint.vs_memory = initial.vs_memory /\
    endpoint.vs_call_ctx = initial.vs_call_ctx /\
    endpoint.vs_data_section = initial.vs_data_section /\
    endpoint.vs_allocas = initial.vs_allocas /\
    endpoint.vs_alloca_next = initial.vs_alloca_next /\
    ((!fuel. mem_safe_run fuel ctx fn endpoint) ==> !fuel. mem_safe_run fuel ctx fn initial) /\
    (!fuel r. run_from fuel ctx fn endpoint = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn endpoint ==> mem_safe_run fuel' ctx fn initial))
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all member_nonempty_offset >> disch_tac >>
  `eval_operand src initial = SOME (n2w sb) /\
   eval_operand dst initial = SOME (n2w d) /\ sb+LENGTH bs < dimword (:256)` by
    fs[abi_decoder_ranges_def] >>
  drule_all abi_valid_member_window >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  PairCases_on `ops` >>
  qpat_x_assum `abi_decode_member_setup _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [abi_decode_member_setup_def] >> disch_tac >>
  drule_all calldata_member_address_endpoint >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  suspend "observations"
QED

Resume calldata_valid_member_address_endpoint[observations]:
  `eval_operand ops0 endpoint = SOME (n2w
    (sb + abi_decode_member_offset (vyper_to_abi_type env ty) bs
      (SUM (MAP abi_member_head_size pre))))` by
    (Cases_on `is_dynamic (vyper_to_abi_type env ty)` >>
     gvs[abi_decode_member_offset_def, word_add_n2w,
       Excl "vyper_decode_valid_enc_def", Excl "dec_def"]) >>
  `abi_decoder_address_frame st.cs_next_var initial endpoint` by
    (simp[abi_decoder_address_frame_def] >> metis_tac[]) >>
  `abi_decoder_valid_pre ce env sf ty tv
    (abi_decode_member_bytes (vyper_to_abi_type env ty) bs
      (DROP (SUM (MAP abi_member_head_size pre)) bs)) v ready ops0 ops1
    CALLDATALOAD (Lit 0w) (Lit 0w)
    0 (sb + abi_decode_member_offset (vyper_to_abi_type env ty) bs
      (SUM (MAP abi_member_head_size pre))) (d+vo) b cap endpoint` by
    (irule (SIMP_RULE bool_ss [LET_THM] member_valid_pre_at_observed_endpoint) >>
     goal_assum (drule_at Any) >> simp[word_add_n2w] >>
     metis_tac[]) >>
  qexists_tac `endpoint` >> simp[word_add_n2w, dec_info_needs_offset_def]
QED
Finalise calldata_valid_member_address_endpoint

(* With the actual calldata hi operand, the empty guard emits no instructions.
   This path therefore requires no payload offset and no payload window. *)
Theorem calldata_empty_member_endpoint:
  abi_decode_member_setup dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (dec_info_needs_offset (type_to_abi_dec_info sf ce ty)) ao vo st = (ops,middle) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty) middle = ((),last) /\
  fn_has_code st last fn /\ abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecComplex T [] /\
  abi_to_vyper env ty (dec (vyper_to_abi_type env ty) childbs) = SOME v /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  last.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?endpoint.
    val_in_memory tv v (d+vo) endpoint.vs_memory /\
    ~endpoint.vs_halted /\ endpoint.vs_current_bb = last.cs_current_bb /\
    endpoint.vs_inst_idx = LENGTH last.cs_current_insts /\
    eval_operand (SND ops) endpoint = SOME (n2w (d+vo)) /\
    eval_operand (FST ops) endpoint = SOME (n2w (sb+ao)) /\
    abi_decoder_operand_live last.cs_next_var (FST ops) /\
    abi_decoder_operand_live last.cs_next_var (SND ops) /\
    fresh_vars_wrt limit_st endpoint /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op endpoint = eval_operand op initial) /\
    endpoint.vs_memory = initial.vs_memory /\
    endpoint.vs_call_ctx = initial.vs_call_ctx /\
    endpoint.vs_data_section = initial.vs_data_section /\
    endpoint.vs_allocas = initial.vs_allocas /\
    endpoint.vs_alloca_next = initial.vs_alloca_next /\
    ((!fuel. mem_safe_run fuel ctx fn endpoint) ==> !fuel. mem_safe_run fuel ctx fn initial) /\
    (!fuel r. run_from fuel ctx fn endpoint = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn endpoint ==> mem_safe_run fuel' ctx fn initial))
Proof
  strip_tac >>
  `last = middle` by
    (qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
     simp[abi_decode_empty_complex_phases, abi_decode_complex_head_guard_def,
       comp_return_def]) >>
  drule_all abi_decoder_empty_descriptor_value >> strip_tac >>
  PairCases_on `ops` >>
  qpat_x_assum `abi_decode_member_setup _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [abi_decode_member_setup_def, dec_info_needs_offset_def] >> disch_tac >>
  gvs[] >> drule_all calldata_member_address_endpoint >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `endpoint` >> simp[word_add_n2w, dec_info_needs_offset_def]
QED
