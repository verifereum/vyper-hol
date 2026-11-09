(* Actual tuple member windows establish allocation-free scalar inputs. *)
Theory abiDecodePtrPhysicalMemberRun
Ancestors
  abiDecodePtrPhysicalScalarRun abiValidMember abiValidDecodedMetadata
  abiDecoderValidMemberCons abiDecoderCoherence abiDecoderDynamic
  abiDecoderMemberSetup abiDecoderDynamicLoopSetup abiDecoderReentry
  abiDecodeRanges abiDecoderContract abiDecoderTypedContract abiCanonicalHeadSize abiValidMembers
  abiDecoderClampedWord abiDecoderBytesPhases abiDecoderTypedCompose
  abiDecoderOffset abiDecoderFrameCompose abiDecoderRange emitHelperProps
  supportedTypes exprLowering abiEncoder compileEnv valueEncoding vyperABI contractABI
  venomState words list arithmetic

Theorem abi_decode_supported_source_shape[local]:
  supported_scalar_type ty ==>
  abi_member_head_size (vyper_to_abi_type env ty) = 32 /\
  (!elem. vyper_to_abi_type env ty <> Array (SOME 0) elem)
Proof
  Cases_on `ty` >> fs[supported_scalar_type_def, supported_word_type_def,
    supported_string_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  fs[supported_word_type_def, supported_string_type_def,
    vyper_to_abi_type_def, vyper_base_to_abi_type_def, abi_member_head_size_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  fs[supported_word_type_def, supported_string_type_def,
    vyper_to_abi_type_def, vyper_base_to_abi_type_def, abi_member_head_size_def]
QED

Theorem abi_decode_physical_member_input:
  let at = vyper_to_abi_type env ty;
      ao = SUM (MAP abi_member_head_size pre);
      off = abi_decode_member_offset at bs ao;
      childbs = abi_decode_member_bytes at bs (DROP ao bs) in
  supported_scalar_type ty /\ abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
  vyper_decode_valid_enc_tuple (pre ++ at::ats) bs bs /\
  abi_to_vyper env ty (dec at childbs) = SOME v /\
  mem_bytes_at (B + z) (LENGTH bs) (abi_decode_source MLOAD s) = bs /\
  B + z + LENGTH bs < dimword(:256) /\
  d + q + type_memory_bytes ce ty < dimword(:256) /\
  (B + z + LENGTH bs <= d + q \/ d + q + type_memory_bytes ce ty <= B + z) /\
  eval_operand base_op s = SOME (n2w B) /\
  eval_operand childsrc s = SOME (n2w (z + off)) /\
  eval_operand childdst s = SOME (n2w (d + q)) /\ fresh_vars_wrt st s /\
  (hi = Lit 0w \/ ?h. eval_operand hi s = SOME (n2w h) /\
    z + LENGTH bs <= h /\ h < dimword(:256)) ==>
  abi_decode_physical_scalar_pre ce env ce.ce_struct_fields ty tv childbs v
    st childsrc childdst base_op hi B (z + off) (d + q) s
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decode_supported_source_shape >> disch_then (qspec_then `env` strip_assume_tac) >>
  drule abi_valid_member_window >>
  disch_then (qspecl_then [`B + z`, `s`, `MLOAD`] mp_tac) >>
  asm_simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule abi_decoder_valid_member_readable >>
  asm_simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all abi_valid_decoded_metadata >> strip_tac >>
  asm_simp_tac bool_ss [abi_decode_physical_scalar_pre_def, ADD_ASSOC] >>
  rpt conj_tac
  >- decide_tac
  >- decide_tac >>
  Cases_on `hi = Lit 0w` >> simp[] >>
  qpat_x_assum `hi = Lit 0w \/ _` mp_tac >> simp[] >> strip_tac >>
  qexists_tac `h` >> simp[] >> decide_tac
QED

Theorem abi_decode_physical_member_setup:
  let at = vyper_to_abi_type env ty;
      ao = SUM (MAP abi_member_head_size pre);
      off = abi_decode_member_offset at bs ao;
      childbs = abi_decode_member_bytes at bs (DROP ao bs) in
  abi_decode_member_setup dst src MLOAD base_op hi
    (abi_decoder_dynamic (type_to_abi_dec_info ce.ce_struct_fields ce ty)) ao q st = (ops,ready) /\
  supported_scalar_type ty /\ abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
  vyper_decode_valid_enc_tuple (pre ++ at::ats) bs bs /\
  abi_to_vyper env ty (dec at childbs) = SOME v /\
  mem_bytes_at (B + z) (LENGTH bs) (abi_decode_source MLOAD s) = bs /\
  B + z + LENGTH bs < dimword(:256) /\
  d + q + type_memory_bytes ce ty < dimword(:256) /\
  (B + z + LENGTH bs <= d + q \/ d + q + type_memory_bytes ce ty <= B + z) /\
  eval_operand base_op s = SOME (n2w B) /\
  eval_operand src s = SOME (n2w z) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var base_op /\
  abi_decoder_operand_live st.cs_next_var hi /\ fresh_vars_wrt ready s /\
  (hi = Lit 0w \/ ?h. eval_operand hi s = SOME (n2w h) /\
    z + LENGTH bs <= h /\ h < dimword(:256)) ==>
  ?prepared. run_inst_seq (emitted_insts st ready) s = OK prepared /\
    inst_extends st ready /\ abi_decoder_address_frame st.cs_next_var s prepared /\
    abi_decode_physical_scalar_pre ce env ce.ce_struct_fields ty tv childbs v
      ready (FST ops) (SND ops) base_op hi B (z + off) (d + q) prepared
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decode_supported_source_shape >> disch_then (qspec_then `env` strip_assume_tac) >>
  drule abi_decoder_coherent_dynamic >> strip_tac >>
  drule abi_valid_member_window >>
  disch_then (qspecl_then [`B + z`, `s`, `MLOAD`] mp_tac) >>
  asm_simp_tac bool_ss [LET_THM] >> strip_tac >>
  qpat_x_assum `abi_decode_member_setup _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  qmatch_goalsub_abbrev_tac `z + off` >>
  `is_dynamic (vyper_to_abi_type env ty) ==>
    eval_operand base_op s = SOME (n2w B) /\
    abi_decode_load MLOAD (n2w (B + (z + SUM (MAP abi_member_head_size pre))) : bytes32) s = n2w off /\
    z + off < dimword(:256)` by (strip_tac >> asm_simp_tac bool_ss [ADD_ASSOC] >>
      decide_tac) >>
  `abi_decode_source_opcode MLOAD /\ ready.cs_next_var <= ready.cs_next_var` by
    simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_member_setup_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st ready) s = OK prepared` >>
  `eval_operand (FST ops) prepared = SOME (n2w (z + off))` by
    (Cases_on `is_dynamic (vyper_to_abi_type env ty)` >>
     gvs[Abbr `off`, abi_decode_member_offset_def,
       Excl "vyper_decode_valid_enc_def", Excl "dec_def"]) >>
  `eval_operand base_op prepared = SOME (n2w B)` by
    metis_tac[abi_decoder_address_frame_def] >>
  `hi = Lit 0w \/ ?h. eval_operand hi prepared = SOME (n2w h) /\
     z + LENGTH bs <= h /\ h < dimword(:256)` by
    metis_tac[abi_decoder_address_frame_guard] >>
  `mem_bytes_at (B + z) (LENGTH bs) (abi_decode_source MLOAD prepared) = bs` by
    fs[abi_decoder_address_frame_def, abi_decode_source_def] >>
  qexists_tac `prepared` >> asm_simp_tac bool_ss [] >>
  simp_tac bool_ss [Abbr `off`] >>
  irule (SIMP_RULE bool_ss [LET_THM] abi_decode_physical_member_input) >>
  metis_tac[]
QED

Theorem abi_decode_physical_scalar_shape:
  supported_scalar_type ty /\
  compile_abi_decode_to_buf dst src MLOAD base_op hi
    (type_to_abi_dec_info sf ce ty) st = ((),last) ==>
  inst_extends st last /\
  dec_info_needs_offset (type_to_abi_dec_info sf ce ty) =
    abi_decoder_dynamic (type_to_abi_dec_info sf ce ty)
Proof
  strip_tac >>
  `(?clamp. type_to_abi_dec_info sf ce ty = DecPrimWord clamp) \/
   (?n. type_to_abi_dec_info sf ce ty = DecBytestring n)` by
    (Cases_on `ty` >> fs[supported_scalar_type_def, supported_word_type_def,
       supported_string_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     fs[supported_word_type_def, supported_string_type_def, type_to_abi_dec_info_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     fs[supported_word_type_def, supported_string_type_def, type_to_abi_dec_info_def])
  >- (gvs[] >> `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
      drule_all abi_decoder_clamped_word_shape >> strip_tac >>
      simp[dec_info_needs_offset_def, abi_decoder_dynamic_def] >>
      irule abi_decoder_inst_extends_prefix >> simp[]) >>
  gvs[] >> `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_bytes_position_shape >> strip_tac >>
  simp[dec_info_needs_offset_def, abi_decoder_dynamic_def]
QED

Theorem abi_decode_physical_member_sequence:
  let at = vyper_to_abi_type env ty;
      ao = SUM (MAP abi_member_head_size pre);
      childbs = abi_decode_member_bytes at bs (DROP ao bs) in
  abi_decode_member_setup dst src MLOAD base_op hi
    (abi_decoder_dynamic (type_to_abi_dec_info ce.ce_struct_fields ce ty)) ao q st = (ops,ready) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) MLOAD base_op hi
    (type_to_abi_dec_info ce.ce_struct_fields ce ty) ready = ((),last) /\
  supported_scalar_type ty /\ abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
  vyper_decode_valid_enc_tuple (pre ++ at::ats) bs bs /\
  abi_to_vyper env ty (dec at childbs) = SOME v /\
  mem_bytes_at (B + z) (LENGTH bs) (abi_decode_source MLOAD s) = bs /\
  B + z + LENGTH bs < dimword(:256) /\
  d + q + type_memory_bytes ce ty < dimword(:256) /\
  (B + z + LENGTH bs <= d + q \/ d + q + type_memory_bytes ce ty <= B + z) /\
  eval_operand base_op s = SOME (n2w B) /\
  eval_operand src s = SOME (n2w z) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var base_op /\
  abi_decoder_operand_live st.cs_next_var hi /\ fresh_vars_wrt st s /\
  (hi = Lit 0w \/ ?h. eval_operand hi s = SOME (n2w h) /\
    z + LENGTH bs <= h /\ h < dimword(:256)) ==>
  ?t. run_inst_seq (emitted_insts st last) s = OK t /\ inst_extends st last /\
    val_in_memory tv v (d + q) t.vs_memory /\
    abi_decode_frame (d + q) (type_memory_bytes ce ty) s t /\ fresh_vars_wrt last t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    mem_bytes_at (B + z) (LENGTH bs) (abi_decode_source MLOAD t) = bs /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w)
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decode_member_setup_counters >> strip_tac >>
  `fresh_vars_wrt ready s` by
    (irule fresh_vars_wrt_mono >> qexists_tac `st` >> simp[GREATER_EQ]) >>
  drule_all (SIMP_RULE bool_ss [LET_THM] abi_decode_physical_member_setup) >> strip_tac >>
  drule_all abi_decode_physical_scalar_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts ready last) prepared = OK t` >>
  drule_all abi_decode_physical_scalar_shape >> strip_tac >>
  `run_inst_seq (emitted_insts st last) s = OK t /\ inst_extends st last` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`prepared`, `ready`] >> simp[]) >>
  `abi_decode_frame (d + q) (type_memory_bytes ce ty) s t` by
    (fs[abi_decode_frame_def, abi_decoder_address_frame_def] >> metis_tac[]) >>
  `mem_bytes_at (B + z) (LENGTH bs) (abi_decode_source MLOAD t) = bs` by
    (drule abi_decode_frame_source_window >>
     disch_then (qspecl_then [`B + z`, `MLOAD`, `LENGTH bs`] mp_tac) >>
     asm_simp_tac bool_ss [abi_decode_source_opcode_def]) >>
  qexists_tac `t` >> asm_simp_tac bool_ss [] >>
  fs[abi_decoder_address_frame_def] >> metis_tac[]
QED
