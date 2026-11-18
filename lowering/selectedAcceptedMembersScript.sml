(* Accepted decoding of installed complex members on the real calldata. *)
Theory selectedAcceptedMembers
Ancestors
  selectedAcceptedInterfaces calldataExactMemberValues calldataMembersRawSubregion
  decoderMemberJointModular calldataEmptyArrayChild calldataSourceCorrespondence
  abiDecoderOffset abiDecoderDynamic abiDecoderMemberCons abiDecoderMemberCode abiDecoderComplexExecute
  abiDecoderContract abiDecoderFrame abiDecoderLoop fragExec venomExecSemantics venomInst
  fragGasPathMem fragGasOriginPtrLoop fragGasOriginPtrExec freshWrites
  vyperCalldata valueEncoding valueEncodingDefs valueEncodingTyping vyperTyping
  abiDecoderCoherence compileEnv exprLowering abiEncoder words finite_map list arithmetic

(* The addition uses a word literal, even if the mathematical head cursor
   does not fit in a word. The source also reduces that cursor modulo 2^256. *)
Theorem selected_member_source_decode[local]:
  abi_decoder_coherent ce env sf ty tv ==>
  cd_decode F s.vs_call_ctx.cc_calldata tv
    (w2n (if dec_info_needs_offset (type_to_abi_dec_info sf ce ty)
          then p + abi_decode_load CALLDATALOAD (p + n2w ao) s
          else p + n2w ao)) =
  cd_decode F s.vs_call_ctx.cc_calldata tv
    (cd_member_ptr F s.vs_call_ctx.cc_calldata tv (w2n p) ao)
Proof
  strip_tac >>
  Cases_on `type_to_abi_dec_info sf ce ty = DecComplex T []`
  >- gvs[abi_decoder_empty_dynamic_translation,
         abi_decoder_coherent_array_iff, cd_decode_def] >>
  drule abi_decoder_coherent_dynamic >>
  drule abi_decoder_coherent_header >>
  simp[abi_decoder_header_def] >> rpt strip_tac >>
  `dec_info_needs_offset (type_to_abi_dec_info sf ce ty) = tv_abi_dynamic tv` by
    metis_tac[abi_decoder_nonempty_offset, calldata_coherent_dynamic] >>
  `cd_member_ptr F s.vs_call_ctx.cc_calldata tv (w2n p) ao =
    cd_member_ptr F s.vs_call_ctx.cc_calldata tv (w2n p)
      (w2n (n2w ao : bytes32))` by
    simp[cd_member_ptr_def, cd_at_def, MOD_PLUS] >>
  metis_tac[calldata_member_pointer]
QED

Theorem selected_member_cons_trace[local]:
  compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    ((di,az,mz)::rest) ao vo st = ((),last) /\ fn_has_code st last fn ==>
  ?ops mid en.
    abi_decode_member_setup dst src CALLDATALOAD (Lit 0w) (Lit 0w)
      (dec_info_needs_offset di) ao vo st = (ops,mid) /\
    compile_abi_decode_to_buf (SND ops) (FST ops) CALLDATALOAD (Lit 0w) (Lit 0w)
      di mid = ((),en) /\
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w)
      rest (ao+az) (vo+mz) en = ((),last) /\
    fn_has_code st mid fn /\ fn_has_code mid en fn /\ fn_has_code en last fn /\
    st.cs_next_id <= mid.cs_next_id /\ mid.cs_next_id <= en.cs_next_id /\
    en.cs_next_id <= last.cs_next_id /\
    st.cs_next_var <= mid.cs_next_var /\ mid.cs_next_var <= en.cs_next_var /\
    en.cs_next_var <= last.cs_next_var
Proof
  rewrite_tac[abiDecoderMemberSetupTheory.abi_decode_complex_member_phases] >>
  simp_tac bool_ss [comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `abi_decode_member_setup _ _ _ _ _ _ _ _ st = (ops,mid)` >>
  rename1 `compile_abi_decode_to_buf _ _ _ _ _ di mid = ((),en)` >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_member_cons_code >> strip_tac >>
  `fn_has_code st mid fn /\ fn_has_code mid en fn` by
    metis_tac[fn_has_code_split] >>
  simp[]
QED

Theorem selected_member_exit_phi[local]:
  compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    infos ao vo en = ((),last) /\ fn_has_code en last fn /\
  (last.cs_current_insts = [] ==> !bb.
      lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\ en.cs_current_insts = [] ==>
  !bb. lookup_block en.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0
Proof
  Cases_on `infos`
  >- (simp[Once compile_abi_decode_to_buf_def, comp_return_def] >> metis_tac[]) >>
  PairCases_on `h` >> strip_tac >>
  drule_all selected_member_cons_trace >> strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_member_setup_shape >> strip_tac >>
  `mid.cs_current_insts <> [] /\ phi_prefix_length mid.cs_current_insts = 0` by
    fs[phi_prefix_length_def, mk_inst_def] >>
  metis_tac[exprSimAbiDecodePhiBoundaryTheory.abi_decode_continuation_exit_phi]
QED

Theorem selected_fixed_source_list[local]:
  !n i cd t p nat.
    cd_decode_elems nat cd t p i n =
    cd_decode_list nat cd (REPLICATE n t) p (i * tv_abi_size t)
Proof
  Induct
  >- simp[cd_decode_def, rich_listTheory.REPLICATE] >>
  rpt gen_tac >>
  simp[Once cd_decode_def, rich_listTheory.REPLICATE] >>
  simp[Once cd_decode_def, LEFT_ADD_DISTRIB]
QED
