Theory calldataSourceCorrespondence
Ancestors
  vyperCalldata vyperCalldataProps calldataRecursiveProducers abiDecoderContract
  abiDecoderCoherence abiDecoderDynamic abiDecoderOffset compileEnv vyperABI exprLowering abiEncoder
  arithmetic list words

Theorem calldata_decode_load_word:
  abi_decode_load CALLDATALOAD (p:bytes32) s =
  cd_word s.vs_call_ctx.cc_calldata (w2n p)
Proof
  simp[abi_decode_load_def, abi_decode_source_def, cd_word_def, cd_bytes_def]
QED

Theorem calldata_member_pointer:
  cd_member_ptr F s.vs_call_ctx.cc_calldata tv (w2n bp) (w2n ofs) =
  w2n (if tv_abi_dynamic tv then
    bp + abi_decode_load CALLDATALOAD (bp + ofs) s else bp + ofs)
Proof
  Cases_on `tv_abi_dynamic tv` >>
  simp[cd_member_ptr_def, cd_at_def, calldata_decode_load_word,
       word_add_def, w2n_n2w]
QED

Theorem calldata_coherent_dynamic:
  !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==>
  is_abi_dynamic ce.ce_struct_fields ty = tv_abi_dynamic tv
Proof
  ho_match_mp_tac calldata_coherent_induction >> rpt conj_tac >>
  rpt gen_tac >> strip_tac
  >- (Cases_on `bt` >> simp[is_abi_dynamic_def, tv_abi_dynamic_def] >>
      rename1 `BytesT b` >> Cases_on `b` >>
      simp[is_abi_dynamic_def, tv_abi_dynamic_def])
  >- simp[is_abi_dynamic_def, tv_abi_dynamic_def]
  >- (Cases_on `bound` >> simp[is_abi_dynamic_def, tv_abi_dynamic_def])
  >- (qpat_x_assum `abi_decoder_header _ _ _ _` kall_tac >>
      simp[is_abi_dynamic_def, tv_abi_dynamic_def] >>
      pop_assum mp_tac >> qid_spec_tac `tvs` >> Induct_on `tys` >>
      Cases_on `tvs` >> simp[tv_abi_dynamic_def, is_abi_dynamic_def] >>
      metis_tac[])
  >> `LIST_REL (\ty tv. is_dynamic (vyper_to_abi_type (env \\ nsid) ty) =
          tv_abi_dynamic tv) (MAP SND args) tvs` by
       (gvs[LIST_REL_EL_EQN] >> rpt strip_tac >>
        first_x_assum drule >> strip_tac >>
        drule abi_decoder_coherent_header >> simp[abi_decoder_header_def])
  >> qpat_x_assum `abi_decoder_header _ _ _ _` mp_tac
  >> simp[abi_decoder_header_def, vyper_to_abi_type_def, tv_abi_dynamic_def]
  >> strip_tac >>
  `any_dynamic (vyper_to_abi_types (env \\ nsid) (MAP SND args)) =
    tv_abi_dynamic_fields (ZIP (MAP FST args,tvs))` suffices_by metis_tac[] >>
  qpat_x_assum `LIST_REL (\ty tv. is_dynamic _ = _) _ _` mp_tac >>
  rpt (pop_assum kall_tac) >>
  qid_spec_tac `tvs` >> Induct_on `args` >> Cases_on `tvs` >>
  simp[tv_abi_dynamic_def, vyper_to_abi_type_def] >>
  Cases_on `h` >> simp[tv_abi_dynamic_def, vyper_to_abi_type_def] >>
  metis_tac[]
QED

(* The addition uses a word literal, even if the mathematical head cursor
   does not fit in a word. The source also reduces that cursor modulo 2^256. *)
Theorem member_source_decode:
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
