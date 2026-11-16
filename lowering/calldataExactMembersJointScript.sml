(* Conditional exact decoding of heterogeneous raw-calldata members. *)
Theory calldataExactMembersJoint
Ancestors
  calldataMembersRawCallsite calldataEmptyArrayChild abiDecoderOffset
  abiDecoderCoherence vyperCalldata valueEncodingDefs valueEncodingTyping
  compileEnv exprLowering abiEncoder words list arithmetic vyperTyping valueEncoding calldataSourceCorrespondence abiDecoderDynamic

Theorem calldata_exact_empty_member_source[local]:
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecComplex T [] ==>
  ?x. (!cd p. cd_decode F cd tv p = SOME x) /\
    value_has_type tv x /\ val_wf tv x /\ type_memory_size tv = 0 /\
    (!d mem. val_in_memory tv x d mem)
Proof
  strip_tac >>
  gvs[abi_decoder_empty_dynamic_translation, abi_decoder_coherent_array_iff] >>
  qexists_tac `ArrayV (SArrayV [])` >>
  simp[cd_decode_def, value_has_type_def, vyperValueTheory.make_array_value_def,
    vyperValueTheory.enumerate_static_array_def,
    type_memory_size_def, val_wf_def, val_in_memory_def]
QED

Theorem calldata_exact_member_source_position[local]:
  abi_decoder_coherent ce env sf ty tv /\ ao < dimword (:256) ==>
  cd_decode F s.vs_call_ctx.cc_calldata tv
    (w2n (if dec_info_needs_offset (type_to_abi_dec_info sf ce ty)
          then p + abi_decode_load CALLDATALOAD (p + n2w ao) s
          else p + n2w ao)) =
  cd_decode F s.vs_call_ctx.cc_calldata tv
    (cd_member_ptr F s.vs_call_ctx.cc_calldata tv (w2n p) ao)
Proof
  strip_tac >>
  Cases_on `type_to_abi_dec_info sf ce ty = DecComplex T []`
  >- (drule_all calldata_exact_empty_member_source >> strip_tac >> simp[]) >>
  drule abi_decoder_coherent_dynamic >>
  drule abi_decoder_coherent_header >>
  simp[abi_decoder_header_def] >> rpt strip_tac >>
  `dec_info_needs_offset (type_to_abi_dec_info sf ce ty) = tv_abi_dynamic tv` by
    (metis_tac [abi_decoder_nonempty_offset, calldata_coherent_dynamic]) >>
  `w2n (n2w ao : bytes32) = ao` by simp[] >>
  metis_tac[calldata_member_pointer]
QED
