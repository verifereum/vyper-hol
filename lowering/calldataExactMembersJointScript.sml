(* Conditional exact decoding of heterogeneous raw-calldata members. *)
Theory calldataExactMembersJoint
Ancestors
  calldataMembersRawCallsite calldataEmptyArrayChild abiDecoderOffset
  abiDecoderCoherence vyperCalldata valueEncodingDefs valueEncodingTyping
  compileEnv exprLowering abiEncoder words list arithmetic vyperTyping valueEncoding

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
