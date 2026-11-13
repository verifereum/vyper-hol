(* Scalar descriptors are independent of the descending struct map. *)
Theory entryReachBodyDescendingScalarClosure
Ancestors
  entryReachBodyDescendingProducer entryReachBodyConditionalProducerClosure
  entryReachBodyCertifiedProducer entryReachBodyDescendingMetadata
  abiDecoderTypedContract abiDecoderCoherence exprLowering

Theorem descending_base_root[local]:
  entry_descending_certified_child_producer cert ce env sf
    (BaseT bt) tv av v ctx fn oid root extent ambient b cap site limit_st <=>
  entry_certified_child_producer cert ce env
    (BaseT bt) tv av v ctx fn oid root extent ambient b cap site limit_st
Proof
  Cases_on `bt` >>
  simp_tac bool_ss [entry_descending_certified_child_producer_def,
    entry_certified_child_producer_def, entry_descending_metadata_def,
    abi_decoder_metadata_def, abi_decoder_coherent_base_iff,
    type_to_abi_dec_info_def] >>
  Cases_on `b'` >> simp_tac bool_ss [type_to_abi_dec_info_def]
QED

Theorem descending_flag_root[local]:
  entry_descending_certified_child_producer cert ce env sf
    (FlagT nsid) tv av v ctx fn oid root extent ambient b cap site limit_st <=>
  entry_certified_child_producer cert ce env
    (FlagT nsid) tv av v ctx fn oid root extent ambient b cap site limit_st
Proof
  simp_tac bool_ss [entry_descending_certified_child_producer_def,
    entry_certified_child_producer_def, entry_descending_metadata_def,
    abi_decoder_metadata_def, abi_decoder_coherent_flag_iff,
    type_to_abi_dec_info_def]
QED

Theorem entry_descending_base_producer:
  abi_decoder_coherent ce env sf (BaseT bt) tv ==>
  entry_descending_certified_child_producer
    (\z. z.cs_current_insts = [] ==> !bb.
      lookup_block z.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0)
    ce env sf (BaseT bt) tv av v ctx fn oid root extent ambient b cap site limit_st
Proof
  simp_tac bool_ss [descending_base_root, entry_certified_child_conditional,
    abi_decoder_coherent_base_iff] >>
  strip_tac >> irule entry_conditional_base_producer >>
  simp[abi_decoder_coherent_base_iff]
QED

Theorem entry_descending_flag_producer:
  abi_decoder_coherent ce env sf (FlagT nsid) tv ==>
  entry_descending_certified_child_producer
    (\z. z.cs_current_insts = [] ==> !bb.
      lookup_block z.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0)
    ce env sf (FlagT nsid) tv av v ctx fn oid root extent ambient b cap site limit_st
Proof
  simp_tac bool_ss [descending_flag_root, entry_certified_child_conditional,
    abi_decoder_coherent_flag_iff] >>
  strip_tac >> irule entry_conditional_flag_producer >>
  simp[abi_decoder_coherent_flag_iff] >> goal_assum (drule_at Any) >> simp[]
QED
