(* Reachable decoder headers from root metadata, without namespace restrictions. *)
Theory abiMetadataHeader
Ancestors
  abiMetadataLayout abiLayoutSource abiCallerTupleLayout abiCallerAbiShape
  abiDecoderCoherence compileEnv vyperABI vyperValue list finite_map

Theorem metadata_abi_shape:
  evaluate_type env ty = SOME tv /\ sfields_tenv_consistent sf env ==>
  abi_caller_abi_shape sf env ty
Proof
  strip_tac >> drule_all abi_layout_vyper_type >> strip_tac >>
  drule (cj 1 vyper_to_abi_type_dynamic) >> strip_tac >>
  simp[abi_caller_abi_shape_def] >> strip_tac >>
  drule_all (cj 1 vyper_to_abi_static_length) >> simp[]
QED

Theorem metadata_decoder_header:
  evaluate_type env ty = SOME tv /\
  sfields_tenv_consistent ce.ce_struct_fields env /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    EVERY (\(fname,fty,sz). !v. evaluate_type env fty = SOME v ==>
                                    sz = type_memory_size v) fields) ==>
  abi_decoder_header ce env ty tv
Proof
  strip_tac >> irule abi_caller_header_from_shape >> simp[] >>
  conj_tac
  >- (drule_all metadata_type_memory_size >> simp[])
  >> drule_all metadata_abi_shape >> simp[]
QED
