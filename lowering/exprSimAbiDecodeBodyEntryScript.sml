Theory exprSimAbiDecodeBodyEntry
Ancestors
  exprSimAbiDecodeEntryTyping exprSimAbiDecodeEntryMetadata
  exprSimAbiDecodeEntryCoherence exprSimHypsDefs abiCallerDecodeBounds
  vyperTypeSystem vyperTypeInvariants vyperValue vyperTyping allocLimits list option

Theorem abi_decode_body_target:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiDecode unwrap) ty args) es ==>
  ann = ty /\ assignable_type (get_tenv cx) ty /\
  abi_decode_bytes_widths (get_tenv cx) ty
Proof
  simp_tac bool_ss [expr_body_pre_def] >> strip_tac >>
  drule abi_decode_inv_type_env >> strip_tac >>
  drule abi_decode_parent_type >> metis_tac[]
QED

Theorem abi_decode_body_wrapped_coherent:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiDecode unwrap) ty args) es ==>
  ?tv. abi_decoder_coherent ce (get_tenv cx) ce.ce_struct_fields
    (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty) tv
Proof
  strip_tac >> drule abi_decode_body_target >> strip_tac >>
  drule assignable_type_well_formed >>
  simp[well_formed_type_def, IS_SOME_EXISTS] >> strip_tac >>
  drule abi_decode_wrapped_type >>
  disch_then (qspec_then `unwrap /\ needs_external_call_wrap ty` assume_tac) >>
  drule abi_decode_wrapped_assignable >>
  disch_then (qspec_then `unwrap /\ needs_external_call_wrap ty` assume_tac) >>
  `abi_decode_root_metadata ce (get_tenv cx)` by
    (irule abi_decode_root_metadata_inv >> qexistsl_tac [`env`, `es`] >>
     fs[expr_body_pre_def]) >>
  drule_all abi_decode_root_coherent >> metis_tac[]
QED

Theorem abi_decode_body_wrapped_widths:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiDecode unwrap) ty args) es ==>
  abi_decode_bytes_widths (get_tenv cx)
    (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty)
Proof
  strip_tac >> drule abi_decode_body_target >> strip_tac >>
  irule abi_decode_wrapped_widths >> simp[]
QED

Theorem abi_decode_body_wrapped_assignable:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiDecode unwrap) ty args) es ==>
  assignable_type (get_tenv cx)
    (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty)
Proof
  strip_tac >> drule abi_decode_body_target >> strip_tac >>
  irule abi_decode_wrapped_assignable >> simp[]
QED

Theorem abi_decode_body_output_bound:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiDecode unwrap) ty args) es ==>
  type_memory_bytes ce
    (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty) < 2 ** 64
Proof
  simp_tac bool_ss [expr_body_pre_def] >> strip_tac >>
  drule alloc_limits_abi_decode_output >> simp[]
QED
