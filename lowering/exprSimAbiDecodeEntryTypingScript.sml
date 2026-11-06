Theory exprSimAbiDecodeEntryTyping
Ancestors
  exprSimAbiDecodeEntryCoherence exprSimAbiDecodeEntryMetadata exprSimHypsDefs
  abiCallerDecodeBounds vyperTypeSystem vyperTypeInvariants vyperValue
  vyperTyping allocLimits list option

Theorem abi_decode_parent_type:
  well_typed_expr env (TypeBuiltin ann (AbiDecode unwrap) ty args) ==>
  ann = ty /\ assignable_type env.type_defs ty /\
  abi_decode_bytes_widths env.type_defs ty /\
  ?e n. args = [e] /\ expr_type e = BaseT (BytesT (Dynamic n)) /\
    well_typed_expr env e
Proof
  simp[Once well_typed_expr_def, type_builtin_result_ok_def,
       well_typed_type_builtin_args_def] >> strip_tac >>
  Cases_on `args` >> gvs[well_typed_expr_def]
QED

Theorem abi_decode_inv_type_env:
  expr_sim_inv ce cx env es ==> env.type_defs = get_tenv cx
Proof
  simp[expr_sim_inv_def, env_consistent_def, env_context_consistent_def]
QED

Theorem abi_decode_wrapped_type:
  evaluate_type env ty = SOME tv ==>
  evaluate_type env (if wrapped then TupleT [ty] else ty) =
    SOME (if wrapped then TupleTV [tv] else tv)
Proof
  Cases_on `wrapped` >> simp[abi_caller_singleton_type]
QED

Theorem abi_decode_wrapped_assignable:
  assignable_type env ty ==>
  assignable_type env (if wrapped then TupleT [ty] else ty)
Proof
  Cases_on `wrapped` >> simp[] >> strip_tac >>
  drule assignable_type_well_formed >>
  simp[well_formed_type_def, IS_SOME_EXISTS] >> strip_tac >>
  drule abi_caller_singleton_type >>
  simp[Once assignable_type_def, well_formed_type_def]
QED

Theorem abi_decode_wrapped_widths:
  abi_decode_bytes_widths env ty ==>
  abi_decode_bytes_widths env (if wrapped then TupleT [ty] else ty)
Proof
  Cases_on `wrapped` >> simp[abi_decode_bytes_widths_def]
QED

Theorem abi_decode_pre_operand:
  expr_sim_pre ce cx env (TypeBuiltin ann (AbiDecode unwrap) ty args) es ==>
  ?e n. args = [e] /\ expr_type e = BaseT (BytesT (Dynamic n)) /\
    well_typed_expr env e
Proof
  simp_tac bool_ss [expr_sim_pre_def] >> strip_tac >>
  drule abi_decode_parent_type >> metis_tac[]
QED

Theorem abi_decode_pre_target:
  expr_sim_pre ce cx env (TypeBuiltin ann (AbiDecode unwrap) ty args) es ==>
  ann = ty /\ assignable_type (get_tenv cx) ty /\
  abi_decode_bytes_widths (get_tenv cx) ty
Proof
  simp_tac bool_ss [expr_sim_pre_def] >> strip_tac >>
  drule abi_decode_inv_type_env >> strip_tac >>
  drule abi_decode_parent_type >> metis_tac[]
QED

Theorem abi_decode_pre_wrapped_coherent:
  expr_sim_pre ce cx env (TypeBuiltin ann (AbiDecode unwrap) ty args) es ==>
  ?tv. abi_decoder_coherent ce (get_tenv cx) ce.ce_struct_fields
    (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty) tv
Proof
  strip_tac >> drule abi_decode_pre_target >> strip_tac >>
  drule assignable_type_well_formed >>
  simp[well_formed_type_def, IS_SOME_EXISTS] >> strip_tac >>
  drule abi_decode_wrapped_type >>
  disch_then (qspec_then `unwrap /\ needs_external_call_wrap ty` assume_tac) >>
  drule abi_decode_wrapped_assignable >>
  disch_then (qspec_then `unwrap /\ needs_external_call_wrap ty` assume_tac) >>
  `abi_decode_root_metadata ce (get_tenv cx)` by
    (irule abi_decode_root_metadata_inv >> qexistsl_tac [`env`, `es`] >>
     gvs[expr_sim_pre_def]) >>
  drule_all abi_decode_root_coherent >> metis_tac[]
QED

Theorem abi_decode_pre_wrapped_widths:
  expr_sim_pre ce cx env (TypeBuiltin ann (AbiDecode unwrap) ty args) es ==>
  abi_decode_bytes_widths (get_tenv cx)
    (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty)
Proof
  strip_tac >> drule abi_decode_pre_target >> strip_tac >>
  irule abi_decode_wrapped_widths >> simp[]
QED

Theorem abi_decode_pre_wrapped_assignable:
  expr_sim_pre ce cx env (TypeBuiltin ann (AbiDecode unwrap) ty args) es ==>
  assignable_type (get_tenv cx)
    (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty)
Proof
  strip_tac >> drule abi_decode_pre_target >> strip_tac >>
  irule abi_decode_wrapped_assignable >> simp[]
QED

Theorem abi_decode_pre_output_bound:
  expr_sim_pre ce cx env (TypeBuiltin ann (AbiDecode unwrap) ty args) es ==>
  type_memory_bytes ce
    (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty) < 2 ** 64
Proof
  simp_tac bool_ss [expr_sim_pre_def] >> strip_tac >>
  drule alloc_limits_abi_decode_output >> simp[]
QED
