Theory exprSimAbiDecodeBodyEntry
Ancestors
  exprSimAbiDecodeEntryTyping exprSimAbiDecodeEntryMetadata
  exprSimAbiDecodeEntryCoherence exprSimHypsDefs abiCallerDecodeBounds
  vyperTypeSystem vyperTypeInvariants vyperValue vyperTyping allocLimits list option
  exprSafeOperand exprSimSource

Theorem abi_decode_body_target:
  expr_body_pre_mods mods ce cx env (TypeBuiltin ann (AbiDecode unwrap) ty args) es ==>
  ann = ty /\ assignable_type (get_tenv cx) ty /\
  abi_decode_bytes_widths (get_tenv cx) ty
Proof
  simp_tac bool_ss [expr_body_pre_mods_def] >> strip_tac >>
  drule abi_decode_inv_type_env >> strip_tac >>
  drule abi_decode_parent_type >> metis_tac[]
QED

Theorem abi_decode_body_operand_evaluates:
  expr_body_pre_mods mods ce cx env (TypeBuiltin ann (AbiDecode unwrap) ty [e]) es /\
  expr_type e = BaseT (BytesT (Dynamic n)) ==>
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Dynamic n)))
Proof
  simp_tac bool_ss [expr_body_pre_mods_def] >> strip_tac >>
  drule_then assume_tac abi_decode_inv_type_env >>
  `well_typed_expr env e` by metis_tac[abi_decode_parent_type, listTheory.CONS_11] >>
  `env_consistent env cx es` by fs[expr_sim_inv_mods_def] >>
  `!id t. FLOOKUP env.var_types id = SOME t ==>
          well_formed_type env.type_defs t` by
    metis_tac[well_formed_type_def, env_consistent_var_type_evaluates] >>
  drule_all well_typed_expr_type_well_formed >>
  gvs[well_formed_type_def, evaluate_type_def, AllCaseEqs()]
QED

Theorem abi_decode_body_wrapped_coherent:
  expr_body_pre_mods mods ce cx env (TypeBuiltin ann (AbiDecode unwrap) ty args) es ==>
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
  `expr_sim_inv_mods mods ce cx env es` by fs[expr_body_pre_mods_def] >>
  drule_then assume_tac abi_decode_root_metadata_inv >>
  drule_all abi_decode_root_coherent >> metis_tac[]
QED

Theorem abi_decode_body_wrapped_widths:
  expr_body_pre_mods mods ce cx env (TypeBuiltin ann (AbiDecode unwrap) ty args) es ==>
  abi_decode_bytes_widths (get_tenv cx)
    (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty)
Proof
  strip_tac >> drule abi_decode_body_target >> strip_tac >>
  irule abi_decode_wrapped_widths >> simp[]
QED

Theorem abi_decode_body_wrapped_assignable:
  expr_body_pre_mods mods ce cx env (TypeBuiltin ann (AbiDecode unwrap) ty args) es ==>
  assignable_type (get_tenv cx)
    (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty)
Proof
  strip_tac >> drule abi_decode_body_target >> strip_tac >>
  irule abi_decode_wrapped_assignable >> simp[]
QED

Theorem abi_decode_body_output_bound:
  expr_body_pre_mods mods ce cx env (TypeBuiltin ann (AbiDecode unwrap) ty args) es ==>
  type_memory_bytes ce
    (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty) < 2 ** 64
Proof
  simp_tac bool_ss [expr_body_pre_mods_def] >> strip_tac >>
  drule alloc_limits_abi_decode_output >> simp[]
QED
