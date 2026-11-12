(* Namespace-free metadata for compiler-selected ABI sources. *)
Theory bodyAbiEncodeMetadata
Ancestors
  retAbiPlanProps abiTypeBoundProps compileEnv vyperABI contractABI
  vyperValue valueEncoding finite_map

Theorem abi_source_metadata_upto:
  evaluate_type env ty = SOME tv /\
  abi_sfields_consistent_upto (type_value_size tv) sf env ==>
  is_abi_dynamic sf ty = is_dynamic (vyper_to_abi_type env ty) /\
  abi_embedded_static_size sf ty =
    (if is_dynamic (vyper_to_abi_type env ty) then 32
     else static_length (vyper_to_abi_type env ty)) /\
  abi_size_bound sf ty = vyper_abi_size_bound env ty
Proof
  rpt strip_tac >>
  drule_all abi_props_vyper_upto >> strip_tac >>
  drule (cj 1 vyper_to_abi_type_dynamic) >> strip_tac >>
  simp[abi_embedded_static_size_def] >>
  Cases_on `vyper_is_dynamic env ty` >> simp[] >>
  drule_all (cj 1 vyper_to_abi_static_length) >> simp[]
QED

Theorem abi_source_metadata_reference:
  tenv SUBMAP tenv0 /\
  sfields_tenv_consistent ce.ce_struct_fields tenv0 /\
  (!t tv. evaluate_type tenv0 t = SOME tv ==>
    type_memory_bytes ce t = type_memory_size tv) /\
  evaluate_type tenv t = SOME tv ==>
  is_abi_dynamic ce.ce_struct_fields t =
    is_dynamic (vyper_to_abi_type tenv t) /\
  abi_embedded_static_size ce.ce_struct_fields t =
    (if is_dynamic (vyper_to_abi_type tenv t) then 32
     else static_length (vyper_to_abi_type tenv t)) /\
  abi_size_bound ce.ce_struct_fields t = vyper_abi_size_bound tenv0 t /\
  type_memory_bytes ce t = type_memory_size tv
Proof
  strip_tac >>
  drule (cj 1 vyper_to_abi_type_submap) >>
  disch_then drule >> strip_tac >>
  `abi_sfields_consistent_upto (type_value_size tv) ce.ce_struct_fields tenv0`
    by metis_tac[abi_sfields_consistent_upto_init] >>
  drule_all abi_source_metadata_upto >> simp[]
QED
