Theory extRetEncodableMetadataPtr
Ancestors
  extRetRecursivePlanPtr extRetSupportedShapePtr retAbiPlanProps returnMetadataPtr
  structFieldsProps typedCopyProducer compileEnv compileVyper exprLowering
  vyperContext vyperAST vyperTypeSystem vyperValue vyperABI contractABI
  abiEncoderProps finite_map list rich_list option

val _ = Parse.hide "body";

Theorem ext_ret_encodable_update_plan:
  !tops cenv ret.
    ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    encodable_ret_shape (type_env tops) ret ==>
    abi_enc_plan (type_env tops)
      (if needs_external_call_wrap ret /\
          is_dynamic (vyper_to_abi_type (type_env tops) ret)
       then TupleT [ret] else ret)
      (update_cenv_ret_abi cenv ret).ce_ret_enc_info /\
    vyper_abi_size_bound (type_env tops)
      (if needs_external_call_wrap ret /\
          is_dynamic (vyper_to_abi_type (type_env tops) ret)
       then TupleT [ret] else ret) =
      (update_cenv_ret_abi cenv ret).ce_max_return_size
Proof
  rpt gen_tac >> strip_tac >>
  `sfields_tenv_consistent cenv.ce_struct_fields (type_env tops)`
    by simp[make_struct_fields_map_consistent] >>
  `!k a. FLOOKUP (type_env tops) k = SOME (StructArgs a) ==> FST k = NONE`
    by (rw[type_env_def] >> drule type_env_for_module_struct_mem >>
        rw[] >> simp[]) >>
  `struct_args_unique tops`
    by (irule distinct_type_keys_struct_args_unique >> simp[]) >>
  `!t tv. evaluate_type (type_env tops) t = SOME tv ==>
          type_memory_bytes cenv t = type_memory_size tv`
    by (rpt strip_tac >> drule_all make_struct_fields_map_memory_size >> simp[]) >>
  `abi_enc_plan (type_env tops) ret
     (type_to_abi_enc_info cenv.ce_struct_fields cenv ret)`
    by (irule encodable_ret_shape_plan >> simp[] >>
        qexists_tac `type_env tops` >> simp[make_struct_fields_map_consistent]) >>
  drule encodable_ret_shape_evaluates >> strip_tac >>
  `type_env tops SUBMAP type_env tops` by simp[] >>
  drule_all abi_elem_props >> strip_tac >>
  drule (cj 1 vyper_to_abi_type_dynamic) >> strip_tac >>
  simp[update_cenv_ret_abi_def, external_return_needs_wrap_eq] >>
  IF_CASES_TAC >> gvs[] >>
  conj_tac >- (irule abi_enc_plan_tuple >> gvs[] >>
               drule_all abi_enc_plans_replicate >>
               disch_then (qspec_then `SUC 0` mp_tac) >> gvs[REPLICATE]) >>
  simp[vyper_abi_size_bound_def]
QED

Theorem ext_ret_encodable_package_plan:
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut, nr, rr, name, args, defaults, ret, body)) =
    (lbl, cenv0, pos, cds, payable, nr', key, ut, view, body', rt) /\
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
  encodable_ret_shape (type_env tops) ret /\ ret <> NoneT ==>
  abi_enc_plan (type_env tops)
    (if needs_external_call_wrap ret /\
        is_dynamic (vyper_to_abi_type (type_env tops) ret)
     then TupleT [ret] else ret) cenv0.ce_ret_enc_info /\
  vyper_abi_size_bound (type_env tops)
    (if needs_external_call_wrap ret /\
        is_dynamic (vyper_to_abi_type (type_env tops) ret)
     then TupleT [ret] else ret) = cenv0.ce_max_return_size
Proof
  strip_tac >>
  gvs[package_external_fn_def, set_external_package_target_def,
      update_cenv_nonreentrant_def] >>
  irule ext_ret_encodable_update_plan >>
  simp[build_compile_env_ce_struct_fields]
QED

Theorem ext_ret_encodable_frame_plan:
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut, nr, rr, name, args, defaults, ret, body)) =
    (lbl, cenv0, pos, cds, payable, nr', key, ut, view, body', rt) /\
  compile_register_positional_args cenv0 pos off st = (cenv, sa) /\
  same_frame cenv next /\
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
  encodable_ret_shape (type_env tops) ret /\ ret <> NoneT ==>
  abi_enc_plan (type_env tops)
    (if needs_external_call_wrap ret /\
        is_dynamic (vyper_to_abi_type (type_env tops) ret)
     then TupleT [ret] else ret) next.ce_ret_enc_info
Proof
  strip_tac >> drule_all ext_ret_encodable_package_plan >> strip_tac >>
  drule_all register_same_frame_metadata >>
  simp[compile_env_component_equality] >> metis_tac[]
QED

Theorem ext_ret_encodable_frame_size:
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut, nr, rr, name, args, defaults, ret, body)) =
    (lbl, cenv0, pos, cds, payable, nr', key, ut, view, body', rt) /\
  compile_register_positional_args cenv0 pos off st = (cenv, sa) /\
  same_frame cenv next /\
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
  encodable_ret_shape (type_env tops) ret /\ ret <> NoneT ==>
  vyper_abi_size_bound (type_env tops)
    (if needs_external_call_wrap ret /\
        is_dynamic (vyper_to_abi_type (type_env tops) ret)
     then TupleT [ret] else ret) = next.ce_max_return_size
Proof
  strip_tac >> drule_all ext_ret_encodable_package_plan >> strip_tac >>
  drule_all register_same_frame_metadata >>
  simp[compile_env_component_equality] >> metis_tac[]
QED

Theorem ext_ret_supported_frame_plan:
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut, nr, rr, name, args, defaults, ret, body)) =
    (lbl, cenv0, pos, cds, payable, nr', key, ut, view, body', rt) /\
  compile_register_positional_args cenv0 pos off st = (cenv, sa) /\
  same_frame cenv next /\
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
  supported_place_type tops ret /\ evaluate_type (type_env tops) ret = SOME tv /\
  ret <> NoneT ==>
  abi_enc_plan (type_env tops)
    (if needs_external_call_wrap ret /\
        is_dynamic (vyper_to_abi_type (type_env tops) ret)
     then TupleT [ret] else ret) next.ce_ret_enc_info
Proof
  strip_tac >> drule_all supported_place_encodable_ret_shape >> strip_tac >>
  drule_all ext_ret_encodable_frame_plan >> simp[]
QED

Theorem ext_ret_supported_frame_size:
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut, nr, rr, name, args, defaults, ret, body)) =
    (lbl, cenv0, pos, cds, payable, nr', key, ut, view, body', rt) /\
  compile_register_positional_args cenv0 pos off st = (cenv, sa) /\
  same_frame cenv next /\
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
  supported_place_type tops ret /\ evaluate_type (type_env tops) ret = SOME tv /\
  ret <> NoneT ==>
  vyper_abi_size_bound (type_env tops)
    (if needs_external_call_wrap ret /\
        is_dynamic (vyper_to_abi_type (type_env tops) ret)
     then TupleT [ret] else ret) = next.ce_max_return_size
Proof
  strip_tac >> drule_all supported_place_encodable_ret_shape >> strip_tac >>
  drule_all ext_ret_encodable_frame_size >> simp[]
QED

(* Empty structs need no assignable-type premise. *)
Theorem ext_ret_empty_struct_update_regression[local]:
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
  cenv.ce_struct_fields = make_struct_fields_map tops /\
  FLOOKUP (type_env tops) id = SOME (StructArgs []) /\
  evaluate_type (type_env tops) (StructT id) = SOME tv ==>
  abi_enc_plan (type_env tops) (StructT id)
    (update_cenv_ret_abi cenv (StructT id)).ce_ret_enc_info /\
  vyper_abi_size_bound (type_env tops) (StructT id) =
    (update_cenv_ret_abi cenv (StructT id)).ce_max_return_size
Proof
  strip_tac >> drule_all encodable_ret_shape_empty_struct >> strip_tac >>
  drule_all ext_ret_encodable_update_plan >>
  simp[needs_external_call_wrap_def]
QED
