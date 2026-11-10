(* Return ABI metadata without recursive assignability requirements. *)
Theory supportedReturnAbiMetadata
Ancestors
  supportedPlaceAbiPlan retAbiPlanProps structFieldsProps compileEnv
  abiTypeBoundProps compileVyper abiEncoderProps typedCopyProducer supportedTypes
  exprLowering vyperTyping vyperTypeSystem vyperTypeValues vyperValue
  vyperABI vyperContext finite_map list rich_list arithmetic

Theorem supported_update_cenv_ret_abi_plan:
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
  cenv.ce_struct_fields = make_struct_fields_map tops /\
  supported_place_type tops ret /\ evaluate_type (type_env tops) ret = SOME tv ==>
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
  strip_tac >>
  `sfields_tenv_consistent cenv.ce_struct_fields (type_env tops)`
    by simp[make_struct_fields_map_consistent] >>
  `!k a. FLOOKUP (type_env tops) k = SOME (StructArgs a) ==> FST k = NONE`
    by (rw[type_env_def] >> drule type_env_for_module_struct_mem >>
        rw[] >> simp[]) >>
  `struct_args_unique tops`
    by (irule distinct_type_keys_struct_args_unique >> simp[]) >>
  `!t tv. evaluate_type (type_env tops) t = SOME tv ==>
          type_memory_bytes cenv t = type_memory_size tv`
    by (rpt strip_tac >> drule_all make_struct_fields_map_memory_size >>
        simp[]) >>
  `abi_enc_plan (type_env tops) ret
     (type_to_abi_enc_info cenv.ce_struct_fields cenv ret)`
    by (irule supported_place_type_abi_plan >> simp[] >> metis_tac[]) >>
  `type_env tops SUBMAP type_env tops` by simp[] >>
  drule_all abi_elem_props >> strip_tac >>
  simp[update_cenv_ret_abi_def, external_return_needs_wrap_eq] >>
  IF_CASES_TAC >> gvs[] >>
  conj_tac >- (irule abi_enc_plan_tuple >> gvs[] >>
               drule_all abi_enc_plans_replicate >>
               disch_then (qspec_then `SUC 0` mp_tac) >> gvs[REPLICATE]) >>
  drule (cj 1 abi_props_vyper) >>
  disch_then (qspec_then `make_struct_fields_map tops` mp_tac) >>
  simp[vyper_abi_size_bound_def]
QED
