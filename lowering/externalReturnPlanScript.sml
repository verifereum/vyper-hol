Theory externalReturnPlan
Ancestors
  externalReturnPackage retAbiPlanProps externalReturnSupport
  e2eDefs vyperTypeContract vyperTypeContractStaticMaps vyperTypeContractContext
  vyperInterpreter supportedDecls supportedProgram abiTypeBoundProps compileVyper compileEnv exprLowering
  abiEncoderProps structFieldsProps typedCopyProducer supportedTypes
  vyperTypeSystem vyperContext vyperValue vyperABI contractABI
  valueEncoding finite_map list rich_list option pair combin

Theorem return_plan_array[local]:
  evaluate_type tenv (ArrayT elem bd) = SOME tv /\
  evaluate_type tenv elem = SOME etv /\
  abi_enc_plan tenv elem (type_to_abi_enc_info sf cenv elem) /\
  tenv SUBMAP tenv0 /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv0 /\
  (!k a. FLOOKUP tenv0 k = SOME (StructArgs a) ==> FST k = NONE) /\
  (!t tv. evaluate_type tenv0 t = SOME tv ==>
          type_memory_bytes cenv t = type_memory_size tv) ==>
  abi_enc_plan tenv (ArrayT elem bd)
    (type_to_abi_enc_info sf cenv (ArrayT elem bd))
Proof
  strip_tac >> Cases_on `bd` >> simp[Once type_to_abi_enc_info_def]
  >- (IF_CASES_TAC >- (drule_all abi_enc_plan_static_copy >> simp[]) >>
      simp[GSYM REPLICATE_GENLIST] >>
      qpat_x_assum `evaluate_type tenv elem = _` assume_tac >>
      drule_all abi_elem_props >> strip_tac >>
      irule abi_enc_plan_sarray >> gvs[is_abi_dynamic_def] >>
      drule_all abi_enc_plans_replicate >>
      disch_then (qspec_then `n` mp_tac) >> gvs[]) >>
  qpat_x_assum `evaluate_type tenv elem = _` assume_tac >>
  drule_all abi_elem_props >> strip_tac >> simp[] >>
  irule abi_enc_plan_dynarray >> simp[]
QED

Theorem return_map_struct_types[local]:
  !fields. MAP (\(fn, fty, sz). g fty) fields = MAP g (MAP (FST o SND) fields)
Proof
  Induct >> simp[FORALL_PROD]
QED

Theorem return_supported_evaluated_plan:
  !sf cenv ty fuel tops tenv tv.
    supported_nested_type supported_scalar_type fuel tops ty /\
    tenv SUBMAP type_env tops /\ evaluate_type tenv ty = SOME tv /\
    sfields_tenv_consistent sf tenv /\
    sfields_tenv_consistent cenv.ce_struct_fields (type_env tops) /\
    (!k a. FLOOKUP (type_env tops) k = SOME (StructArgs a) ==> FST k = NONE) /\
    (!t tv. evaluate_type (type_env tops) t = SOME tv ==>
            type_memory_bytes cenv t = type_memory_size tv) ==>
    abi_enc_plan tenv ty (type_to_abi_enc_info sf cenv ty)
Proof
  recInduct type_to_abi_enc_info_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt strip_tac
  >~ [`BaseT (BytesT (Dynamic n))`]
  >- simp[type_to_abi_enc_info_def, abi_enc_plan_bytes]
  >~ [`BaseT (StringT n)`]
  >- simp[type_to_abi_enc_info_def, abi_enc_plan_string]
  >~ [`ArrayT elem (Dynamic n)`]
  >- suspend "dynamic_array"
  >~ [`ArrayT elem (Fixed n)`]
  >- suspend "fixed_array"
  >~ [`TupleT tys`]
  >- suspend "tuple"
  >~ [`StructT id`]
  >- suspend "struct" >>
  gvs[Once supported_nested_type_def, supported_scalar_type_def,
      supported_word_type_def, supported_string_type_def] >>
  irule return_static_evaluated_plan >>
  simp[is_abi_dynamic_def] >> metis_tac[]
QED

Resume return_supported_evaluated_plan[dynamic_array]:
  qpat_x_assum `supported_nested_type _ _ _ (ArrayT _ _)` mp_tac >>
  simp[Once supported_nested_type_def, supported_scalar_type_def,
       supported_word_type_def, supported_string_type_def] >> strip_tac >>
  `?etv. evaluate_type tenv elem = SOME etv` by
    (gvs[evaluate_type_def, AllCaseEqs()]) >>
  `abi_enc_plan tenv elem (type_to_abi_enc_info sfields cenv elem)` by
    (first_x_assum irule >> metis_tac[]) >>
  irule return_plan_array >> metis_tac[]
QED

Resume return_supported_evaluated_plan[fixed_array]:
  Cases_on `is_abi_dynamic cenv.ce_struct_fields (ArrayT elem (Fixed n))`
  >- (qpat_x_assum `supported_nested_type _ _ _ (ArrayT _ _)` mp_tac >>
      simp[Once supported_nested_type_def, supported_scalar_type_def,
           supported_word_type_def, supported_string_type_def] >> strip_tac >>
      `?etv. evaluate_type tenv elem = SOME etv` by
        (gvs[evaluate_type_def, AllCaseEqs()]) >>
      `abi_enc_plan tenv elem (type_to_abi_enc_info sfields cenv elem)` by
        (first_x_assum (qspec_then `0` mp_tac) >> simp[] >>
         disch_then irule >> metis_tac[]) >>
      irule return_plan_array >> metis_tac[]) >>
  irule return_static_evaluated_plan >> simp[] >> metis_tac[]
QED

Resume return_supported_evaluated_plan[tuple]:
  Cases_on `is_abi_dynamic cenv.ce_struct_fields (TupleT tys)`
  >- (qpat_x_assum `supported_nested_type _ _ _ (TupleT _)` mp_tac >>
      simp[Once supported_nested_type_def, supported_scalar_type_def,
           supported_word_type_def, supported_string_type_def] >> strip_tac >>
      `!t. MEM t tys ==> IS_SOME (evaluate_type tenv t)` by
        (qpat_x_assum `evaluate_type tenv (TupleT tys) = _` mp_tac >>
         simp[evaluate_type_def, evaluate_types_OPT_MMAP, AllCaseEqs()] >>
         strip_tac >>
         `IS_SOME (OPT_MMAP (evaluate_type tenv) tys)` by simp[] >>
         gvs[IS_SOME_OPT_MMAP, EVERY_MEM, EVERY_MAP]) >>
      drule_all abi_elem_props >> strip_tac >>
      simp[Once type_to_abi_enc_info_def] >>
      gvs[] >> irule abi_enc_plan_tuple >> simp[] >>
      irule abi_enc_plans_map >> simp[] >>
      reverse conj_tac >- (qexists `type_env tops` >> simp[]) >>
      rpt strip_tac >> simp[] >>
      qpat_x_assum `!t. _ ==> !fuel tops tenv tv. _` (drule_then mp_tac) >>
      simp[] >> disch_then irule >>
      gvs[EVERY_MEM, IS_SOME_EXISTS] >> metis_tac[]) >>
  irule return_static_evaluated_plan >> simp[] >> metis_tac[]
QED

Resume return_supported_evaluated_plan[struct]:
  Cases_on `is_abi_dynamic cenv.ce_struct_fields (StructT id)`
  >- (qpat_x_assum `supported_nested_type _ _ _ (StructT _)` mp_tac >>
      simp[Once supported_nested_type_def, supported_scalar_type_def,
           supported_word_type_def, supported_string_type_def] >> strip_tac >>
      Cases_on `supported_struct_fields tops id` >> gvs[] >>
      rename1 `supported_struct_fields tops id = SOME args` >>
      `FLOOKUP (type_env tops) id = SOME (StructArgs args)` by
        (drule supported_struct_fields_type_env >> simp[]) >>
      drule_all abi_elem_props >> strip_tac >>
      qpat_x_assum `evaluate_type tenv (StructT id) = _` mp_tac >>
      simp[evaluate_type_def, AllCaseEqs()] >> strip_tac >>
      `args' = args` by
        (gvs[] >> qpat_x_assum `tenv SUBMAP _` mp_tac >>
         simp[SUBMAP_FLOOKUP_EQN] >> disch_then drule >> simp[]) >> gvs[] >>
      `!k a. FLOOKUP tenv k = SOME (StructArgs a) ==> FST k = NONE` by
        (fs[SUBMAP_FLOOKUP_EQN] >> metis_tac[]) >>
      `?fields. FLOOKUP sfields (nsid_to_string id) = SOME fields /\
                MAP (FST o SND) fields = MAP SND args` by
        (qpat_x_assum `sfields_tenv_consistent sfields tenv` mp_tac >>
         simp[sfields_tenv_consistent_def] >> strip_tac >>
         first_x_assum drule >> strip_tac >> simp[]) >>
      `sfields_tenv_consistent (sfields \\ nsid_to_string id) (tenv \\ id)` by
        (irule (cj 1 sfields_tenv_consistent_domsub) >> metis_tac[]) >>
      `tenv \\ id SUBMAP type_env tops` by
        (irule SUBMAP_TRANS >> qexists `tenv` >> simp[]) >>
      `!t. MEM t (MAP SND args) ==> IS_SOME (evaluate_type (tenv \\ id) t)` by
        (qpat_x_assum `evaluate_types _ _ _ = _` mp_tac >>
         simp[evaluate_types_OPT_MMAP] >> strip_tac >>
         `IS_SOME (OPT_MMAP (evaluate_type (tenv \\ id)) (MAP SND args))` by simp[] >>
         gvs[IS_SOME_OPT_MMAP, EVERY_MAP, EVERY_MEM, MEM_MAP, PULL_EXISTS]) >>
      simp[Once type_to_abi_enc_info_def, return_map_struct_types] >>
      gvs[] >> irule abi_enc_plan_struct >> simp[] >>
      irule abi_enc_plans_map >> simp[] >>
      reverse conj_tac >- (qexists `type_env tops` >> simp[]) >>
      rpt strip_tac >> simp[] >>
      `?fn sz. MEM (fn,t,sz) fields` by
        (`MEM t (MAP (FST o SND) fields)` by metis_tac[] >>
         pop_assum mp_tac >> simp[MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
      qpat_x_assum `!fn fty sz. _` (drule_then irule) >>
      gvs[EVERY_MEM, MEM_MAP, IS_SOME_EXISTS] >> metis_tac[]) >>
  irule return_static_evaluated_plan >> simp[] >> metis_tac[]
QED
Finalise return_supported_evaluated_plan

Theorem return_abi_dynamic[local]:
  (!tenv ty tv.
     evaluate_type tenv ty = SOME tv ==>
     is_dynamic (vyper_to_abi_type tenv ty) = vyper_is_dynamic tenv ty) /\
  (!tenv ts acc tvs.
     evaluate_types tenv ts acc = SOME tvs ==>
     any_dynamic (vyper_to_abi_types tenv ts) = vyper_any_dynamic tenv ts)
Proof
  ho_match_mp_tac evaluate_type_ind >> rpt conj_tac >> rpt gen_tac >>
  simp[evaluate_type_def, vyper_is_dynamic_def, AllCaseEqs(), PULL_EXISTS] >>
  rpt strip_tac >> gvs[vyper_is_dynamic_def] >>
  Cases_on `bd` >> gvs[vyper_is_dynamic_def]
QED

Theorem return_update_plan_supported_evaluated:
  !tops cenv ret fuel tv.
    ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    supported_nested_type supported_scalar_type fuel tops ret /\
    evaluate_type (type_env tops) ret = SOME tv ==>
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
    by (rw[type_env_def] >> drule type_env_for_module_struct_mem >> rw[] >> simp[]) >>
  `struct_args_unique tops`
    by (irule distinct_type_keys_struct_args_unique >> simp[]) >>
  `!t tv. evaluate_type (type_env tops) t = SOME tv ==>
          type_memory_bytes cenv t = type_memory_size tv`
    by (rpt strip_tac >> drule_all make_struct_fields_map_memory_size >> simp[]) >>
  `abi_enc_plan (type_env tops) ret
     (type_to_abi_enc_info cenv.ce_struct_fields cenv ret)` by
    (irule return_supported_evaluated_plan >> simp[] >>
     qexistsl [`fuel`, `tops`] >> gvs[]) >>
  `type_env tops SUBMAP type_env tops` by simp[] >>
  drule_all abi_elem_props >> strip_tac >>
  drule (cj 1 return_abi_dynamic) >> strip_tac >>
  simp[update_cenv_ret_abi_def, external_return_needs_wrap_eq] >>
  IF_CASES_TAC >> gvs[] >>
  conj_tac >- (irule abi_enc_plan_tuple >> gvs[] >>
               drule_all abi_enc_plans_replicate >>
               disch_then (qspec_then `SUC 0` mp_tac) >> gvs[REPLICATE]) >>
  simp[vyper_abi_size_bound_def]
QED

Theorem return_update_plan_supported_place:
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
  cenv.ce_struct_fields = make_struct_fields_map tops /\
  supported_place_type tops ret /\
  evaluate_type (type_env tops) ret = SOME tv ==>
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
  strip_tac >> irule return_update_plan_supported_evaluated >> simp[] >>
  gvs[supported_place_type_def] >> metis_tac[]
QED

Theorem return_selected_package_plan:
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
  supported_place_type tops ret /\ ret <> NoneT /\
  evaluate_type (type_env tops) ret = SOME tv /\
  set_external_package_target target
    (package_external_fn tops F nkey_map
      (mut,F,rr,fname,args,[],ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut,iv,fbody,rt) /\
  compile_register_positional_args cenv0 pos_args off st = (cenv,sa) ==>
  abi_enc_plan (type_env tops)
    (if needs_external_call_wrap ret /\
        is_dynamic (vyper_to_abi_type (type_env tops) ret)
     then TupleT [ret] else ret) cenv.ce_ret_enc_info /\
  vyper_abi_size_bound (type_env tops)
    (if needs_external_call_wrap ret /\
        is_dynamic (vyper_to_abi_type (type_env tops) ret)
     then TupleT [ret] else ret) = cenv.ce_max_return_size
Proof
  strip_tac >> drule_all return_selected_frame_encoding >> strip_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac `update_cenv_ret_abi bcenv ret` >>
  `bcenv.ce_struct_fields = make_struct_fields_map tops` by
    simp[Abbr `bcenv`, build_compile_env_ce_struct_fields] >>
  drule_all return_update_plan_supported_place >> simp[]
QED

Theorem return_same_frame_plan:
  same_frame cenv cenv' /\ abi_enc_plan env ty cenv.ce_ret_enc_info ==>
  abi_enc_plan env ty cenv'.ce_ret_enc_info
Proof
  strip_tac >> drule return_same_frame_metadata >> simp[]
QED

Theorem return_same_frame_capacity:
  same_frame cenv cenv' /\ vyper_abi_size_bound env ty <= cenv.ce_max_return_size ==>
  vyper_abi_size_bound env ty <= cenv'.ce_max_return_size
Proof
  strip_tac >> drule return_same_frame_metadata >> simp[]
QED

Theorem return_source_type_keys:
  source_typing_ok tops am tx ==>
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops))
Proof
  rw[source_typing_ok_def, check_contract_def] >>
  drule contract_namespaces_ok_module_type_def_keys >> simp[]
QED

Theorem return_supported_selected_plan:
  supported_program tops /\ source_typing_ok tops am tx /\
  lookup_function NONE fname External tops = SOME (mut,F,args,[],ret,fbody) /\
  ret <> NoneT /\ evaluate_type (type_env tops) ret = SOME tv /\
  set_external_package_target target
    (package_external_fn tops F nkey_map
      (mut,F,rr,fname,args,[],ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut,iv,fbody,rt) /\
  compile_register_positional_args cenv0 pos_args off st = (cenv,sa) ==>
  abi_enc_plan (type_env tops)
    (if needs_external_call_wrap ret /\
        is_dynamic (vyper_to_abi_type (type_env tops) ret)
     then TupleT [ret] else ret) cenv.ce_ret_enc_info /\
  vyper_abi_size_bound (type_env tops)
    (if needs_external_call_wrap ret /\
        is_dynamic (vyper_to_abi_type (type_env tops) ret)
     then TupleT [ret] else ret) <= cenv.ce_max_return_size
Proof
  strip_tac >> drule return_source_type_keys >> strip_tac >>
  drule_all return_selected_external_support >> strip_tac >> gvs[] >>
  drule_all return_selected_package_plan >> simp[]
QED

Theorem return_decl_from_headers[local]:
  !tops tops0 name mut nr args dflts ret fbody.
    EVERY (supported_declaration_header tops0) tops /\
    lookup_function NONE name External tops =
      SOME (mut,nr,args,dflts,ret,fbody) ==>
    ?raw. MEM (FunctionDecl External mut nr raw name args dflts ret fbody) tops
Proof
  Induct >- simp[lookup_function_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `h` >> gvs[supported_declaration_header_def, lookup_function_def] >>
  BasicProvers.every_case_tac >> gvs[lookup_function_def, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem return_selected_type_evaluates:
  supported_program tops /\ source_typing_ok tops am tx /\
  lookup_function NONE fname External tops = SOME (mut,F,args,[],ret,fbody) ==>
  ?tv. evaluate_type (type_env tops) ret = SOME tv
Proof
  strip_tac >>
  `?raw. MEM (FunctionDecl External mut F raw fname args [] ret fbody) tops` by
    (irule return_decl_from_headers >>
     gvs[supported_program_def, supported_declaration_headers_def] >> metis_tac[]) >>
  gvs[source_typing_ok_def] >>
  `module_allocated am.layouts tx.target NONE tops` by
    (fs[check_contract_def, main_module_allocated_def]) >>
  `check_function_body am.layouts tx.target [(NONE,tops)] art NONE External
     mut F args [] ret fbody` by
    (irule check_contract_runtime_function_body_MEM >> simp[] >> metis_tac[]) >>
  gvs[check_function_body_def, IS_SOME_EXISTS] >>
  gvs[vyperContextTheory.type_env_all_modules_def, vyperContextTheory.type_env_def]
QED

Theorem return_selected_plan:
  supported_program tops /\ source_typing_ok tops am tx /\
  lookup_function NONE fname External tops = SOME (mut,F,args,[],ret,fbody) /\
  ret <> NoneT /\
  set_external_package_target target
    (package_external_fn tops F nkey_map
      (mut,F,rr,fname,args,[],ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut,iv,fbody,rt) /\
  compile_register_positional_args cenv0 pos_args off st = (cenv,sa) ==>
  abi_enc_plan (type_env tops)
    (if needs_external_call_wrap ret /\
        is_dynamic (vyper_to_abi_type (type_env tops) ret)
     then TupleT [ret] else ret) cenv.ce_ret_enc_info /\
  vyper_abi_size_bound (type_env tops)
    (if needs_external_call_wrap ret /\
        is_dynamic (vyper_to_abi_type (type_env tops) ret)
     then TupleT [ret] else ret) <= cenv.ce_max_return_size
Proof
  strip_tac >> drule_all return_selected_type_evaluates >> strip_tac >>
  drule_all return_supported_selected_plan >> simp[]
QED
