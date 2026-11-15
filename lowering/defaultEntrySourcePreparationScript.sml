(* Source and package facts at the caller's evaluated type witnesses. *)
Theory defaultEntrySourcePreparation
Ancestors
  defaultDispatchFacts defaultGetterArguments entryParameterAdmissibility
  entryRuntimePackageLayout entryRuntimeStateBoundary vyperTypeContractContext
  vyperLoweringCorrect entryStateRel list

Theorem default_entry_source_preparation:
  supported_program tops /\ source_typing_ok tops am tx /\
  tx.function_name = "__default__" /\
  initial_venom_state_rel tops am tx vs /\
  calldata_dispatch tops vs.vs_call_ctx.cc_calldata =
    SOME (tx.function_name,tx.args) /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,F,args,[],ret,fbody) /\
  OPT_MMAP (evaluate_type (type_env tops)) (MAP SND args) = SOME tvs ==>
  ALL_DISTINCT (MAP FST args) /\
  contract_namespaces_ok F [(NONE,tops)] /\
  LIST_REL (\(name,ty) tv.
    assignable_type (type_env tops) ty /\
    evaluate_type (type_env tops) ty = SOME tv /\
    (is_word_type ty \/ is_bytestring_type ty)) args tvs /\
  SUM (MAP tv_abi_size tvs) <= LENGTH (DROP 4 vs.vs_call_ctx.cc_calldata) /\
  LENGTH vs.vs_call_ctx.cc_calldata < dimword (:256) /\
  (MEM (mut,F,lookup_raw_return_or_F (NONE:num option) tx.function_name External tops,
       tx.function_name,args,([]:expr list),ret,fbody) (FST (classify_functions tops)) \/
   FST (SND (SND (classify_functions tops))) =
     SOME (mut,F,lookup_raw_return_or_F (NONE:num option) tx.function_name External tops,
       tx.function_name,args,([]:expr list),ret,fbody))
Proof
  strip_tac >>
  drule_all selected_external_params_ok >>
  simp[vyperTypeContractTheory.params_ok_def] >> strip_tac >>
  `contract_namespaces_ok F [(NONE,tops)]` by
    (gvs[e2eDefsTheory.source_typing_ok_def] >>
     metis_tac[check_contract_namespaces_ok]) >>
  `LENGTH vs.vs_call_ctx.cc_calldata < dimword (:256)` by
    metis_tac[initial_venom_state_calldata_length] >>
  `EVERY (\a. is_word_type (SND a) \/ is_bytestring_type (SND a)) args` by
    (`ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) tops))` by
       metis_tac[source_typing_ok_external_names_distinct] >>
     drule default_dispatch_raw_cases >>
     disch_then (DISJ_CASES_THEN2 assume_tac strip_assume_tac)
     >- (gvs[] >> metis_tac[default_fallback_no_args, EVERY_DEF]) >>
     `MEM ("__default__",tys) (abi_external_signatures tops)` by
       metis_tac[venomInstTheory.FIND_MEM] >>
     gvs[] >> drule_all default_selected_source_args >> strip_tac >>
     drule_all default_getter_argument_types >> simp[]) >>
  `LIST_REL (\(name,ty) tv.
    assignable_type (type_env tops) ty /\
    evaluate_type (type_env tops) ty = SOME tv /\
    (is_word_type ty \/ is_bytestring_type ty)) args tvs` by
    (drule vyperTypeABITheory.OPT_MMAP_LIST_REL >>
     simp[LIST_REL_EL_EQN, EVERY_EL, EL_MAP] >> strip_tac >>
     rpt strip_tac >>
     gvs[EVERY_EL] >>
     qpat_x_assum `!n'. _ ==> (\(_0,ty). _) _`
       (qspec_then `n` mp_tac) >>
     Cases_on `EL n args` >> gvs[] >>
     metis_tac[pairTheory.SND]) >>
  gvs[] >> drule_all default_dispatch_source_cases >>
  strip_tac >> gvs[LENGTH_DROP]
QED

Theorem default_entry_package_preparation:
  supported_program tops /\ source_typing_ok tops am tx /\
  source_deployment_rel tops am tx /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,F,args,[],ret,fbody) /\
  set_external_package_target target
    (package_external_fn tops T keys
      (mut,F,rr,tx.function_name,args,([]:expr list),ret,fbody)) =
    (lbl,ce,pa,mc,pay,F,key,ut,view,fbody,rt) ==>
  ce.ce_module = NONE /\ ~ce.ce_is_ctor /\ ce.ce_imm_alloca = NONE /\
  ce.ce_return_pc = NONE /\ ce.ce_return_buf = NONE /\
  storage_vars_rel ce (initial_evaluation_context am.sources am.layouts tx NONE) /\
  transient_vars_rel ce (initial_evaluation_context am.sources am.layouts tx NONE) /\
  immutable_section_layout ce tops
Proof
  strip_tac >>
  drule targeted_external_package_layout >> strip_tac >>
  `ALL_DISTINCT (MAP FST args)` by
    (drule_all selected_external_params_ok >>
     simp[vyperTypeContractTheory.params_ok_def]) >>
  `ce.ce_module_vars = add_immutable_locations
    (get_struct_fields (make_struct_fields_map tops)) tops 0
    (add_module_var_locations tops FEMPTY)` by
    (Cases_on `package_external_fn tops T keys
       (mut,F,rr,tx.function_name,args,([]:expr list),ret,fbody)` >>
     PairCases_on `r` >> gvs[compileVyperTheory.set_external_package_target_def] >>
     drule_all package_external_fn_vars >> simp[]) >>
  `ce.ce_return_pc = NONE` by
    (qpat_x_assum `set_external_package_target _ _ = _` mp_tac >>
     gvs[compileVyperTheory.set_external_package_target_def,
       compileVyperTheory.package_external_fn_def,
       compileVyperTheory.update_cenv_nonreentrant_def] >>
     rw[compileVyperTheory.update_cenv_ret_abi_def] >>
     gvs[compileVyperTheory.build_compile_env_def] >>
     rpt (pairarg_tac >> gvs[])) >>
  `storage_vars_rel ce (initial_evaluation_context am.sources am.layouts tx NONE) /\
   transient_vars_rel ce (initial_evaluation_context am.sources am.layouts tx NONE)` by
    (irule runtime_entry_storage_vars_rel >> simp[] >>
     qexistsl_tac [`am`,`tops`,`tx`] >>
     simp[vyperInterpreterTheory.initial_evaluation_context_def] >>
     metis_tac[source_typing_ok_vtype_keys_distinct,
       supportedProgramTheory.supported_program_def]) >>
  simp[]
QED
