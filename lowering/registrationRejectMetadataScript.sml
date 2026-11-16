(* Typed metadata for a calldata-selected package, without successful-call
   argument binding or body correctness. *)
Theory registrationRejectMetadata
Ancestors
  entryExternalParameterAdmissibility entryStateRel entryDecodePlanProps entryDispatchProps registrationSizeAdmissibility
  abiCallerBuiltinInput abiDecoderCoherence calldataSourceSize
  vyperTypeSystem vyperTypeContract vyperTypeContractContext
  compileVyper compileEnv moduleLowering supportedProgram list rich_list words
  vyperMisc vyperTypeArgFits

Theorem registration_abi_head_bound[local]:
  !ts sf. SUM (MAP (abi_embedded_static_size sf) ts) <=
    abi_size_bound sf (TupleT ts)
Proof
  Induct >- simp[abi_size_bound_def] >> rpt gen_tac >>
  rename1 `head::tail` >>
  first_x_assum (qspec_then `sf` mp_tac) >>
  simp[abi_size_bound_def] >>
  Cases_on `is_abi_dynamic sf head` >> simp[]
QED

(* Allocation bounds depend on classified argument layout, not the package's
   raw-return flag. Keep that flag independent for the lookup corollary. *)
Theorem registration_reject_member_package_inputs[local]:
  lower_vyper_runtime_unit tops policy = SOME unit /\
  supported_program tops /\ source_typing_ok tops am tx /\
  MEM (mut,nr,rawret,name,args,[],ret,fbody) (FST (classify_functions tops)) /\
  lookup_function NONE name External tops = SOME (mut,nr,args,[],ret,fbody) /\
  set_external_package_target policy.rpol_target
    (package_external_fn tops ut nk (mut,nr,rr,name,args,[],ret,fbody)) =
    (lbl,ce,pos,mincd,pay,nr',key,ut',iv,fbody',rt) ==>
  ALL_DISTINCT (MAP FST args) /\ pos = build_positional_args ce args /\
  ?tvs. OPT_MMAP (evaluate_type (type_env tops)) (MAP SND args) = SOME tvs /\
    mincd = 4 + SUM (MAP tv_abi_size tvs) /\ mincd < dimword (:256) /\
    LIST_REL (\(argname,ty) (ty',tv). ty = ty' /\
      abi_decoder_coherent ce (type_env tops) ce.ce_struct_fields ty tv /\
      (?loc. FLOOKUP ce.ce_vars argname = SOME loc /\
        var_location_memory_size loc = SOME (type_memory_size tv)) /\
      type_memory_size tv < dimword (:256)) args (ZIP (MAP SND args,tvs))
Proof
  strip_tac >>
  `supported_declaration_headers tops` by fs[supported_program_def] >>
  drule_all source_typing_ok_external_params_ok >> strip_tac >>
  `ALL_DISTINCT (MAP FST args)` by fs[params_ok_def] >>
  `ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops))` by
    metis_tac[source_typing_ok_type_def_keys_distinct] >>
  `contract_namespaces_ok F [((NONE:num option),tops)]` by
    (fs[e2eDefsTheory.source_typing_ok_def] >>
     drule check_contract_namespaces_ok >> simp[]) >>
  `?tvs. LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv)
     (MAP SND args) tvs` by suspend "evaluate" >>
  `?rawce rawpos rest. package_external_fn tops ut nk
    (mut,nr,rr,name,args,[],ret,fbody) = (lbl,rawce,rawpos,rest) /\
    ce = rawce with ce_target := policy.rpol_target /\ pos = rawpos` by
    suspend "raw_package" >>
  drule_all package_external_fn_dec_cenv_agrees >> strip_tac >>
  drule_all package_external_fn_vars >> strip_tac >>
  `pos = build_positional_args ce args` by
    (gvs[] >> irule build_positional_args_layout_cong >> simp[]) >>
  asm_rewrite_tac [] >> qexists_tac `tvs` >>
  conj_tac >- suspend "opt_mmap" >>
  `LIST_REL (\(nm,ty) tv. abi_decoder_coherent ce (type_env tops)
     ce.ce_struct_fields ty tv) args tvs` by suspend "coherent" >>
  conj_tac >- suspend "head_eq" >>
  conj_tac >- suspend "head_bound" >>
  suspend "parameters"
QED

Resume registration_reject_member_package_inputs[evaluate]:
  irule well_formed_types_evaluate >>
  gvs[params_ok_def, EVERY_MAP, EVERY_MEM, pairTheory.FORALL_PROD] >>
  metis_tac[assignable_type_well_formed]
QED
Resume registration_reject_member_package_inputs[raw_package]:
  Cases_on `package_external_fn tops ut nk (mut,nr,rr,name,args,[],ret,fbody)` >>
  PairCases_on `r` >> gvs[set_external_package_target_def]
QED
Resume registration_reject_member_package_inputs[opt_mmap]:
  simp[OPT_MMAP_SOME_IFF, EVERY_MAP, EVERY_EL, LIST_EQ_REWRITE] >>
  fs[LIST_REL_EL_EQN, EL_MAP] >> rpt strip_tac >>
  first_x_assum (drule_then assume_tac) >> gvs[]
QED
Resume registration_reject_member_package_inputs[coherent]:
  `ce.ce_struct_fields =
     (build_compile_env tops External mut name args ret fbody ut).ce_struct_fields /\
   ce.ce_flag_n_members =
     (build_compile_env tops External mut name args ret fbody ut).ce_flag_n_members` by
    (Cases_on `ret = NoneT` >>
     gvs[package_external_fn_def, set_external_package_target_def,
         update_cenv_nonreentrant_def, update_cenv_ret_abi_def]) >>
  fs[LIST_REL_EL_EQN] >> rpt strip_tac >>
  Cases_on `EL n args` >> rename1 `EL n args = (argname,ty)` >> simp[] >>
  `assignable_type (type_env tops) ty` by
    (fs[params_ok_def, EVERY_MEM] >>
     qpat_x_assum `!e. MEM e args ==> (\(nm,t). assignable_type _ t) e`
       (qspec_then `(argname,ty)` mp_tac) >> simp[] >>
     metis_tac[EL_MEM]) >>
  `evaluate_type (type_env tops) ty = SOME (EL n tvs)` by
    (qpat_x_assum `!n. n < LENGTH args ==> _` (qspec_then `n` mp_tac) >>
     simp[EL_MAP]) >>
  irule abi_decoder_coherent_layout_transport >>
  qexists_tac `build_compile_env tops External mut name args ret fbody ut` >>
  gvs[] >> irule abi_caller_coherent >> metis_tac[]
QED
Resume registration_reject_member_package_inputs[head_eq]:
  `mincd = 4 + SUM (MAP (\(nm,ty).
      abi_embedded_static_size ce.ce_struct_fields ty) args)` by
    (Cases_on `ret = NoneT` >>
     gvs[package_external_fn_def, set_external_package_target_def,
         update_cenv_nonreentrant_def, update_cenv_ret_abi_def,
         min_calldata_size_def]) >>
  asm_rewrite_tac [] >> AP_TERM_TAC >> AP_TERM_TAC >>
  simp[LIST_EQ_REWRITE] >> fs[LIST_REL_EL_EQN] >> rpt strip_tac >>
  Cases_on `EL x args` >> rename1 `EL x args = (nm,ty)` >>
  qpat_x_assum `!n. n < LENGTH args ==> (\(nm,ty) tv. _) _ _`
    (qspec_then `x` mp_tac) >> simp[] >> strip_tac >>
  drule calldata_coherent_embedded_size >> gvs[EL_MAP]
QED
Resume registration_reject_member_package_inputs[head_bound]:
  Cases_on `classify_functions tops` >> rename1 `classify_functions tops = (exts,more)` >>
  PairCases_on `more` >>
  `fn_allocs_ok tops (mut,nr,rawret,name,args,[],ret,fbody)` by
    (irule lower_vyper_runtime_unit_allocs_ok >> fs[] >> metis_tac[]) >>
  `ce.ce_struct_fields = make_struct_fields_map tops` by
    (Cases_on `ret = NoneT` >>
     gvs[package_external_fn_def, set_external_package_target_def,
         update_cenv_nonreentrant_def, update_cenv_ret_abi_def,
         build_compile_env_ce_struct_fields]) >>
  `mincd = 4 + SUM (MAP (abi_embedded_static_size ce.ce_struct_fields)
                           (MAP SND args))` by
    (Cases_on `ret = NoneT` >>
     gvs[package_external_fn_def, set_external_package_target_def,
         update_cenv_nonreentrant_def, update_cenv_ret_abi_def,
         min_calldata_size_def, MAP_COMPOSE, combinTheory.o_DEF,
         pairTheory.LAMBDA_PROD]) >>
  qspecl_then [`MAP SND args`,`ce.ce_struct_fields`] assume_tac
    registration_abi_head_bound >>
  gvs[fn_allocs_ok_def, build_compile_env_ce_struct_fields, dimword_def] >>
  decide_tac
QED
Resume registration_reject_member_package_inputs[parameters]:
  Cases_on `classify_functions tops` >> rename1 `classify_functions tops = (exts,more)` >>
  PairCases_on `more` >>
  `fn_allocs_ok tops (mut,nr,rawret,name,args,[],ret,fbody)` by
    (irule lower_vyper_runtime_unit_allocs_ok >> fs[] >> metis_tac[]) >>
  fs[LIST_REL_EL_EQN] >>
  rpt strip_tac >> simp[EL_ZIP, EL_MAP] >>
  Cases_on `EL n args` >> rename1 `EL n args = (argname,ty)` >> simp[] >>
  `evaluate_type (type_env tops) ty = SOME (EL n tvs)` by
    (qpat_x_assum `!n. n < LENGTH tvs ==> evaluate_type _ _ = _`
       (qspec_then `n` mp_tac) >> simp[EL_MAP]) >>
  `abi_decoder_coherent ce (type_env tops) ce.ce_struct_fields ty (EL n tvs)` by
    (qpat_x_assum `!n. n < LENGTH args ==> (\(nm,ty) tv. _) _ _`
       (qspec_then `n` mp_tac) >> simp[]) >>
  `type_memory_bytes rawce ty = type_memory_size (EL n tvs)` by
    metis_tac[dec_cenv_agrees_def] >>
  `?off. FLOOKUP rawce.ce_vars argname =
      SOME (MemLoc off (type_memory_size (EL n tvs)))` by
    (qpat_x_assum `EVERY _ args` mp_tac >> simp[EVERY_MEM] >>
     disch_then (qspec_then `(argname,ty)` mp_tac) >>
     simp[] >> metis_tac[EL_MEM]) >>
  `type_memory_size (EL n tvs) < 2 ** 64` by
    (irule registration_parameter_memory_limit >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[EL_MEM]) >>
  gvs[var_location_memory_size_def, dimword_def]
QED
Finalise registration_reject_member_package_inputs

Theorem registration_reject_classified_package_inputs:
  lower_vyper_runtime_unit tops policy = SOME unit /\
  supported_program tops /\ source_typing_ok tops am tx /\
  MEM (mut,nr,rr,name,args,[],ret,fbody) (FST (classify_functions tops)) /\
  lookup_function NONE name External tops = SOME (mut,nr,args,[],ret,fbody) /\
  set_external_package_target policy.rpol_target
    (package_external_fn tops ut nk (mut,nr,rr,name,args,[],ret,fbody)) =
    (lbl,ce,pos,mincd,pay,nr',key,ut',iv,fbody',rt) ==>
  ALL_DISTINCT (MAP FST args) /\ pos = build_positional_args ce args /\
  ?tvs. OPT_MMAP (evaluate_type (type_env tops)) (MAP SND args) = SOME tvs /\
    mincd = 4 + SUM (MAP tv_abi_size tvs) /\ mincd < dimword (:256) /\
    LIST_REL (\(argname,ty) (ty',tv). ty = ty' /\
      abi_decoder_coherent ce (type_env tops) ce.ce_struct_fields ty tv /\
      (?loc. FLOOKUP ce.ce_vars argname = SOME loc /\
        var_location_memory_size loc = SOME (type_memory_size tv)) /\
      type_memory_size tv < dimword (:256)) args (ZIP (MAP SND args,tvs))
Proof
  strip_tac >> irule registration_reject_member_package_inputs >>
  metis_tac[]
QED

Theorem registration_reject_package_inputs:
  lower_vyper_runtime_unit tops policy = SOME unit /\
  supported_program tops /\ source_typing_ok tops am tx /\
  name <> "__default__" /\
  lookup_function NONE name External tops = SOME (mut,nr,args,[],ret,fbody) /\
  set_external_package_target policy.rpol_target
    (package_external_fn tops ut nk (mut,nr,rr,name,args,[],ret,fbody)) =
    (lbl,ce,pos,mincd,pay,nr',key,ut',iv,fbody',rt) ==>
  ALL_DISTINCT (MAP FST args) /\ pos = build_positional_args ce args /\
  ?tvs. OPT_MMAP (evaluate_type (type_env tops)) (MAP SND args) = SOME tvs /\
    mincd = 4 + SUM (MAP tv_abi_size tvs) /\ mincd < dimword (:256) /\
    LIST_REL (\(argname,ty) (ty',tv). ty = ty' /\
      abi_decoder_coherent ce (type_env tops) ce.ce_struct_fields ty tv /\
      (?loc. FLOOKUP ce.ce_vars argname = SOME loc /\
        var_location_memory_size loc = SOME (type_memory_size tv)) /\
      type_memory_size tv < dimword (:256)) args (ZIP (MAP SND args,tvs))
Proof
  strip_tac >>
  `supported_declaration_headers tops` by fs[supported_program_def] >>
  drule_all supported_headers_external_member >> strip_tac >>
  irule registration_reject_member_package_inputs >>
  metis_tac[]
QED
