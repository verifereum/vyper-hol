(* Signature provenance and typed selected-package metadata for NONE dispatch. *)
Theory calldataNoneMetadata
Ancestors
  registrationRejectMetadata entryExternalParameterAdmissibility
  checkedSelectorTableProps loweringShapeProps entryDispatchProps
  supportedProgram supportedDecls e2eDefs vyperTypeContract
  vyperTypeContractContext vyperTypeSystem publicGetterProps constSubst
  compileVyper vyperABIEntries vyperMisc vyperTypeArgFits list sorting

Theorem none_signature_evaluates:
  supported_program tops /\ source_typing_ok tops am tx /\
  MEM (name,tys) (abi_external_signatures tops) ==>
  ?mut nr rr args ret fbody tvs.
    MEM (mut,nr,rr,name,args,[],ret,fbody) (FST (classify_functions tops)) /\
    tys = MAP SND args /\
    OPT_MMAP (evaluate_type (type_env tops)) tys = SOME tvs
Proof
  strip_tac >>
  `MEM (name,tys)
    (FLAT (MAP (\(mut,nr,rr,n,args,ds,ret,body).
       abi_function_signatures n args ds) (FST (classify_functions tops))))` by
    (rewrite_tac[classify_external_signatures] >>
     metis_tac[abi_signature_partition, PERM_MEM_EQ]) >>
  pop_assum mp_tac >>
  simp[MEM_FLAT, MEM_MAP, PULL_EXISTS, pairTheory.EXISTS_PROD] >>
  rpt strip_tac >>
  `~EXISTS external_has_defaults (FST (classify_functions tops))` by
    metis_tac[supported_program_no_external_defaults] >>
  fs[EVERY_MEM, external_has_defaults_def, combinTheory.o_DEF] >>
  suspend "signature"
QED

Resume none_signature_evaluates[signature]:
  qpat_x_assum `!e. MEM e _ ==> _` drule >>
  simp[external_has_defaults_def, NULL_EQ] >> strip_tac >> gvs[] >>
  gvs[abi_function_signatures_no_defaults] >>
  rename1 `MEM (mut,nr,rr,name,args,[],ret,fbody) _` >>
  `lookup_function NONE name External tops =
     SOME (mut,nr,args,[],ret,fbody)` by suspend "lookup" >>
  `supported_declaration_headers tops` by fs[supported_program_def] >>
  drule_all source_typing_ok_external_params_ok >> strip_tac >>
  `?tvs. LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv)
     (MAP SND args) tvs` by
    (irule well_formed_types_evaluate >>
     gvs[params_ok_def, EVERY_MAP, EVERY_MEM, pairTheory.FORALL_PROD] >>
     metis_tac[assignable_type_well_formed]) >>
  qexistsl_tac [`mut`,`nr`,`rr`,`args`,`ret`,`fbody`,`tvs`] >>
  simp[] >>
  simp[OPT_MMAP_SOME_IFF, EVERY_MAP, EVERY_EL, LIST_EQ_REWRITE] >>
  fs[LIST_REL_EL_EQN, EL_MAP] >> rpt strip_tac >>
  first_x_assum (drule_then assume_tac) >> gvs[]
QED
Resume none_signature_evaluates[lookup]:
  `module_consts_env tops [] = []` by
    metis_tac[supported_headers_module_consts_env,
      supported_program_def, supported_declaration_headers_def] >>
  `ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) tops))` by
    (fs[source_typing_ok_def] >>
     drule check_contract_external_names_distinct >> simp[contract_keys_def]) >>
  drule classify_functions_external_source >> strip_tac >>
  gvs[subst_consts_fn_empty]
  >- (irule lookup_function_external_unique_decl >> simp[] >>
      qexists_tac `FunctionDecl External mut nr rr name args [] ret fbody` >>
      simp[vyperInterpreterTheory.lookup_function_def,
           external_name_keys_toplevel_def]) >>
  drule public_getter_lookup_singleton >> strip_tac >>
  metis_tac[lookup_function_external_unique_decl]
QED
Finalise none_signature_evaluates

(* Fix the decoder's evaluated list before using the package resources. *)
Theorem none_selected_package_metadata:
  lower_vyper_runtime_unit tops policy = SOME unit /\
  supported_program tops /\ source_typing_ok tops am tx /\
  MEM (mut,nr,rr,name,args,[],ret,fbody) (FST (classify_functions tops)) /\
  lookup_function NONE name External tops = SOME (mut,nr,args,[],ret,fbody) /\
  OPT_MMAP (evaluate_type (type_env tops)) (MAP SND args) = SOME tvs /\
  set_external_package_target policy.rpol_target
    (package_external_fn tops ut nk (mut,nr,rr,name,args,[],ret,fbody)) =
    (lbl,ce,pos,mincd,pay,nr',key,ut',iv,fbody',rt) ==>
  ALL_DISTINCT (MAP FST args) /\ pos = build_positional_args ce args /\
  mincd = 4 + SUM (MAP tv_abi_size tvs) /\ mincd < dimword (:256) /\
  LIST_REL (\(argname,ty) (ty',tv). ty = ty' /\
    abi_decoder_coherent ce (type_env tops) ce.ce_struct_fields ty tv /\
    (?loc. FLOOKUP ce.ce_vars argname = SOME loc /\
      var_location_memory_size loc = SOME (type_memory_size tv)) /\
    type_memory_size tv < dimword (:256)) args (ZIP (MAP SND args,tvs))
Proof
  strip_tac >> drule_all registration_reject_classified_package_inputs >>
  strip_tac >> gvs[]
QED
