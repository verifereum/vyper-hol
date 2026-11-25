(* A piece of S1 (loweringRuntimeCorrect's lower_vyper_runtime_unit_correct). *)
Theory externalBodyFrame
Ancestors
  entryDispatchProps constSubst constSubstCorrect constSubstStmts constSubstStmtsPreserve
  bodyFullPreds gasContext supportedGetterProps externalRawReturnType externalReturnPackage externalEntryBound
  externalBodyWidths externalBodySupport memoryLocalRhsProps
  bodyQualifiedStmtSupport linkedConstAnnotations constSubstMods
  stmtSimProps stmtSimDefs exprSimDefs exprSimHypsDefs exprSimHyps
  loweringPosts
  list pair finite_map alist arithmetic combin integer option pred_set rich_list
  fragExec bodySim bodySimEntry bodySimStmtFacts
  bodyInvSplit bodyInvCodeProps bodyInvExecutionProps bodyInvIntCallPinsProps compileUnit
  loweringHalt stmtLoweringMono exprLoweringProps
  compileEnv compileVyper moduleLowering stmtLowering exprLowering
  e2eDefs supportedProgram supportedProgramProps supportedDecls supportedNames
  supportedStmts supportedExprs supportedTypes
  supportedExprTraverse supportedStmtTraverse allocLimits allocLimitsProps
  vyperLoweringCorrect rawReturnHeader immutableSectionRel immutableLocationProps
  placeTypingBuildProps entryDecodePlanProps structFieldsProps entryStateRel
  typedCopyProducer typedCopyMetadata
  vyperTypeSelectedEntrySoundness vyperTypeSystem vyperTypeStmtSoundness
  vyperTypeEvalSoundness vyperTypeExprSoundness vyperTypeInvariants
  vyperTypeContractFunction vyperTypeContractSoundness vyperTypeContractContext
  vyperTypeContract vyperTypeContractStaticMaps vyperTypeExternalDefaults
  vyperTypeContractGetter vyperGetter
  vyperTypeInitialState vyperTypeBindArguments
  vyperTypeEvalStoragePreservation vyperTypeStoragePreservation
  vyperStorageLayoutSafety vyperStorageBackend vyperPlaceInvariants
  vyperInterpreter vyperState vyperContext
  venomState venomExecSemantics venomWf

val _ = Parse.hide "body";

Theorem collect_locals_supported_bindings_mem:
  !ss n. MEM n (MAP FST (collect_locals ss)) <=>
    MEM n (MAP FST (supported_stmts_bindings T ss)) \/
    MEM n (MAP FST (supported_stmts_bindings F ss))
Proof
  recInduct collect_locals_ind >>
  simp[collect_locals_def, supported_stmt_bindings_def] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem supported_function_arg_not_collect_locals:
  supported_function_body tops vis args ss /\ MEM (id,ty) args ==>
  ~MEM id (MAP FST (collect_locals ss))
Proof
  strip_tac >> drule supported_function_body_binding_contract >>
  simp[EVERY_MEM, collect_locals_supported_bindings_mem] >> strip_tac >>
  `MEM id (MAP FST args)` by (simp[MEM_MAP] >> qexists `(id,ty)` >> simp[]) >>
  metis_tac[]
QED

Theorem supported_function_names_mem:
  !tops vis mut nr rr name args defaults ret body.
    MEM (FunctionDecl vis mut nr rr name args defaults ret body) tops ==>
    MEM name (supported_function_names tops)
Proof
  Induct >> simp[supported_function_names_def] >>
  rpt gen_tac >> Cases_on `h` >> simp[supported_function_names_def] >>
  metis_tac[]
QED

Theorem distinct_classify_fold_fallback[local]:
  !tops mut nr rr args defaults ret body.
    ALL_DISTINCT (supported_function_names tops) /\
    MEM (FunctionDecl External mut nr rr "__default__" args defaults ret body) tops ==>
    FST (SND (SND (FOLDR classify_function ([],[],NONE,NONE) tops))) =
      SOME (mut,nr,rr,"__default__",args,defaults,ret,body)
Proof
  Induct >- simp[] >> rpt gen_tac >>
  simp[Once FOLDR] >>
  qmatch_goalsub_abbrev_tac `classify_function h acc` >>
  PairCases_on `acc` >> fs[] >> Cases_on `h` >>
  simp[supported_function_names_def, classify_function_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  Cases_on `f` >> gvs[] >>
  Cases_on `s = "__default__"` >> gvs[] >>
  metis_tac[supported_function_names_mem]
QED

Theorem distinct_external_classification:
  !tops mut nr rr name args defaults ret body exts ints fb ctor.
    supported_declaration_headers tops /\
    ALL_DISTINCT (supported_function_names tops) /\
    MEM (FunctionDecl External mut nr rr name args defaults ret body) tops /\
    classify_functions tops = (exts,ints,fb,ctor) ==>
    (if name = "__default__" then
       fb = SOME (subst_consts_fn (module_consts_env tops [])
         (mut,nr,rr,name,args,defaults,ret,body))
     else MEM (subst_consts_fn (module_consts_env tops [])
       (mut,nr,rr,name,args,defaults,ret,body)) exts)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `name = "__default__"`
  >- (gvs[] >> drule_all distinct_classify_fold_fallback >>
      qpat_x_assum `classify_functions _ = _` mp_tac >>
      simp[classify_functions_def] >> pairarg_tac >>
      rpt strip_tac >> gvs[]) >>
  drule_all classify_fold_external_member >>
  qpat_x_assum `classify_functions _ = _` mp_tac >>
  simp[classify_functions_def] >> pairarg_tac >>
  rpt strip_tac >> gvs[MEM_MAP] >>
  disj1_tac >> qexists `(mut,nr,rr,name,args,defaults,ret,body)` >>
  simp[]
QED

Theorem supported_external_classification:
  supported_program tops /\
  MEM (FunctionDecl External mut nr rr name args defaults ret fbody) tops /\
  classify_functions tops = (exts,ints,fb,ctor) ==>
  (if name = "__default__" then
     fb = SOME (subst_consts_fn (module_consts_env tops [])
       (mut,nr,rr,name,args,defaults,ret,fbody))
   else MEM (subst_consts_fn (module_consts_env tops [])
      (mut,nr,rr,name,args,defaults,ret,fbody)) exts)
Proof
  strip_tac >> irule distinct_external_classification >>
  drule supported_program_names >>
  simp[supported_declaration_names_def] >>
  gvs[supported_program_def] >> metis_tac[]
QED

Theorem supported_external_allocs_ok:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\
  MEM (FunctionDecl External mut nr rr name args defaults ret fbody) tops ==>
  fn_allocs_ok tops
    (subst_consts_fn (module_consts_env tops []) (mut,nr,rr,name,args,defaults,ret,fbody))
Proof
  strip_tac >> Cases_on `classify_functions tops` >> PairCases_on `r` >>
  drule_all supported_external_classification >> strip_tac >>
  irule lower_vyper_runtime_unit_allocs_ok >>
  conj_tac >- metis_tac[] >>
  qexistsl [`r2`, `q`, `r1`, `r0`] >>
  simp[] >> Cases_on `name = "__default__"` >> gvs[]
QED


Theorem build_compile_env_return_buffer_ok:
  !tops vis mut name args ret body use_trans.
    return_buffer_ok
      (build_compile_env tops vis mut name args ret body use_trans)
Proof
  rpt gen_tac >> simp[build_compile_env_def] >>
  rpt (pairarg_tac >> gvs[]) >> simp[return_buffer_ok_def]
QED

Theorem update_cenv_ret_abi_word_return_buffer_ok:
  !cenv ret. is_word_type ret ==>
    return_buffer_ok (update_cenv_ret_abi cenv ret)
Proof
  Cases_on `ret` >> simp[is_word_type_def] >-
    (Cases_on `b` >>
     simp[is_word_type_def, update_cenv_ret_abi_def, return_buffer_ok_def,
          type_to_abi_enc_info_def, abi_size_bound_def, is_abi_dynamic_def,
          abi_static_size_def, type_memory_bytes_def] >>
     rename1 `BytesT kind` >> Cases_on `kind` >>
     simp[is_word_type_def, update_cenv_ret_abi_def, return_buffer_ok_def,
          type_to_abi_enc_info_def, abi_size_bound_def, is_abi_dynamic_def,
          abi_static_size_def, type_memory_bytes_def]) >>
  simp[update_cenv_ret_abi_def, return_buffer_ok_def,
       type_to_abi_enc_info_def, abi_size_bound_def, is_abi_dynamic_def,
       abi_static_size_def, type_memory_bytes_def]
QED

Theorem package_external_fn_return_buffer_ok:
  !target tops use_trans nkeys mut nr rr name args dflts ret body'
   lbl cenv pos_args min_cds is_payable nr' nkey ut iv body rt.
  set_external_package_target target
    (package_external_fn tops use_trans nkeys
      (mut,nr,rr,name,args,dflts,ret,body')) =
      (lbl,cenv,pos_args,min_cds,is_payable,nr',nkey,ut,iv,body,rt) /\
  external_return_buffer_ok
      (lbl,cenv,pos_args,min_cds,is_payable,nr',nkey,ut,iv,body,rt) ==>
  (stmts_valued_return body /\ ~cenv.ce_raw_return ==>
    return_buffer_ok cenv)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `ret = NoneT`
  >- (qpat_x_assum `external_return_buffer_ok _` kall_tac >>
      `return_buffer_ok
         (build_compile_env tops External mut name args ret body' use_trans)`
        by irule build_compile_env_return_buffer_ok >>
      gvs[package_external_fn_def, set_external_package_target_def,
          update_cenv_nonreentrant_def, return_buffer_ok_def]) >>
  Cases_on `is_word_type ret`
  >- (qpat_x_assum `external_return_buffer_ok _` kall_tac >>
      drule update_cenv_ret_abi_word_return_buffer_ok >>
      disch_then (qspec_then
        `build_compile_env tops External mut name args ret body' use_trans
           with ce_raw_return := rr` mp_tac) >>
      gvs[package_external_fn_def, set_external_package_target_def,
          update_cenv_nonreentrant_def, return_buffer_ok_def]) >>
  gvs[package_external_fn_def, set_external_package_target_def,
      external_return_buffer_ok_def]
QED

Theorem make_struct_fields_map_fields:
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
  (!name args. MEM (StructDecl name args) tops ==>
     ALL_DISTINCT (MAP FST args)) /\
  FLOOKUP (make_struct_fields_map tops) name = SOME fields ==>
  ALL_DISTINCT (MAP FST fields) /\
  EVERY (\(fname,fty,sz). !tv.
    evaluate_type (type_env tops) fty = SOME tv ==>
    sz = type_memory_size tv) fields
Proof
  strip_tac >>
  `struct_args_unique tops` by
    metis_tac[distinct_type_keys_struct_args_unique] >>
  fs[make_struct_fields_map_def] >>
  drule built_struct_fields_origin >> simp[] >> strip_tac >>
  `fields = build_struct_fields_one (type_env tops) args` by
    (drule_all build_struct_fields_map_lookup >>
     disch_then (qspecl_then [`type_env tops`, `FEMPTY`] mp_tac) >> gvs[]) >>
  conj_tac >- metis_tac[built_struct_fields_names] >>
  simp[EVERY_MEM, build_struct_fields_one_def, MEM_MAP, FORALL_PROD,
       PULL_EXISTS, field_mem_bytes_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem checked_single_module_bare_global_no_hashmap:
  check_contract F layouts addr [(NONE,tops)] = SOME art /\
  FLOOKUP art.cta_bare_globals nsid = SOME ty ==>
  build_hashmap_info tops nsid = NONE
Proof
  Cases_on `nsid` >> rw[check_contract_def] >>
  gvs[live_artifact_fields] >>
  drule_all build_contract_type_artifact_bare_globals_sound >>
  strip_tac >> gvs[] >>
  irule build_hashmap_info_variable >>
  gvs[contract_namespaces_ok_def, contract_keys_def] >>
  metis_tac[]
QED

Theorem package_external_target_param_memory:
  set_external_package_target target
    (package_external_fn tops use_trans nkey_map
      (mut,nr,rr,fname,fargs,dflts,ret,fbody)) =
    (lbl,cenv,pos_args,rest) /\ ALL_DISTINCT (MAP FST fargs) ==>
  EVERY (\a. ?off sz. FLOOKUP cenv.ce_vars (FST a) =
                       SOME (MemLoc off sz)) fargs /\
  MAP FST pos_args = MAP FST fargs
Proof
  strip_tac >>
  Cases_on `package_external_fn tops use_trans nkey_map
    (mut,nr,rr,fname,fargs,dflts,ret,fbody)` >>
  PairCases_on `r` >> gvs[set_external_package_target_def] >>
  drule_all package_external_fn_vars >> strip_tac >>
  conj_tac
  >- (gvs[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >>
      metis_tac[]) >>
  qpat_x_assum `package_external_fn _ _ _ _ = _` mp_tac >>
  simp[package_external_fn_def] >> strip_tac >>
  gvs[build_positional_args_names]
QED

Theorem external_entry_target_param_pointer:
  set_external_package_target target
    (package_external_fn tops use_trans nkey_map
      (mut,nr,rr,fname,fargs,dflts,ret,fbody)) =
    (lbl,cenv0,pos_args,rest) /\
  compile_register_positional_args cenv0 pos_args 4 st = (cenv,st') /\
  ALL_DISTINCT (MAP FST fargs) /\ MEM (id,ty) fargs ==>
  ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)
Proof
  strip_tac >> drule_all package_external_target_param_memory >>
  strip_tac >> gvs[EVERY_MEM] >>
  first_x_assum drule >> simp[] >> strip_tac >>
  `MEM id (MAP FST pos_args)` by
    (qpat_x_assum `MAP FST pos_args = _` SUBST1_TAC >>
     simp[MEM_MAP] >> qexists `(id,ty)` >> simp[]) >>
  `var_location_memory_size (MemLoc off sz) = SOME sz` by
    simp[var_location_memory_size_def] >>
  drule_all compile_register_positional_args_ptrs >> metis_tac[]
QED

Theorem external_entry_target_param_type:
  set_external_package_target target
    (package_external_fn tops use_trans nkey_map
      (mut,nr,rr,fname,fargs,dflts,ret,fbody)) =
    (lbl,cenv0,pos_args,rest) /\
  compile_register_positional_args cenv0 pos_args 4 st = (cenv,st') /\
  supported_function_body tops External fargs fbody /\ MEM (id,ty) fargs ==>
  cenv.ce_var_type id = SOME ty
Proof
  strip_tac >>
  `~MEM id (MAP FST (collect_locals fbody))` by
    metis_tac[supported_function_arg_not_collect_locals] >>
  `ALL_DISTINCT (MAP FST fargs)` by
    (drule supported_function_body_binding_contract >> simp[]) >>
  `ALOOKUP (REVERSE fargs) id = SOME ty` by
    (irule ALOOKUP_ALL_DISTINCT_MEM >>
     simp[MAP_REVERSE, ALL_DISTINCT_REVERSE]) >>
  drule compile_register_positional_args_cenv >> strip_tac >>
  `cenv.ce_var_type = cenv0.ce_var_type` by
    (qpat_x_assum `cenv = _` SUBST1_TAC >> simp[]) >>
  qpat_x_assum `cenv.ce_var_type = _` (fn th => rewrite_tac[th]) >>
  qpat_x_assum `compile_register_positional_args _ _ _ _ = _` kall_tac >>
  qpat_x_assum `cenv = _` kall_tac >>
  `ALOOKUP (REVERSE (collect_locals fbody)) id = NONE` by
    simp[ALOOKUP_NONE, MAP_REVERSE] >>
  qpat_x_assum `set_external_package_target _ _ = _` mp_tac >>
  simp[package_external_fn_def, set_external_package_target_def,
       update_cenv_nonreentrant_def, update_cenv_ret_abi_def] >>
  Cases_on `ret = NoneT` >> simp[] >> strip_tac >>
  gvs[build_compile_env_def] >> rpt (pairarg_tac >> gvs[]) >>
  simp[REVERSE_APPEND, ALOOKUP_APPEND]
QED

val external_package_ce_vars_tac =
  `cenv = cenv0 with ce_vars := cenv.ce_vars` by
    fs[compile_env_component_equality];

Theorem external_package_registered_hashmap_info:
  set_external_package_target target
    (package_external_fn tops use_trans nkey_map
      (mut,nr,rr,fname,args,dflts,ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,nr',nkey,ut',iv,fbody',rt) /\
  cenv with ce_vars := cenv0.ce_vars = cenv0 ==>
  cenv.ce_hashmap_info = build_hashmap_info tops
Proof
  strip_tac >>
  external_package_ce_vars_tac >>
  qpat_x_assum `cenv = _` SUBST1_TAC >>
  gvs[package_external_fn_def, set_external_package_target_def] >>
  Cases_on `ret = NoneT` >>
  gvs[update_cenv_nonreentrant_def, update_cenv_ret_abi_def,
      build_compile_env_ce_hashmap_info]
QED

Theorem external_entry_target_declared:
  !tops use_trans nkey_map mut nr rr fname fargs dflts ret fbody
   target lbl cenv0 pos_args rest st cenv st' n l.
    set_external_package_target target
      (package_external_fn tops use_trans nkey_map
        (mut,nr,rr,fname,fargs,dflts,ret,fbody)) =
      (lbl,cenv0,pos_args,rest) /\
    compile_register_positional_args cenv0 pos_args 4 st = (cenv,st') /\
    FLOOKUP cenv.ce_vars n = SOME l ==>
    MEM n (MAP FST fargs)
Proof
  rpt gen_tac >> strip_tac >>
  `cenv0.ce_vars = (build_compile_env tops External mut fname fargs ret fbody
                    use_trans).ce_vars` by
    (gvs[package_external_fn_def, set_external_package_target_def,
         update_cenv_nonreentrant_def] >> rw[update_cenv_ret_abi_def]) >>
  drule_all compile_register_positional_args_bound >> strip_tac >>
  gvs[] >> drule build_compile_env_bound >> simp[]
QED

Theorem external_entry_target_locals_declared:
  set_external_package_target target
    (package_external_fn tops use_trans nkey_map
      (mut,nr,rr,fname,fargs,dflts,ret,fbody)) =
    (lbl,cenv0,pos_args,rest) /\
  compile_register_positional_args cenv0 pos_args 4 st = (cenv,st') /\
  (!id ty. MEM (id,ty) fargs ==> FLOOKUP env.var_types id = SOME ty) ==>
  ce_locals_declared cenv env
Proof
  rw[ce_locals_declared_def] >>
  drule_all external_entry_target_declared >>
  simp[MEM_MAP, PULL_EXISTS] >> strip_tac >>
  PairCases_on `y` >> gvs[] >> strip_tac >> gvs[] >>
  first_x_assum drule >> simp[FLOOKUP_DEF] >> metis_tac[]
QED

(* The packaged external env reads the module's variables and the internal
   functions' return types as build_compile_env does, as fn_allocs_ok_body
   needs. *)
Theorem external_package_alloc_env_agree:
  set_external_package_target target
    (package_external_fn tops T (K global_nonreentrant_slot)
      (mut,nr,rr,fname,args,dflts,ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,nr,nkey,ut',iv,fbody,rt) /\
  cenv with ce_vars := cenv0.ce_vars = cenv0 ==>
  alloc_env_agree (build_compile_env tops Internal mut fname args ret fbody F)
    cenv
Proof
  strip_tac >>
  external_package_ce_vars_tac >>
  qpat_x_assum `cenv = _` SUBST1_TAC >>
  gvs[set_external_package_target_def, package_external_fn_def] >>
  simp[alloc_env_agree_def] >>
  rw[update_cenv_nonreentrant_def, update_cenv_ret_abi_def] >>
  simp[build_compile_env_def] >> rpt (pairarg_tac >> gvs[])
QED

Theorem external_body_support_bounds_from_allocs[local]:
  fn_allocs_ok tops (mut,nr,rr,name,args,defaults,ret,ss) /\
  supported_function_body tops External args ss /\
  cenv.ce_struct_fields = make_struct_fields_map tops /\
  cenv.ce_event_info = build_event_info (type_env tops) tops (K NONE) /\
  alloc_env_agree (build_compile_env tops Internal mut name args ret ss F)
    cenv /\
  env_context_consistent env cx /\
  (!n ty. FLOOKUP env.var_types n = SOME ty ==> MEM (n,ty) args) /\
  EVERY (\(n,ty). assignable_type env.type_defs ty) args /\
  type_stmts env ret ss = SOME env' /\
  ~supported_stmts_expr_exists (const_name_root_mods cenv.ce_modules) ss /\
  qualified_stmts_decls_ok cenv.ce_modules ss /\
  (stmts_valued_return ss /\ cenv.ce_is_external /\ ~cenv.ce_raw_return ==>
   return_buffer_ok cenv) ==>
  locals_alloc_ok cenv env /\ stmts_exprs_ok cenv ss /\
  ?bindings. supported_stmts tops bindings ss
Proof
  disch_then strip_assume_tac >>
  drule_all fn_allocs_ok_body >> strip_tac >>
  `~supported_stmts_expr_exists (\e. ~byte_widths_expr e) ss` by
    (drule_all typed_parameter_body_excludes_bad_widths >> simp[]) >>
  `stmts_exprs_ok cenv ss` by
    (irule stmt_exprs_ok_from_traversal_bounds >> simp[]) >>
  conj_tac
  >- (simp[locals_alloc_ok_def] >> rpt strip_tac >>
      `MEM (id,ty) args` by metis_tac[] >>
      qpat_x_assum `EVERY (\(_,ty). type_memory_bytes cenv ty < _) args` mp_tac >>
      simp[EVERY_MEM] >>
      disch_then (qspec_then `(id,ty)` mp_tac) >> simp[]) >>
  gvs[supported_function_body_def] >> metis_tac[]
QED

Theorem external_bind_arguments_popped:
  !args tenv vals env.
    bind_arguments tenv args vals = SOME env ==>
    popped_keys_indexed [env]
Proof
  Induct >> simp[Once bind_arguments_def]
  >- (Cases_on `vals` >>
      simp[bind_arguments_def, popped_keys_indexed_def]) >>
  Cases_on `h` >> Cases_on `vals` >>
  simp[Once bind_arguments_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >> first_x_assum drule >>
  simp[popped_keys_indexed_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[AllCaseEqs(), popped_history_typed_def] >>
  metis_tac[]
QED

Theorem external_selected_args_distinct:
  supported_program tops /\ source_typing_ok tops am tx /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,dflts,ret,fbody) ==>
  ALL_DISTINCT (MAP FST args)
Proof
  strip_tac >>
  `supported_declaration_headers tops` by fs[supported_program_def] >>
  drule_all source_typing_ok_params_ok >> simp[params_ok_def]
QED

Theorem external_package_body_inv:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\ source_typing_ok tops am tx /\
  source_deployment_rel tops am tx /\
  set_external_package_target rpolicy.rpol_target
    (package_external_fn tops T (K global_nonreentrant_slot)
      (mut,nr,rr,tx.function_name,args,dflts,ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,nr,nkey,ut',iv,fbody,rt) /\
  cenv with ce_vars := cenv0.ce_vars = cenv0 ==>
  body_inv tops unit.cu_context cenv
    (initial_evaluation_context am.sources am.layouts tx NONE) /\
  cenv.ce_return_pc = NONE
Proof
  strip_tac >>
  `!v0 m0 n0 r0 f0 a0 d0 t0 b0.
     MEM (FunctionDecl v0 m0 n0 r0 f0 a0 d0 t0 b0) tops ==>
     function_mutability_ok [(NONE, tops)] v0 m0 n0 d0 b0` by
    (gvs[source_typing_ok_def] >>
     metis_tac[bodySimTheory.check_contract_function_mutability_ok]) >>
  `acyclic_struct_metadata (make_struct_fields_map tops)` by
    (gvs[source_typing_ok_def] >>
     drule_all supported_checked_struct_metadata_acyclic >> simp[]) >>
  external_package_ce_vars_tac >>
  qpat_x_assum `cenv = _` SUBST1_TAC >>
  `ALL_DISTINCT
     (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))` by
    metis_tac[source_typing_ok_vtype_keys_distinct] >>
  gvs[set_external_package_target_def, package_external_fn_def] >>
  Cases_on `ret = NoneT` >>
  gvs[update_cenv_nonreentrant_def, update_cenv_ret_abi_def] >>
  `!vis mut rr name args dflts ret ss.
     MEM (FunctionDecl vis mut T rr name args dflts ret ss) tops ==>
     lookup_nonreentrant_slot am.layouts tx.target =
       SOME global_nonreentrant_slot` by
    (rpt strip_tac >> irule layouts_agree_nonreentrant_slot >>
     fs[source_deployment_rel_def] >> metis_tac[]) >>
  simp[body_inv_def, cenv_module_pins_def, build_compile_env_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[source_deployment_rel_def, get_module_code_def,
      initial_evaluation_context_def, get_tenv_def,
      type_env_all_modules_def, GSYM type_env_def] >>
  gvs[source_typing_ok_def] >>
  metis_tac[]
QED

Theorem external_package_dec_metadata:
  source_typing_ok tops am tx /\
  source_deployment_rel tops am tx /\
  set_external_package_target target
    (package_external_fn tops T (K global_nonreentrant_slot)
      (mut,nr,rr,tx.function_name,args,dflts,ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,nr,nkey,ut',iv,fbody,rt) /\
  cenv with ce_vars := cenv0.ce_vars = cenv0 ==>
  dec_cenv_agrees cenv
    (get_tenv (initial_evaluation_context am.sources am.layouts tx NONE))
Proof
  strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops))`
    by metis_tac[source_typing_ok_type_def_keys_distinct] >>
  external_package_ce_vars_tac >>
  qpat_x_assum `cenv = _` SUBST1_TAC >>
  Cases_on `package_external_fn tops T (K global_nonreentrant_slot)
    (mut,nr,rr,tx.function_name,args,dflts,ret,fbody)` >>
  PairCases_on `r` >> gvs[set_external_package_target_def] >>
  drule_all package_external_fn_dec_cenv_agrees >> strip_tac >>
  gvs[dec_cenv_agrees_def, source_deployment_rel_def,
      get_tenv_def, initial_evaluation_context_def, get_module_code_def,
      type_env_all_modules_def, type_env_def] >>
  rpt strip_tac >>
  irule EQ_TRANS >> irule_at Any type_memory_bytes_struct_fields >>
  simp[] >> metis_tac[]
QED

Theorem external_signature_return:
  supported_program tops /\ fn_sigs_consistent fs cx /\ ~cx.in_deploy /\
  (!src ts. get_module_code cx src = SOME ts ==> src = NONE /\ ts = tops) /\
  cenv.ce_func_return_type = build_func_return_type tops /\
  FLOOKUP fs fid = SOME sig ==>
  cenv.ce_func_return_type (nsid_to_string fid) = sig.ret_ty
Proof
  strip_tac >> PairCases_on `fid` >>
  fs[fn_sigs_consistent_def] >>
  first_x_assum drule >> strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  drule lookup_callable_function_F_SOME_MEM >> strip_tac >>
  `ALL_DISTINCT (supported_function_names tops)` by
    metis_tac[supported_program_names, supported_declaration_names_unique] >>
  simp[nsid_to_string_def] >>
  irule build_func_return_type_distinct >>
  simp[] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem external_source_flag_member_id:
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
  cenv_module_pins tops cenv /\ source_deployment_rel tops am tx /\
  get_module_code
    (initial_evaluation_context am.sources am.layouts tx NONE) src = SOME ts /\
  lookup_flag fid ts = SOME ls /\ INDEX_OF mid ls = SOME i ==>
  cenv.ce_flag_member_id (nsid_to_string (src, fid)) mid = i
Proof
  strip_tac >>
  gvs[source_deployment_rel_def, get_module_code_def,
      initial_evaluation_context_def, AllCaseEqs(), cenv_module_pins_def,
      nsid_to_string_def] >>
  irule build_flag_info_member_id >> metis_tac[]
QED

Theorem external_package_struct_fields:
  source_typing_ok tops am tx /\
  source_deployment_rel tops am tx /\
  set_external_package_target target
    (package_external_fn tops T (K global_nonreentrant_slot)
      (mut,nr,rr,tx.function_name,args,dflts,ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,nr,nkey,ut',iv,fbody,rt) /\
  cenv with ce_vars := cenv0.ce_vars = cenv0 /\
  FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
  ALL_DISTINCT (MAP FST fields) /\
  EVERY (\(fname,fty,sz). !tv.
    evaluate_type
      (get_tenv (initial_evaluation_context am.sources am.layouts tx NONE))
      fty = SOME tv ==> sz = type_memory_size tv) fields
Proof
  strip_tac >>
  `ALOOKUP am.sources tx.target = SOME [(NONE,tops)] /\
   layouts_agree tops am tx` by fs[source_deployment_rel_def] >>
  qpat_x_assum `source_deployment_rel _ _ _` kall_tac >>
  `ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops))`
    by metis_tac[source_typing_ok_type_def_keys_distinct] >>
  `!name args. MEM (StructDecl name args) tops ==>
     ALL_DISTINCT (MAP FST args)` by
    (rpt strip_tac >> gvs[source_typing_ok_def] >>
     drule check_contract_struct_fields_distinct >>
     simp[] >> disch_then drule >> simp[]) >>
  external_package_ce_vars_tac >>
  qpat_x_assum `cenv = _` SUBST_ALL_TAC >>
  gvs[set_external_package_target_def, package_external_fn_def] >>
  Cases_on `ret = NoneT` >>
  gvs[update_cenv_nonreentrant_def, update_cenv_ret_abi_def,
      build_compile_env_ce_struct_fields] >>
  gvs[get_tenv_def,
      initial_evaluation_context_def, get_module_code_def,
      type_env_all_modules_def, GSYM type_env_def] >>
  irule make_struct_fields_map_fields >> metis_tac[]
QED

(* The packaged external env's method ids are the selectors over the
   source's type environment, as expr_sim_inv asks. *)
Theorem external_package_method_id:
  source_deployment_rel tops am tx /\
  set_external_package_target target
    (package_external_fn tops T (K global_nonreentrant_slot)
      (mut,nr,rr,tx.function_name,args,dflts,ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,nr,nkey,ut',iv,fbody,rt) /\
  cenv with ce_vars := cenv0.ce_vars = cenv0 ==>
  !fname tys.
    cenv.ce_method_id fname tys =
    w2n (calldata_method_id
           (function_selector fname
              (vyper_to_abi_types
                 (get_tenv (initial_evaluation_context am.sources am.layouts
                              tx NONE)) tys)))
Proof
  strip_tac >>
  external_package_ce_vars_tac >>
  qpat_x_assum `cenv = _` SUBST1_TAC >>
  gvs[set_external_package_target_def, package_external_fn_def] >>
  rw[update_cenv_nonreentrant_def, update_cenv_ret_abi_def] >>
  simp[build_compile_env_def] >> rpt (pairarg_tac >> gvs[]) >>
  gvs[source_deployment_rel_def, get_tenv_def,
      initial_evaluation_context_def, get_module_code_def,
      type_env_all_modules_def, GSYM type_env_def]
QED

Theorem external_package_global_maps:
  set_external_package_target target
    (package_external_fn tops T (K global_nonreentrant_slot)
      (mut,nr,rr,tx.function_name,args,dflts,ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,nr,nkey,ut',iv,fbody,rt) /\
  cenv with ce_vars := cenv0.ce_vars = cenv0 /\
  check_contract F am.layouts tx.target [(NONE,tops)] = SOME art /\
  env_t.toplevel_vtypes = art.cta_toplevel_vtypes /\
  env_t.bare_globals = art.cta_bare_globals ==>
  place_map_tables_agree_on_defined cenv env_t /\
  (!nsid ty. FLOOKUP env_t.bare_globals nsid = SOME ty ==>
     cenv.ce_hashmap_info nsid = NONE)
Proof
  strip_tac >>
  drule_all external_package_registered_hashmap_info >> strip_tac >>
  conj_tac
  >- (drule checked_single_module_defined_map_agreement >>
      disch_then irule >> simp[]) >>
  rpt strip_tac >> gvs[] >>
  drule_all checked_single_module_bare_global_no_hashmap >> simp[]
QED

Theorem external_package_bare_globals:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  source_deployment_rel tops am tx /\
  initial_venom_state_rel tops am tx vs /\
  es0.immutables = am.immutables /\
  env_consistent env_t
    (initial_evaluation_context am.sources am.layouts tx NONE) es0 /\
  set_external_package_target target
    (package_external_fn tops T (K global_nonreentrant_slot)
      (mut,nr,rr,tx.function_name,args,dflts,ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,nr,nkey,ut',iv,fbody,rt) /\
  cenv with ce_vars := cenv0.ce_vars = cenv0 ==>
  !src id ty. FLOOKUP env_t.bare_globals (src,id) = SOME ty /\
    (~cx_const_name (initial_evaluation_context am.sources am.layouts tx NONE)
       (src,id) \/
     IS_SOME (FLOOKUP env_t.bare_global_assignable (src,id))) ==>
    src = cenv.ce_module /\
    ?off. FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
      !tv. evaluate_type (get_tenv
        (initial_evaluation_context am.sources am.layouts tx NONE)) ty = SOME tv ==>
        off + type_memory_size tv < dimword (:256)
Proof
  strip_tac >>
  drule lower_vyper_runtime_unit_immutables_bound >> strip_tac >>
  `immutables_section_rel tops (account_immutables am tx.target)
     vs.vs_data_section` by gvs[initial_venom_state_rel_def] >>
  drule immutables_section_rel_length >> strip_tac >>
  `LENGTH vs.vs_data_section < dimword (:256)` by
    (simp[wordsTheory.dimword_def] >> decide_tac) >>
  `get_module_code (initial_evaluation_context am.sources am.layouts tx NONE)
     NONE = SOME tops /\
   (!src ts. get_module_code
      (initial_evaluation_context am.sources am.layouts tx NONE) src = SOME ts ==>
      src = NONE)` by
    (gvs[source_deployment_rel_def, get_module_code_def,
         initial_evaluation_context_def] >> rpt strip_tac >> gvs[]) >>
  Cases_on `ALOOKUP am.immutables tx.target`
  >- (gvs[env_consistent_def, env_immutables_consistent_def,
          initial_evaluation_context_def, get_source_immutables_def] >>
      rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `!src id ty. FLOOKUP env_t.bare_globals (src,id) = SOME ty /\
     (~cx_const_name (initial_evaluation_context am.sources am.layouts tx NONE)
        (src,id) \/
      IS_SOME (FLOOKUP env_t.bare_global_assignable (src,id))) ==>
     src = (build_compile_env tops External mut tx.function_name args ret fbody T).ce_module /\
     ?off. FLOOKUP (build_compile_env tops External mut tx.function_name args ret fbody T).ce_module_vars
       (src,id) = SOME (ImmutableLoc off) /\
       !tv. evaluate_type (get_tenv
         (initial_evaluation_context am.sources am.layouts tx NONE)) ty = SOME tv ==>
         off + type_memory_size tv < dimword (:256)` by
    (drule_at (Pat `env_consistent _ _ _`)
       (INST_TYPE [alpha |-> ``:string``] build_compile_env_bare_globals) >>
     simp[] >> strip_tac >> rpt gen_tac >> strip_tac >>
     first_x_assum irule >>
     gvs[account_immutables_def, initial_evaluation_context_def] >>
     metis_tac[]) >>
  external_package_ce_vars_tac >>
  gvs[package_external_fn_def, set_external_package_target_def] >>
  Cases_on `ret = NoneT` >>
  gvs[update_cenv_nonreentrant_def, update_cenv_ret_abi_def] >>
  qpat_x_assum `cenv = _` (fn th => once_rewrite_tac [th]) >>
  simp[] >> metis_tac[]
QED

Theorem external_source_return_buffer_ok:
  !tops rpolicy unit tx ret mut nr args dflts fbody lbl cenv0 pos_args
   min_cds is_payable nkey ut iv rt cenv.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut,nr,args,dflts,ret,fbody) /\
    set_external_package_target rpolicy.rpol_target
      (package_external_fn tops T (K global_nonreentrant_slot)
        (mut,nr,lookup_raw_return_or_F (NONE : num option)
          tx.function_name External tops,tx.function_name,args,subst_consts_exprs (module_consts_env tops []) dflts,ret,
         subst_consts_stmts (module_consts_env tops []) fbody)) =
      (lbl,cenv0,pos_args,min_cds,is_payable,nr,nkey,ut,iv,subst_consts_stmts (module_consts_env tops []) fbody,rt) /\
    cenv with ce_vars := cenv0.ce_vars = cenv0 ==>
    (stmts_valued_return (subst_consts_stmts (module_consts_env tops []) fbody) /\ cenv.ce_is_external /\
     ~cenv.ce_raw_return ==> return_buffer_ok cenv)
Proof
  rpt gen_tac >> strip_tac >> strip_tac >>
  `EVERY (supported_declaration_header tops) tops` by
    gvs[supported_program_def, supported_declaration_headers_def] >>
  `~lookup_raw_return_or_F (NONE:num option) tx.function_name External tops` by
    (drule return_package_target_inversion >> strip_tac >>
     drule return_package_metadata >> strip_tac >>
     fs[compile_env_component_equality]) >>
  `external_return_buffer_ok
     (lbl,cenv0,pos_args,min_cds,is_payable,nr,nkey,ut,iv,subst_consts_stmts (module_consts_env tops []) fbody,rt)` by
    (drule lookup_function_external_raw_cases >> strip_tac
     >- (`MEM (FunctionDecl External mut nr F tx.function_name args dflts ret fbody)
            tops` by gvs[lookup_raw_return_or_F_def] >>
         Cases_on `classify_functions tops` >> PairCases_on `r` >>
         drule_all supported_external_classification >>
         simp[subst_consts_fn_def, subst_consts_expr_def] >> strip_tac >>
         Cases_on `tx.function_name = "__default__"` >> gvs[]
         >- (qpat_x_assum `lower_vyper_runtime_unit _ _ = _` mp_tac >>
             simp[lower_vyper_runtime_unit_def, package_fallback_fn_def,
                  set_fallback_package_target_def] >> strip_tac >>
             gvs[package_external_fn_def, set_external_package_target_def,
                 external_return_buffer_ok_def]) >>
         drule_all lower_vyper_runtime_unit_return_buffer_ok >>
         gvs[lookup_raw_return_or_F_def]) >>
     `dflts = []` by (drule vyperReadOnlySyntaxTheory.external_getter_defaults >> simp[]) >>
     gvs[subst_consts_expr_def] >>
     `public_getter decl =
        SOME (mut,nr,F,tx.function_name,args,([]:expr list),ret,fbody)` by
       fs[public_getter_source_tuple] >>
     `MEM (mut,nr,F,tx.function_name,args,[],
          ret,subst_consts_stmts (module_consts_env tops []) fbody)
        (FST (classify_functions tops))` by
       (irule (REWRITE_RULE [subst_consts_fn_def, subst_consts_expr_def]
         (Q.SPECL [`tops`, `(mut,nr,F,tx.function_name,args,[]:expr list,ret,fbody)`]
           public_getter_classified_mem)) >>
        simp[MEM_public_getters] >> metis_tac[]) >>
     Cases_on `classify_functions tops` >> PairCases_on `r` >> gvs[] >>
     drule_all lower_vyper_runtime_unit_return_buffer_ok >>
     gvs[lookup_raw_return_or_F_def]) >>
  drule package_external_fn_return_buffer_ok >>
  disch_then drule >> strip_tac >>
  external_package_ce_vars_tac >>
  `~cenv0.ce_raw_return` by gvs[compile_env_component_equality] >>
  qpat_x_assum `cenv = _` (fn th => once_rewrite_tac [th]) >>
  gvs[return_buffer_ok_def]
QED

Theorem external_selected_return_buffer_ok:
  !tops rpolicy unit tx calldata ret mut args fbody lbl cenv0 pos_args
   min_cds is_payable nkey ut iv rt st cenv sa.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    valid_vyper_call tops tx calldata ret /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut,F,args,[],ret,fbody) /\
    set_external_package_target rpolicy.rpol_target
      (package_external_fn tops T (K global_nonreentrant_slot)
        (mut,F,lookup_raw_return_or_F (NONE : num option)
          tx.function_name External tops,tx.function_name,args,[],ret,
         subst_consts_stmts (module_consts_env tops []) fbody)) =
      (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut,iv,subst_consts_stmts (module_consts_env tops []) fbody,rt) /\
    compile_register_positional_args cenv0 pos_args 4 st = (cenv,sa) ==>
    (stmts_valued_return (subst_consts_stmts (module_consts_env tops []) fbody) /\ cenv.ce_is_external /\
     ~cenv.ce_raw_return ==> return_buffer_ok cenv)
Proof
  rpt gen_tac >> strip_tac >>
  `cenv with ce_vars := cenv0.ce_vars = cenv0` by
    (drule compile_register_positional_args_cenv >> simp[compile_env_component_equality]) >>
  qspecl_then [`tops`,`rpolicy`,`unit`,`tx`,`ret`,`mut`,`F`,`args`,`[]:expr list`,
    `fbody`,`lbl`,`cenv0`,`pos_args`,`min_cds`,`is_payable`,`nkey`,`ut`,`iv`,`rt`,`cenv`]
    mp_tac external_source_return_buffer_ok >>
  fs[subst_consts_expr_def,package_external_fn_def]
QED


Theorem external_body_inv_source[local]:
  body_inv tops ctx cenv cx ==>
  !src ts. get_module_code cx src = SOME ts ==> src = NONE /\ ts = tops
Proof
  strip_tac >> drule body_inv_contract >>
  disch_then (fn th => GEN_TAC >> Cases_on `src` >>
    simp[MATCH_MP contract_inv_module_codes th, ALOOKUP_def])
QED

Theorem contract_inv_event_info[local]:
  contract_inv mods exps ctx cenv cx ==>
  cenv.ce_event_info = build_event_info_mods (type_env_all_modules mods) mods (K NONE)
Proof
  simp[contract_inv_def]
QED

(* At the start of the selected function's body, the
   premises of body_stmts_sim other than the frame's returns: the frame is
   the lowered program's (body_inv), the body is supported and typed at
   the return type in a type environment env_t of the parameters, which
   the compile env and the source state agree with and whose locals fit
   the allocation limit, and the external frame has no return PC and no
   lock. expr_sim_inv's storage-variable clause (each storage variable has
   its declared module type and no hash-map info) follows from body_inv
   and the single-module fact via body_inv_storage_var_types. *)
Theorem external_source_body_const_cells[local]:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
  check_contract F am.layouts tx.target [(NONE,tops)] = SOME art /\
  env = function_entry_env art [(NONE,tops)] NONE External args /\
  es.immutables = am.immutables ==>
  body_const_cells_agree [(NONE,tops)]
    (initial_evaluation_context am.sources am.layouts tx NONE) env es
Proof
  strip_tac >>
  Cases_on `classify_functions tops` >>
  rename1 `classify_functions tops = (exts,tail)` >> PairCases_on `tail` >>
  drule_all lower_vyper_runtime_unit_consts_guard >> strip_tac >>
  drule source_typing_ok_consts_ready >> strip_tac >>
  `ALOOKUP am.sources tx.target = SOME [(NONE,tops)]` by
    fs[source_deployment_rel_def] >>
  mp_tac (Q.INST
    [`cx` |-> `initial_evaluation_context am.sources am.layouts tx NONE`,
     `mods` |-> `[(NONE,tops)]`, `imms` |-> `account_immutables am tx.target`,
     `artifact` |-> `art`, `A` |-> `A`,
     `sc` |-> `[]`, `current_src` |-> `NONE`]
    constSubstCorrectTheory.checked_module_consts_subst_context) >>
  impl_tac >- gvs[initial_evaluation_context_def] >>
  strip_tac >>
  `cx_tops (initial_evaluation_context am.sources am.layouts tx NONE) = tops` by
    simp[cx_tops_def, get_module_code_def, initial_evaluation_context_def,
         ALOOKUP_def] >>
  `frame_maps env art` by simp[] >>
  `const_subst_context roots
      (initial_evaluation_context am.sources am.layouts tx NONE) env
      (module_consts_env tops []) [(NONE,tops)] art` by
    (irule const_subst_context_static >> goal_assum (drule_at Any) >>
     gvs[function_entry_env_def, artifact_env_def,
         vyperTypeContractContextTheory.FOLDL_extend_local_args_static]) >>
  `const_cells_agree roots es` by
    fs[const_cells_agree_def, initial_state_def] >>
  pure_once_rewrite_tac [body_const_cells_agree_def] >>
  qexistsl_tac [`roots`, `art`, `account_immutables am tx.target`, `A`] >>
  qpat_assum `cx_tops (initial_evaluation_context am.sources am.layouts tx NONE) = tops`
    (fn th => pure_rewrite_tac [th]) >>
  conj_tac
  >- qpat_assum `check_contract F am.layouts tx.target [(NONE,tops)] = SOME art`
       (fn th => simp[NoAsms, initial_evaluation_context_def, th]) >>
  conj_tac
  >- qpat_assum `ALOOKUP am.sources tx.target = SOME [(NONE,tops)]`
       (fn th => simp[NoAsms, initial_evaluation_context_def, th]) >>
  conj_tac >- simp[NoAsms] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem runtime_context_bare_globals[local]:
  env_context_consistent env cx /\ env_context_consistent env' cx ==>
  env.bare_globals = env'.bare_globals
Proof
  `!e1 e2 src id ty.
     env_context_consistent e1 cx /\ env_context_consistent e2 cx /\
     FLOOKUP e1.bare_globals (src,id) = SOME ty ==>
     FLOOKUP e2.bare_globals (src,id) = SOME ty` by
    (rpt gen_tac >> strip_tac >>
     drule_at_then (Pat `FLOOKUP _ _ = SOME _`) drule
       env_context_consistent_bare_global_find_NONE >>
     disch_then (qx_choose_then `ts` strip_assume_tac) >>
     drule is_bare_global_decl_cases >> strip_tac >>
     imp_res_tac is_immutable_decl_MEM_Immutable_exists >>
     fs[env_context_consistent_def, bare_globals_complete_def] >>
     metis_tac[]) >>
  simp[fmap_eq_flookup, FORALL_PROD] >>
  rpt strip_tac >>
  Cases_on `FLOOKUP env.bare_globals (p_1,p_2)` >>
  Cases_on `FLOOKUP env'.bare_globals (p_1,p_2)` >>
  metis_tac[optionTheory.SOME_11, optionTheory.NOT_NONE_SOME]
QED

Theorem runtime_context_fn_sigs[local]:
  ~cx.in_deploy /\ env_context_consistent env cx /\ env_context_consistent env' cx ==>
  env.fn_sigs = env'.fn_sigs
Proof
  strip_tac >>
  `!e1 e2 src fn sg.
      env_context_consistent e1 cx /\ env_context_consistent e2 cx /\
      FLOOKUP e1.fn_sigs (src,fn) = SOME sg ==>
      FLOOKUP e2.fn_sigs (src,fn) = SOME sg` by
    (rpt gen_tac >> strip_tac >>
     fs[env_context_consistent_def, fn_sigs_declared_complete_nondeploy,
        fn_sigs_consistent_def, fn_sigs_live_def, fn_sigs_complete_def] >>
     qpat_assum `!sid f signature. FLOOKUP e1.fn_sigs _ = _ ==> _`
       (drule_then strip_assume_tac) >>
     `context_function_live cx (src,fn)` by
       (qpat_assum `!k signature. FLOOKUP e1.fn_sigs k = SOME signature ==> _`
          (drule_then ACCEPT_TAC)) >>
     rename1 `lookup_callable_function _ fn ts = SOME (fm,nr,params,dflts,sg.ret_ty,ss)` >>
     qpat_assum `~cx.in_deploy` (fn runtime =>
       qpat_assum `fn_sigs_declared_complete e2.fn_sigs cx`
         (qspecl_then [`src`,`fn`,`ts`,`fm`,`nr`,`params`,`dflts`,
                      `sg.ret_ty`,`ss`] mp_tac o
          REWRITE_RULE [MATCH_MP fn_sigs_declared_complete_nondeploy runtime,
                        fn_sigs_complete_def])) >>
     simp[fn_sig_component_equality]) >>
  simp[fmap_eq_flookup, FORALL_PROD] >>
  rpt strip_tac >>
  Cases_on `FLOOKUP env.fn_sigs (p_1,p_2)` >>
  Cases_on `FLOOKUP env'.fn_sigs (p_1,p_2)` >>
  metis_tac[optionTheory.SOME_11, optionTheory.NOT_NONE_SOME]
QED

Theorem external_source_body_const_cells_checked:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
  env_context_consistent env (initial_evaluation_context am.sources am.layouts tx NONE) /\
  es.immutables = am.immutables ==>
  body_const_cells_agree [(NONE,tops)]
    (initial_evaluation_context am.sources am.layouts tx NONE) env es
Proof
  strip_tac >>
  drule source_typing_ok_consts_ready >> strip_tac >>
  `ALOOKUP am.sources tx.target = SOME [(NONE,tops)]` by
    fs[source_deployment_rel_def] >>
  qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts tx NONE` >>
  qabbrev_tac `canonical_env = artifact_env art [(NONE,tops)] NONE` >>
  `~cx.in_deploy` by simp[Abbr `cx`, initial_evaluation_context_def] >>
  `env_context_consistent canonical_env cx` by
    (unabbrev_all_tac >> irule check_contract_env_context_consistent_initial_NONE >>
     simp[]) >>
  `body_const_cells_agree [(NONE,tops)] cx canonical_env es` by
    (unabbrev_all_tac >> irule external_source_body_const_cells >>
     asm_rewrite_tac[] >> conj_tac
     >- (qexistsl [`rpolicy`,`unit`] >> first_assum ACCEPT_TAC) >>
     qexistsl [`[]`,`art`] >> simp[function_entry_env_def]) >>
  `env.bare_globals = canonical_env.bare_globals` by
    drule_all_then ACCEPT_TAC runtime_context_bare_globals >>
  `env.fn_sigs = canonical_env.fn_sigs` by
    drule_all_then ACCEPT_TAC runtime_context_fn_sigs >>
  `env.bare_global_assignable = canonical_env.bare_global_assignable` by
    fs[env_context_consistent_def, bare_global_assignable_complete_def] >>
  `env.type_defs = get_tenv cx` by fs[env_context_consistent_def] >>
  `!id ty. FLOOKUP env.bare_globals (NONE,id) = SOME ty ==>
            FLOOKUP env.toplevel_vtypes (NONE,id) = SOME (Type ty)` by
    (rpt strip_tac >>
     drule_all_then strip_assume_tac env_context_consistent_bare_global_find_NONE >>
     first_assum ACCEPT_TAC) >>
  qpat_x_assum `body_const_cells_agree _ cx canonical_env es`
    (strip_assume_tac o REWRITE_RULE [body_const_cells_agree_def]) >>
  rewrite_tac [body_const_cells_agree_def] >>
  qexistsl [`roots`,`art'`,`imms`,`A'`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY (simp[ALOOKUP_def] >> NO_TAC)
  >- fs[frame_maps_def] >>
  qpat_x_assum `const_subst_context roots cx canonical_env _ _ art'`
    (strip_assume_tac o REWRITE_RULE [const_subst_context_def]) >>
  rewrite_tac [const_subst_context_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!a s n t e. MEM (a,s,n,t,e) roots ==> _`
        (drule_then (strip_assume_tac o REWRITE_RULE [checked_frame_context_def])) >>
      simp[checked_frame_context_def, frame_maps_def] >>
      conj_tac >- (qexists_tac `mode` >> fs[]) >> fs[frame_maps_def]) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!i e. ALOOKUP (module_consts_env _ []) i = SOME e ==> _`
    (drule_then strip_assume_tac) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY (simp[] >> NO_TAC) >>
  TRY (qpat_assum `!id ty. FLOOKUP env.bare_globals (NONE,id) = SOME ty ==> _`
         irule >> simp[] >> NO_TAC) >>
  metis_tac[]
QED

Theorem external_source_body_frame_nr:
  !tops rpolicy unit am tx ret vs mut nr args dflts fbody gs es0 lbl cenv0
   pos_args min_cds is_payable nkey ut iv rt cenv.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
    initial_venom_state_rel tops am tx vs /\
    outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut,nr,args,dflts,ret,fbody) /\
    external_entry_bound tops am tx vs.vs_outcomes gs mut args dflts es0 /\
    set_external_package_target rpolicy.rpol_target
      (package_external_fn tops T (K global_nonreentrant_slot)
         (mut,nr,lookup_raw_return_or_F (NONE:num option)
            tx.function_name External tops,
          tx.function_name,args,subst_consts_exprs (module_consts_env tops []) dflts,ret,
          subst_consts_stmts (module_consts_env tops []) fbody)) =
      (lbl,cenv0,pos_args,min_cds,is_payable,nr,nkey,ut,iv,
       subst_consts_stmts (module_consts_env tops []) fbody,rt) /\
    cenv with ce_vars := cenv0.ce_vars = cenv0 /\
    (!id ty. MEM (id,ty) args ==>
       (?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) /\
       cenv.ce_var_type id = SOME ty) /\
    (!id loc. FLOOKUP cenv.ce_vars id = SOME loc ==> MEM id (MAP FST args)) ==>
    body_inv tops unit.cu_context cenv
      (initial_evaluation_context am.sources am.layouts tx NONE) /\
    cenv.ce_return_pc = NONE /\
    ?bindings env_t env'.
      supported_stmts tops bindings (subst_consts_stmts (module_consts_env tops []) fbody) /\
      expr_sim_inv cenv
        (initial_evaluation_context am.sources am.layouts tx NONE) env_t es0 /\
      body_const_cells_agree [(NONE,tops)]
        (initial_evaluation_context am.sources am.layouts tx NONE) env_t es0 /\
      ce_locals_declared cenv env_t /\ locals_alloc_ok cenv env_t /\
      type_stmts env_t ret (subst_consts_stmts (module_consts_env tops []) fbody) = SOME env' /\
      stmts_exprs_ok cenv (subst_consts_stmts (module_consts_env tops []) fbody) /\
      call_evaluation_safe
        (initial_evaluation_context am.sources am.layouts tx NONE)
        (int_calls_stmts (subst_consts_stmts (module_consts_env tops []) fbody))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all external_package_body_inv >> strip_tac >> simp[] >>
  drule_all external_lookup_body_typing_canonical >> strip_tac >>
  `?A. constants_fold_module [(NONE,tops)] (account_immutables am tx.target)
          NONE tops FEMPTY = SOME A` by fs[source_typing_ok_def] >>
  pop_assum strip_assume_tac >>
  `env_t.type_defs = type_env_all_modules [(NONE,tops)]` by
    fs[checked_contract_runtime_ready_def, get_tenv_def, initial_evaluation_context_def] >>
  `!id ty. MEM (id,ty) args ==> FLOOKUP env_t.var_types id = SOME ty` by metis_tac[] >>
  `?env_compiled.
     type_stmts env_t ret (subst_consts_stmts (module_consts_env tops []) fbody) =
       SOME env_compiled` by
    (drule_all compiled_selected_external_body_typing >>
     metis_tac[optionTheory.IS_SOME_EXISTS]) >>
  pop_assum strip_assume_tac >>
  `int_calls_stmts (subst_consts_stmts (module_consts_env tops []) fbody) =
     int_calls_stmts fbody` by
    (irule (INST_TYPE [alpha |-> ``:160 word``] checked_const_substitution_int_calls) >>
     qexistsl [`A`, `tx.target`, `art`, `account_immutables am tx.target`,
       `am.layouts`, `F`, `[(NONE,tops)]`] >> simp[]) >>
  `machine_well_typed am` by gvs[source_typing_ok_def] >>
  drule_all external_entry_bound_source_frame >> strip_tac >>
  drule_all external_source_body_const_cells >> strip_tac >>
  qpat_x_assum `env_t = function_entry_env _ _ _ _ _` kall_tac >>
  drule_all external_selected_env_consistent >> strip_tac >>
  `outcomes_accounts_typed es0.outcomes /\ IS_SOME es0.outcomes` by
    (qpat_assum `outcome_suffix _ _`
       (strip_assume_tac o SIMP_RULE (srw_ss())
         [vyperEvalOutcomeSuffixTheory.outcome_suffix_def]) >>
     qpat_assum `es0.outcomes = SOME _` (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
     qpat_assum `outcomes_accounts_typed (SOME vs.vs_outcomes)` mp_tac >>
     qpat_assum `vs.vs_outcomes = _ ++ _` (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
     simp[outcomes_accounts_typed_def, EVERY_APPEND]) >>
  drule_all external_source_context_typed >> strip_tac >>
  drule_all external_package_dec_metadata >> strip_tac >>
  drule_all external_package_global_maps >> strip_tac >>
  mp_tac (Q.INST [`tops` |-> `tops`, `rpolicy` |-> `rpolicy`, `unit` |-> `unit`,
    `am` |-> `am`, `tx` |-> `tx`, `vs` |-> `vs`, `es0` |-> `es0`, `env_t` |-> `env_t`,
    `target` |-> `rpolicy.rpol_target`, `rr` |-> `lookup_raw_return_or_F (NONE:num option)
      tx.function_name External tops`, `mut` |-> `mut`, `nr` |-> `nr`,
    `dflts` |-> `subst_consts_exprs (module_consts_env tops []) dflts`,
    `fbody` |-> `subst_consts_stmts (module_consts_env tops []) fbody`,
    `args` |-> `args`, `ret` |-> `ret`, `lbl` |-> `lbl`, `cenv0` |-> `cenv0`,
    `pos_args` |-> `pos_args`, `min_cds` |-> `min_cds`, `is_payable` |-> `is_payable`,
    `nkey` |-> `nkey`, `iv` |-> `iv`, `ut'` |-> `ut`, `rt` |-> `rt`, `cenv` |-> `cenv`]
    (INST_TYPE [alpha |-> ``:expr``] (SPEC_ALL external_package_bare_globals))) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  `supported_function_body tops External args
     (subst_consts_stmts (module_consts_env tops []) fbody)` by
    metis_tac[supported_selected_external_body] >>
  `ALL_DISTINCT (MAP FST args)` by
    (drule_all external_selected_args_distinct >> simp[]) >>
  `EVERY (\(n,ty). assignable_type env_t.type_defs ty) args` by
    (`supported_declaration_headers tops` by fs[supported_program_def] >>
     drule_all source_typing_ok_params_ok >>
     `env_t.type_defs = type_env tops` by
       (qpat_x_assum `env_t.type_defs = _` SUBST1_TAC >>
        qpat_x_assum `checked_contract_runtime_ready _ _ _ _` mp_tac >>
        simp[checked_contract_runtime_ready_def, get_tenv_def,
             initial_evaluation_context_def, type_env_all_modules_def,
             type_env_def]) >>
     disch_then (strip_assume_tac o REWRITE_RULE [params_ok_def]) >>
     ASM_REWRITE_TAC []) >>
  `cenv.ce_struct_fields = make_struct_fields_map tops /\
   cenv.ce_event_info = build_event_info (type_env tops) tops (K NONE)` by
    (qpat_assum `body_inv tops _ cenv _` (fn inv =>
       let
         val contract = MATCH_MP body_inv_contract inv
       in
         mp_tac (CONJ (MATCH_MP contract_inv_struct_fields contract)
                      (MATCH_MP contract_inv_event_info contract))
       end) >>
     simp[make_struct_fields_map_mods_singleton, build_event_info_mods_singleton,
          type_env_all_modules_def, type_env_def, FUNION_FEMPTY_2]) >>
  `env_context_consistent env_t
     (initial_evaluation_context am.sources am.layouts tx NONE)` by
    gvs[env_consistent_def] >>
  `stmts_valued_return (subst_consts_stmts (module_consts_env tops []) fbody) /\
   cenv.ce_is_external /\ ~cenv.ce_raw_return ==> return_buffer_ok cenv` by
    (strip_tac >> drule external_source_return_buffer_ok >>
     rpt (disch_then drule) >> simp[]) >>
  drule_all external_package_alloc_env_agree >> strip_tac >>
  `?rr:bool. fn_allocs_ok tops
     (mut,nr,rr,tx.function_name,args,subst_consts_exprs (module_consts_env tops []) dflts,
      ret,subst_consts_stmts (module_consts_env tops []) fbody)` by
    (drule lookup_function_external_classified >>
     simp[subst_consts_fn_def, subst_consts_expr_def] >> strip_tac >>
     Cases_on `classify_functions tops` >> PairCases_on `r` >> gvs[] >>
     qexists `rr` >> irule lower_vyper_runtime_unit_allocs_ok >>
     metis_tac[]) >>
  `~supported_stmts_expr_exists (const_name_root_mods cenv.ce_modules)
     (subst_consts_stmts (module_consts_env tops []) fbody)` by
    (qpat_assum `body_inv tops _ cenv _`
       (fn inv => REWRITE_TAC
         [MATCH_MP contract_inv_cenv_modules (MATCH_MP body_inv_contract inv)]) >>
     irule (INST_TYPE [alpha |-> ``:160 word``]
       checked_const_substitution_const_name_free) >>
     metis_tac[]) >>
  `qualified_stmts_decls_ok cenv.ce_modules
     (subst_consts_stmts (module_consts_env tops []) fbody)` by
    (qpat_assum `body_inv tops _ cenv _`
       (fn inv => REWRITE_TAC
         [MATCH_MP contract_inv_cenv_modules (MATCH_MP body_inv_contract inv)]) >>
     drule lookup_function_External_cases >> strip_tac
     >- (`module_allocated am.layouts tx.target NONE tops` by
           (drule check_contract_main_module_allocated >> simp[]) >>
         `check_function_body am.layouts tx.target [(NONE,tops)] art NONE
             External mut nr args dflts ret fbody` by
           (irule check_contract_runtime_function_body_MEM >> simp[] >>
            qexistsl [`tx.function_name`, `raw`] >> simp[]) >>
         drule_all (SIMP_RULE (srw_ss())
           [consts_env_mods_singleton, subst_consts_mods_singleton]
           (Q.INST [`mods` |-> `[(NONE,tops)]`]
             checked_qualified_body_decl_resolution)) >> simp[]) >>
     `?exp. fbody = [Return (SOME exp)]` by
       (Cases_on `decl` >>
        gvs[is_public_getter_decl_def, external_getter_tuple_def] >>
        Cases_on `v` >>
        gvs[external_getter_tuple_def, getter_def, AllCaseEqs()] >>
        rpt (pairarg_tac >> gvs[]) >> metis_tac[]) >>
     gvs[subst_consts_stmt_def]) >>
  drule_all external_body_support_bounds_from_allocs >> strip_tac >>
  `ce_locals_declared cenv env_t` by
    (rw[ce_locals_declared_def] >>
     qpat_assum `!id loc. FLOOKUP cenv.ce_vars id = SOME loc ==> MEM id (MAP FST args)`
       (fn declared => qpat_assum `FLOOKUP cenv.ce_vars n = SOME l`
         (mp_tac o MATCH_MP declared)) >>
     qpat_assum `!id ty. MEM (id,ty) args ==> FLOOKUP env_t.var_types id = SOME ty` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[MEM_MAP,pairTheory.EXISTS_PROD,FLOOKUP_DEF] >> metis_tac[]) >>
  qexistsl [`bindings`, `env_t`, `env_compiled`] >> simp[] >>
  simp[expr_sim_inv_def] >> rpt conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!n ty. FLOOKUP env_t.var_types n = SOME ty ==> _` drule >>
      qpat_assum `!id ty. MEM (id,ty) args ==> (?p sz. _) /\ _`
        (fn params => disch_then (mp_tac o MATCH_MP params)) >> simp[])
  >- (rpt strip_tac >>
      irule external_signature_return >>
      qexistsl [`initial_evaluation_context am.sources am.layouts tx NONE`,
                `art.cta_fn_sigs`, `tops`] >> simp[] >>
      qpat_assum `env_consistent _ _ _` (strip_assume_tac o
        SIMP_RULE std_ss [env_consistent_def, env_context_consistent_def]) >>
      rpt conj_tac
      >- (qpat_assum `body_inv tops _ cenv _`
            (ACCEPT_TAC o MATCH_MP external_body_inv_source))
      >- simp_tac (srw_ss()) [initial_evaluation_context_def]
      >- (qpat_assum `body_inv tops _ cenv _`
            (mp_tac o MATCH_MP contract_inv_return_types o MATCH_MP body_inv_contract) >>
          simp[build_func_return_type_mods_singleton]) >>
      qpat_x_assum `env_t.fn_sigs = art.cta_fn_sigs` (SUBST_ALL_TAC o SYM) >>
      first_assum ACCEPT_TAC)
  >- (rpt strip_tac >> irule external_source_flag_member_id >>
      drule_then assume_tac intcall_args_body_inv_pins >>
      metis_tac[source_typing_ok_type_def_keys_distinct])
  >- gvs[dec_cenv_agrees_def]
  >- (drule_all external_package_method_id >> simp[])
  >- gvs[dec_cenv_agrees_def]
  >- (rpt strip_tac >>
      `FLOOKUP cenv.ce_struct_fields name = SOME fields` by simp[] >>
      drule_all external_package_struct_fields >> simp[])
  >- (`!src ts. get_module_code
         (initial_evaluation_context am.sources am.layouts tx NONE) src =
         SOME ts ==> src = NONE` by
        (qpat_assum `body_inv tops _ cenv _`
           (mp_tac o MATCH_MP external_body_inv_source) >> metis_tac[]) >>
      drule body_inv_storage_var_types >> disch_then drule >>
      strip_tac >> rpt gen_tac >> strip_tac >>
      first_x_assum drule_all >> simp[])
  >- (simp[] >> irule external_bind_arguments_popped >> goal_assum (drule_at Any))
  >- (rpt strip_tac >>
      qpat_assum `env_t.bare_globals = art.cta_bare_globals` (SUBST_ALL_TAC o SYM) >>
      first_x_assum drule >> simp[]) >>
  simp[bare_globals_layout_def] >> rpt conj_tac
  >~ [`ALOOKUP cenv.ce_modules`] >- metis_tac[body_inv_modules_aligned]
  >~ [`ALL_DISTINCT (MAP FST cenv.ce_modules)`]
  >- metis_tac[body_inv_modules_aligned]
  >~ [`ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel _) _))`]
  >- metis_tac[body_inv_modules_aligned]
  >- (rpt strip_tac >>
      drule_then strip_assume_tac body_inv_module_locations >>
      `get_module_code (initial_evaluation_context am.sources am.layouts tx NONE)
         NONE = SOME tops` by
        (drule body_inv_main_code >> simp[]) >>
      `bare_globals_complete env_t.bare_globals
         (initial_evaluation_context am.sources am.layouts tx NONE)` by
        fs[env_context_consistent_def] >>
      fs[] >> drule add_immutable_locations_cases >> strip_tac
      >- (drule add_module_var_locations_FLOOKUP >> simp[]) >>
      gvs[bare_globals_complete_def] >> metis_tac[])
  >- (rpt strip_tac >>
      qpat_assum `body_inv tops _ cenv _`
        (ACCEPT_TAC o MATCH_MP bodyInvMetadataPropsTheory.contract_inv_constructor o
         MATCH_MP body_inv_contract))
  >- (rpt strip_tac >>
      `FLOOKUP env_t.bare_globals (src,id) = SOME ty` by simp[] >>
      drule_all body_inv_bare_global_type >> simp[]) >>
  rpt strip_tac >>
  `FLOOKUP env_t.bare_globals (src,id1) = SOME ty1 /\
   FLOOKUP env_t.bare_globals (src,id2) = SOME ty2` by simp[] >>
  `src = NONE /\ cenv.ce_module_var_type (src,id1) = SOME ty1 /\
   cenv.ce_module_var_type (src,id2) = SOME ty2` by
    metis_tac[body_inv_bare_global_type] >>
  `ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops))` by
    (qpat_assum `check_contract F _ _ _ = SOME _` mp_tac >>
     simp_tac std_ss [check_contract_def, LET_THM] >>
     strip_tac >>
     drule contract_namespaces_ok_module_type_def_keys >>
     disch_then (qspecl_then [`tops`, `NONE`] mp_tac) >> simp[]) >>
  `get_tenv (initial_evaluation_context am.sources am.layouts tx NONE) =
   type_env tops` by
    (qpat_assum `source_deployment_rel _ _ _` mp_tac >>
     simp_tac (srw_ss()) [get_tenv_def, initial_evaluation_context_def,
        source_deployment_rel_def, type_env_all_modules_def, type_env_def,
        FUNION_FEMPTY_2]) >>
  `cenv_module_pins tops cenv /\
   ALL_DISTINCT
     (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops))` by
    (qpat_assum `body_inv tops _ cenv _` (fn inv =>
       let
         val contract = MATCH_MP body_inv_contract inv
         val modul = MATCH_MP body_inv_module inv
       in
         ACCEPT_TAC (CONJ (MATCH_MP intcall_args_body_inv_pins inv)
           (MATCH_MP contract_inv_module_distinct_keys (CONJ contract modul)))
       end)) >>
  gvs[] >> irule cenv_module_pins_immutables_disjoint >>
  qexistsl [`cenv`, `initial_evaluation_context am.sources am.layouts tx NONE`,
            `id1`, `id2`, `tops`, `ty1`, `ty2`] >> simp[]
QED

Theorem external_source_body_frame:
  !tops rpolicy unit am tx ret vs mut args fbody env es0 lbl cenv0 pos_args
   min_cds is_payable nkey ut' iv rt st cenv sa.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    initial_venom_state_rel tops am tx vs /\
    outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INL (), es0) /\
    set_external_package_target rpolicy.rpol_target
      (package_external_fn tops T (K global_nonreentrant_slot)
         (mut, F, lookup_raw_return_or_F (NONE : num option)
                     tx.function_name External tops,
          tx.function_name, args, [], ret,
          subst_consts_stmts (module_consts_env tops []) fbody)) =
      (lbl, cenv0, pos_args, min_cds, is_payable, F, nkey, ut', iv,
       subst_consts_stmts (module_consts_env tops []) fbody,
       rt) /\
    compile_register_positional_args cenv0 pos_args 4 st = (cenv, sa) ==>
    body_inv tops unit.cu_context cenv
      (initial_evaluation_context am.sources am.layouts tx NONE) /\
    cenv.ce_return_pc = NONE /\
    ?bindings env_t env'.
      supported_stmts tops bindings (subst_consts_stmts (module_consts_env tops []) fbody) /\
      expr_sim_inv cenv
        (initial_evaluation_context am.sources am.layouts tx NONE) env_t es0 /\
      body_const_cells_agree [(NONE,tops)]
        (initial_evaluation_context am.sources am.layouts tx NONE) env_t es0 /\
      ce_locals_declared cenv env_t /\ locals_alloc_ok cenv env_t /\
      type_stmts env_t ret (subst_consts_stmts (module_consts_env tops []) fbody) = SOME env' /\
      stmts_exprs_ok cenv (subst_consts_stmts (module_consts_env tops []) fbody) /\
      call_evaluation_safe
        (initial_evaluation_context am.sources am.layouts tx NONE)
        (int_calls_stmts (subst_consts_stmts (module_consts_env tops []) fbody))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all external_entry_bound_no_defaults >> strip_tac >>
  `external_entry_bound tops am tx vs.vs_outcomes es0.gas_obs mut args [] es0` by
    (`es0 with gas_obs := es0.gas_obs = es0` by (Cases_on `es0` >> simp[]) >>
     pop_assum (fn same =>
       qpat_assum `!gx. external_entry_bound _ _ _ _ _ _ _ _ _`
         (qspec_then `es0.gas_obs` (ACCEPT_TAC o PURE_REWRITE_RULE [same])))) >>
  `cenv with ce_vars := cenv0.ce_vars = cenv0` by
    (drule compile_register_positional_args_cenv >> simp[compile_env_component_equality]) >>
  drule_all supported_selected_external_body >> strip_tac >>
  drule_all external_selected_args_distinct >> strip_tac >>
  `!id ty. MEM (id,ty) args ==>
    (?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) /\
    cenv.ce_var_type id = SOME ty` by
    (rpt strip_tac
     >- (irule external_entry_target_param_pointer >>
         goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> metis_tac[]) >>
     metis_tac[external_entry_target_param_type]) >>
  `!id loc. FLOOKUP cenv.ce_vars id = SOME loc ==> MEM id (MAP FST args)` by
    metis_tac[external_entry_target_declared] >>
  mp_tac (Q.SPECL [`tops`, `rpolicy`, `unit`, `am`, `tx`, `ret`,
    `vs`, `mut`, `F`, `args`, `[]`, `fbody`, `es0.gas_obs`, `es0`, `lbl`,
    `cenv0`, `pos_args`, `min_cds`, `is_payable`, `nkey`, `ut'`, `iv`, `rt`,
    `cenv`] external_source_body_frame_nr) >>
  qpat_assum `!id ty. MEM (id,ty) args ==> (?p sz. _) /\ _`
    (assume_tac o SIMP_RULE bool_ss [IMP_CONJ_THM, FORALL_AND_THM]) >>
  fs[subst_consts_expr_def, package_external_fn_def, FORALL_AND_THM] >>
  impl_tac >- first_assum ACCEPT_TAC >> simp[]
QED

Theorem external_body_frame:
  !tops rpolicy unit am tx ret vs mut args fbody env es0 lbl cenv0 pos_args
   min_cds is_payable nkey ut' iv rt st cenv sa.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INL (), es0) /\
    set_external_package_target rpolicy.rpol_target
      (package_external_fn tops T (K global_nonreentrant_slot)
         (mut, F, lookup_raw_return_or_F (NONE : num option)
                     tx.function_name External tops,
          tx.function_name, args, [], ret,
          subst_consts_stmts (module_consts_env tops []) fbody)) =
      (lbl, cenv0, pos_args, min_cds, is_payable, F, nkey, ut', iv, subst_consts_stmts (module_consts_env tops []) fbody,
       rt) /\
    compile_register_positional_args cenv0 pos_args 4 st = (cenv, sa) ==>
    body_inv tops unit.cu_context cenv
      (initial_evaluation_context am.sources am.layouts tx NONE) /\
    cenv.ce_return_pc = NONE /\
    ?bindings env_t env'.
      supported_stmts tops bindings (subst_consts_stmts (module_consts_env tops []) fbody) /\
      expr_sim_inv cenv
        (initial_evaluation_context am.sources am.layouts tx NONE) env_t es0 /\
      ce_locals_declared cenv env_t /\ locals_alloc_ok cenv env_t /\
      type_stmts env_t ret (subst_consts_stmts (module_consts_env tops []) fbody) = SOME env' /\
      stmts_exprs_ok cenv (subst_consts_stmts (module_consts_env tops []) fbody) /\
      call_evaluation_safe
        (initial_evaluation_context am.sources am.layouts tx NONE)
        (int_calls_stmts (subst_consts_stmts (module_consts_env tops []) fbody))
Proof
  rpt strip_tac >> drule_all external_source_body_frame >> simp[] >> metis_tac[]
QED
