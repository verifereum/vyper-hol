Theory runtimeSymSrcPackageTransport
Ancestors
  runtimeSymSrcRuntimePackaging runtimeSymSrcEmission supportedProgram e2eProducers list
  supportedExprs supportedExprTraverse exprOracleStorageInterfaces runtimeSymSrcInterfaces
  runtimeSymSrcClassifiedSource
  compileVyper compileEnv loweringShapeProps constSubst pair

Theorem runtime_sym_source_exclusions:
  ~program_reads_self_code tops /\
  MEM (FunctionDecl vis mut nr rr name args defaults ret stmts) tops ==>
  ~supported_exprs_exists is_self_code defaults /\
  ~supported_stmts_expr_exists is_self_code stmts
Proof
  simp[program_reads_self_code_def, EXISTS_MEM] >> strip_tac >>
  first_x_assum (qspec_then `FunctionDecl vis mut nr rr name args defaults ret stmts` mp_tac) >>
  simp[]
QED

Theorem runtime_sym_source_fbody:
  vis <> Deploy /\ supported_program tops /\
  MEM (FunctionDecl vis mut nr rr name args defaults ret stmts) tops ==>
  supported_stmts tops
    (args ++ supported_stmts_bindings T stmts ++ supported_stmts_bindings F stmts)
    stmts
Proof
  strip_tac >> drule_all supported_program_function >>
  simp[supported_function_body_def]
QED

Theorem runtime_sym_source_default:
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
  supported_program tops /\ ~program_reads_self_code tops /\
  MEM (FunctionDecl vis mut nr rr name args defaults ret stmts) tops /\
  MEM e defaults ==>
  supported_expr tops e /\ ~supported_expr_exists is_self_code e
Proof
  strip_tac >> drule_all supported_program_defaults >>
  drule_all runtime_sym_source_exclusions >>
  simp[supported_exprs_exists_not_every, EVERY_MEM,
       supported_default_expression_def] >> metis_tac[]
QED

Theorem runtime_sym_build_compile_env_defaults:
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
  supported_program tops /\ ~program_reads_self_code tops ==>
  runtime_sym_defaults_ok tops (build_compile_env tops vis mut name args ret stmts trans).
    ce_func_defaults
Proof
  strip_tac >>
  simp[runtime_sym_defaults_ok_def, build_compile_env_ce_func_defaults,
       build_func_defaults_def, EVERY_MAP, EVERY_MEM] >>
  gen_tac >> strip_tac >> gvs[MEM_MAP] >> PairCases_on `y` >> gvs[] >>
  drule (iffLR MEM_classify_internal) >> strip_tac >>
  imp_res_tac runtime_sym_supported_function_subst >> gvs[] >>
  drule_all runtime_sym_source_exclusions >> strip_tac >>
  drule_all supported_program_declaration >>
  simp[supported_declaration_body_def, supported_pure_exprs_every, EVERY_MEM]
QED

Theorem runtime_sym_env_target[simp]:
  runtime_sym_env tops (ce with ce_target := target) = runtime_sym_env tops ce
Proof
  simp[runtime_sym_env_def]
QED

Theorem runtime_sym_env_raw[simp]:
  runtime_sym_env tops (ce with ce_raw_return := rr) = runtime_sym_env tops ce
Proof
  simp[runtime_sym_env_def]
QED

Theorem runtime_sym_env_ctor[simp]:
  runtime_sym_env tops (ce with ce_is_ctor := ctor) = runtime_sym_env tops ce
Proof
  simp[runtime_sym_env_def]
QED

Theorem runtime_sym_env_ret_abi[simp]:
  runtime_sym_env tops (update_cenv_ret_abi ce ty) = runtime_sym_env tops ce
Proof
  simp[update_cenv_ret_abi_def, runtime_sym_env_def]
QED

Theorem runtime_sym_env_nonreentrant[simp]:
  runtime_sym_env tops (update_cenv_nonreentrant ce nr key tr view) = runtime_sym_env tops ce
Proof
  simp[update_cenv_nonreentrant_def, runtime_sym_env_def]
QED

Theorem runtime_sym_external_environment:
  set_external_package_target target
    (package_external_fn tops trans keys source) =
      (lbl,ce,args,mincd,pay,nr,key,tr,view,stmts,ret) /\
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
  supported_program tops /\ ~program_reads_self_code tops ==>
  runtime_sym_env tops ce
Proof
  Cases_on `source` >> PairCases_on `r` >>
  simp[package_external_fn_def, set_external_package_target_def] >>
  IF_CASES_TAC >> strip_tac >> gvs[] >>
  simp[runtime_sym_build_compile_env, runtime_sym_build_compile_env_defaults]
QED

Theorem runtime_sym_internal_environment:
  set_internal_package_target target
    (package_internal_fn tops trans keys ctor imm source) =
      (lbl,ce,params,buf,nr,key,tr,view,ct,im,stmts,ret) /\
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
  supported_program tops /\ ~program_reads_self_code tops ==>
  runtime_sym_env tops ce
Proof
  Cases_on `source` >> PairCases_on `r` >>
  simp[package_internal_fn_def, set_internal_package_target_def] >>
  strip_tac >> gvs[] >>
  simp[runtime_sym_build_compile_env, runtime_sym_build_compile_env_defaults]
QED

Theorem runtime_sym_fallback_environment:
  set_fallback_package_target target
    (package_fallback_fn tops trans keys source) =
      SOME (ce,pay,nr,key,tr,view,stmts,ret) /\
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
  supported_program tops /\ ~program_reads_self_code tops ==>
  runtime_sym_env tops ce
Proof
  Cases_on `source` >> simp[package_fallback_fn_def, set_fallback_package_target_def] >>
  PairCases_on `x` >>
  simp[package_fallback_fn_def, set_fallback_package_target_def] >>
  IF_CASES_TAC >> strip_tac >>
  gvs[runtime_sym_build_compile_env, runtime_sym_build_compile_env_defaults]
QED

Theorem runtime_sym_prefixed_label:
  runtime_sym_label ("fn_" ++ name) /\
  runtime_sym_label (external_common_label name) /\
  runtime_sym_label (external_prefix_label name k)
Proof
  simp[runtime_sym_label_def, external_common_label_def,
       external_prefix_label_def]
QED


Theorem runtime_sym_external_package_fields:
  set_external_package_target target
    (package_external_fn tops trans keys
      (mut,nr,rr,name,args,defaults,ret,fbody)) =
      (lbl,ce,params,mincd,pay,nr',key,tr,view,stmts,rt) ==>
  stmts = fbody /\ runtime_sym_label lbl
Proof
  simp[package_external_fn_def, set_external_package_target_def] >>
  IF_CASES_TAC >> strip_tac >> gvs[runtime_sym_label_def]
QED

Theorem runtime_sym_internal_package_fields:
  set_internal_package_target target
    (package_internal_fn tops trans keys ctor imm
      (mut,nr,rr,name,args,defaults,ret,fbody)) =
      (lbl,ce,params,buf,nr',key,tr,view,ct,im,stmts,rt) ==>
  stmts = fbody /\ runtime_sym_label lbl
Proof
  simp[package_internal_fn_def, set_internal_package_target_def] >>
  strip_tac >> gvs[runtime_sym_internal_label]
QED

Theorem runtime_sym_fallback_package_fbody:
  set_fallback_package_target target
    (package_fallback_fn tops trans keys
      (SOME (mut,nr,rr,name,args,defaults,ret,fbody))) =
      SOME (ce,pay,nr',key,tr,view,stmts,rt) ==>
  stmts = fbody
Proof
  simp[package_fallback_fn_def, set_fallback_package_target_def] >>
  strip_tac >> gvs[]
QED

Theorem runtime_sym_group_environment:
  package_external_group tops target trans keys
    (mut,nr,rr,name,args,defaults,ret,fbody) =
      ExternalDefaults common entries specs mincd /\
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
  supported_program tops /\ ~program_reads_self_code tops ==>
  runtime_sym_env tops common.ec_env
Proof
  simp[package_external_group_def] >>
  pairarg_tac >> gvs[] >> IF_CASES_TAC >> simp[] >> strip_tac >> gvs[] >>
  drule_all runtime_sym_external_environment >> simp[]
QED

Theorem runtime_sym_group_body:
  package_external_group tops target trans keys
    (mut,nr,rr,name,args,defaults,ret,fbody) =
      ExternalDefaults common entries specs mincd ==>
  common.ec_body = fbody /\
  runtime_sym_label common.ec_common_label
Proof
  simp[package_external_group_def] >>
  pairarg_tac >> gvs[] >> IF_CASES_TAC >> simp[] >> strip_tac >> gvs[] >>
  drule runtime_sym_external_package_fields >>
  simp[runtime_sym_prefixed_label]
QED

Theorem runtime_sym_group_entry_labels:
  package_external_group tops target trans keys
    (mut,nr,rr,name,args,defaults,ret,fbody) =
      ExternalDefaults common entries specs mincd ==>
  !sel lbl minsize k. MEM (sel,lbl,minsize,k) entries ==>
    runtime_sym_label lbl
Proof
  simp[package_external_group_def] >>
  pairarg_tac >> gvs[] >> IF_CASES_TAC >> simp[] >> strip_tac >> gvs[] >>
  simp[MEM_MAP, FORALL_PROD] >> rpt strip_tac >>
  PairCases_on `y` >> gvs[] >>
  pairarg_tac >> gvs[runtime_sym_label_def, external_prefix_label_def]
QED

Theorem runtime_sym_group_default_source:
  package_external_group tops target trans keys
    (mut,nr,rr,name,args,defaults,ret,fbody) =
      ExternalDefaults common entries specs mincd /\
  LENGTH defaults <= LENGTH args /\ MEM (n,ty,e) specs ==>
  MEM e defaults
Proof
  simp[package_external_group_def] >>
  pairarg_tac >> gvs[] >> IF_CASES_TAC >> simp[] >> strip_tac >> gvs[] >>
  gvs[MEM_MAP, EXISTS_PROD] >>
  drule_at (Pat `MEM _ (ZIP _)`) MEM_ZIP_MEM_MAP >> simp[]
QED

Theorem runtime_sym_external_source:
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
  supported_program tops /\ ~program_reads_self_code tops /\
  MEM (mut,nr,rr,name,args,defaults,ret,stmts) (FST (classify_functions tops)) ==>
  (supported_stmts tops
    (args ++ supported_stmts_bindings T stmts ++ supported_stmts_bindings F stmts) stmts /\
   ~supported_stmts_expr_exists is_self_code stmts /\
   (!e. MEM e defaults ==> supported_expr tops e /\ ~supported_expr_exists is_self_code e)) \/
  (?top rawdefaults rawbody. MEM top tops /\
    public_getter top = SOME (mut,nr,rr,name,args,rawdefaults:expr list,ret,rawbody) /\
    stmts = subst_consts_stmts (module_consts_env tops []) rawbody)
Proof
  strip_tac >> drule classify_functions_external_source >> strip_tac >>
  imp_res_tac runtime_sym_supported_function_subst >> gvs[]
  >- (disj1_tac >>
      `External <> Deploy` by simp[] >>
      drule_all runtime_sym_source_fbody >>
      drule_all runtime_sym_source_exclusions >> rpt strip_tac >>
      metis_tac[runtime_sym_source_default]) >>
  disj2_tac >> qexistsl_tac [`top`, `rawdefaults`, `rawbody`] >>
  gvs[subst_consts_fn_def]
QED

Theorem runtime_sym_internal_source:
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
  supported_program tops /\ ~program_reads_self_code tops /\
  MEM (mut,nr,rr,name,args,defaults,ret,stmts) (FST (SND (classify_functions tops))) ==>
  supported_stmts tops
    (args ++ supported_stmts_bindings T stmts ++ supported_stmts_bindings F stmts) stmts /\
  ~supported_stmts_expr_exists is_self_code stmts
Proof
  strip_tac >> gvs[MEM_classify_internal] >>
  imp_res_tac runtime_sym_supported_function_subst >> gvs[] >>
  `Internal <> Deploy` by simp[] >>
  drule_all runtime_sym_source_fbody >>
  drule_all runtime_sym_source_exclusions >> simp[]
QED

Theorem runtime_sym_fallback_source:
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
  supported_program tops /\ ~program_reads_self_code tops /\
  FST (SND (SND (classify_functions tops))) =
    SOME (mut,nr,rr,name,args,defaults,ret,stmts) ==>
  supported_stmts tops
    (args ++ supported_stmts_bindings T stmts ++ supported_stmts_bindings F stmts) stmts /\
  ~supported_stmts_expr_exists is_self_code stmts
Proof
  strip_tac >> drule classify_functions_fallback_mem >> strip_tac >>
  imp_res_tac runtime_sym_supported_function_subst >> gvs[] >>
  `External <> Deploy` by simp[] >>
  drule_all runtime_sym_source_fbody >>
  drule_all runtime_sym_source_exclusions >> simp[]
QED
