Theory deploySymSrcConstructorSource
Ancestors
  ctorDeployDefs runtimeSymSrcPackageTransport runtimeSymSrcInstructions
  runtimeSymSrcClassifiedSource
  runtimeSymSrcRuntimePackaging supportedProgram supportedStmts
  supportedExprTraverse compileVyper compileEnv list
  vyperTypeContract constSubstCorrect constSubst

Theorem deploy_sym_constructor_source:
  check_contract T layouts addr [(NONE,tops)] = SOME art /\
  constants_fold_module [(NONE,tops)] imms NONE tops FEMPTY = SOME A /\
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
  supported_program tops /\ supported_program_deploy tops /\
  ~program_reads_self_code tops /\
  SND (SND (SND (classify_functions tops))) =
    SOME (mut,nr,rr,name,args,defaults,ret,stmts) ==>
  supported_stmts tops
    (args ++ supported_stmts_bindings T stmts ++ supported_stmts_bindings F stmts) stmts /\
  ~supported_stmts_expr_exists is_self_code stmts
Proof
  strip_tac >> drule classify_functions_ctor_mem >> strip_tac >>
  drule_all runtime_sym_source_exclusions >> strip_tac >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`vis` |-> `Deploy`, `mode` |-> `T`] runtime_sym_checked_function_subst)) >>
  simp[supported_function_body_def] >>
  strip_tac >> gvs[subst_consts_fn_def]
QED

Theorem deploy_sym_constructor_package:
  check_contract T layouts addr [(NONE,tops)] = SOME art /\
  constants_fold_module [(NONE,tops)] imms NONE tops FEMPTY = SOME A /\
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
  supported_program tops /\ supported_program_deploy tops /\
  ~program_reads_self_code tops /\
  SND (SND (SND (classify_functions tops))) =
    SOME (mut,nr,rr,name,args,defaults,ret,fbody) /\
  set_constructor_package_target target
    (package_constructor tops trans keys (mut,nr,rr,name,args,defaults,ret,fbody)) =
    (ce,params,pay,nr',key,tr,stmts,rt) ==>
  runtime_sym_env tops ce /\
  ?bindings. supported_stmts tops bindings stmts /\
    ~supported_stmts_expr_exists is_self_code stmts /\
    (!ce'. runtime_sym_stmts_contract tops bindings compile_stmts ce' NoLoop NoneT stmts)
Proof
  strip_tac >> drule_all deploy_sym_constructor_source >> strip_tac >>
  gvs[package_constructor_def, set_constructor_package_target_def] >>
  conj_tac >- (irule runtime_sym_build_compile_env >>
    irule runtime_sym_build_compile_env_defaults >> metis_tac[]) >>
  goal_assum (drule_at Any) >> simp[runtime_sym_stmts_closed]
QED
