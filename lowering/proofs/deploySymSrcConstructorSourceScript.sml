Theory deploySymSrcConstructorSource
Ancestors
  ctorDeployDefs runtimeSymSrcPackageTransport runtimeSymSrcInstructions
  runtimeSymSrcClassifiedSource
  runtimeSymSrcRuntimePackaging supportedProgram supportedStmts
  supportedExprTraverse compileVyper compileEnv list

Theorem deploy_sym_constructor_source:
  supported_program tops /\ supported_program_deploy tops /\
  ~program_reads_self_code tops /\
  SND (SND (SND (classify_functions tops))) =
    SOME (mut,nr,rr,name,args,defaults,ret,stmts) ==>
  supported_stmts tops
    (args ++ supported_stmts_bindings T stmts ++ supported_stmts_bindings F stmts) stmts /\
  ~supported_stmts_expr_exists is_self_code stmts
Proof
  strip_tac >> drule classify_functions_ctor_mem >> strip_tac >>
  gvs[runtime_sym_supported_subst_consts_fn] >>
  drule_all supported_program_deploy_function >>
  simp[supported_function_body_def] >> strip_tac >>
  drule_all runtime_sym_source_exclusions >> simp[]
QED

Theorem deploy_sym_constructor_package:
  supported_program tops /\ supported_program_deploy tops /\
  ~program_reads_self_code tops /\
  SND (SND (SND (classify_functions tops))) =
    SOME (mut,nr,rr,name,args,defaults,ret,fbody) /\
  set_constructor_package_target target
    (package_constructor tops trans keys (mut,nr,rr,name,args,defaults,ret,fbody)) =
    (ce,params,pay,nr',key,tr,stmts,rt) ==>
  runtime_sym_env ce /\
  ?bindings. supported_stmts tops bindings stmts /\
    ~supported_stmts_expr_exists is_self_code stmts /\
    (!ce'. runtime_sym_stmts_contract tops bindings compile_stmts ce' NoLoop NoneT stmts)
Proof
  strip_tac >> drule_all deploy_sym_constructor_source >> strip_tac >>
  gvs[package_constructor_def, set_constructor_package_target_def] >>
  conj_tac >- simp[runtime_sym_build_compile_env] >>
  goal_assum (drule_at Any) >> simp[runtime_sym_stmts_closed]
QED
