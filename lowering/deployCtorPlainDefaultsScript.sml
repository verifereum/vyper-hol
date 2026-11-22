(* The constructor's re-keyed compile environment is unchanged when none
   of the internal defaults can read msg.gas, even after constant folding. *)
Theory deployCtorPlainDefaults
Ancestors
  ctorDeployLoweringDefs ctorDeployDefs ctorDeployLoweringArms e2eDeployDefs
  compileVyper compileEnv loweringFunctionOpcodes loweringShapeProps constSubstStmtsPreserve
  gasShadowCompileBase gasShadowShape supportedProgram supportedExprTraverse
  constSubst finite_map alist list pair

Theorem deploy_ctor_code_defaults[local]:
  deploy_ctor_code tops rpolicy runtime_bc dunit
    (stmts,cenv,nr,nkey,ut,imm,exit_lbl,sa,sb,sj,st_exit,st_epilogue,st_final,func) ==>
  cenv.ce_func_defaults = build_func_defaults tops
Proof
  simp[deploy_ctor_code_def] >> strip_tac >> simp[] >>
  qpat_assum `compile_register_constructor_args _ _ _ _ _ = _`
    (mp_tac o Q.AP_TERM `\p. (FST p).ce_func_defaults`) >>
  simp[register_constructor_args_defaults] >> disch_then (rewrite_tac o single o GSYM) >>
  qpat_x_assum `set_constructor_package_target _ _ = _` mp_tac >>
  PairCases_on `cf` >>
  simp[set_constructor_package_target_def, package_constructor_def,
       update_cenv_nonreentrant_def] >>
  strip_tac >> gvs[build_compile_env_ce_func_defaults]
QED

Theorem classified_plain_defaults_shadow_id[local]:
  ~internal_defaults_msg_gas tops /\
  check_contract mode layouts addr [(NONE,tops)] = SOME art /\
  constants_fold_module [(NONE,tops)] imms NONE tops FEMPTY = SOME A ==>
  MAP (I ## MAP gas_shadow_expr) (build_func_defaults tops) = build_func_defaults tops
Proof
  strip_tac >>
  `MAP (I ## MAP gas_shadow_expr) (build_func_defaults tops) =
   MAP I (build_func_defaults tops)` suffices_by simp[] >>
  pure_rewrite_tac[MAP_EQ_f] >>
  simp[build_func_defaults_def, MEM_MAP] >>
  gen_tac >> strip_tac >> PairCases_on `y` >> gvs[] >>
  drule (iffLR MEM_classify_internal) >> strip_tac >>
  `~supported_exprs_exists expr_msg_gas_root rawdflts` by
    (qpat_x_assum `~internal_defaults_msg_gas tops` mp_tac >>
     simp[internal_defaults_msg_gas_def, EXISTS_MEM] >>
     disch_then (qspec_then `FunctionDecl Internal y0 y1 y2 y3 y4 rawdflts y6 rawbody` mp_tac) >>
     simp[supported_exprs_exists_every, EVERY_MEM] >> metis_tac[]) >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`mods` |-> `[(NONE,tops)]`] module_consts_defaults_no_msg_gas)) >>
  disch_then (mp_tac o Q.SPEC `0` o MATCH_MP omitted_defaults_gas_shadow_id) >>
  gvs[subst_consts_fn_def]
QED

Theorem deploy_ctor_plain_defaults_shadow_env:
  ~internal_defaults_msg_gas tops /\
  deploy_source_ok tops am tx /\
  deploy_ctor_start tops am tx (mut,nr',body',am_c,es0) /\
  deploy_ctor_code tops rpolicy runtime_bc dunit
    (stmts,cenv,nr,nkey,ut,imm,exit_lbl,sa,sb,sj,st_exit,st_epilogue,st_final,func) ==>
  gas_shadow_env T cenv = cenv
Proof
  strip_tac >>
  drule_all deploy_ctor_constant_cells >> strip_tac >>
  `?art. check_contract T am.layouts tx.target [(NONE,tops)] = SOME art` by
    fs[deploy_source_ok_def, deploy_typing_ok_def] >>
  drule_all classified_plain_defaults_shadow_id >> strip_tac >>
  drule deploy_ctor_code_defaults >> strip_tac >>
  simp[gas_shadow_env_def, compile_env_component_equality]
QED
