(* Check that packaged CREATE-free bodies and their defaults remain CREATE-free. *)
Theory loweringCreatePackages
Ancestors
  loweringCreateSource loweringRuntimeOpcodes loweringGroupedOpcodes
  compileVyper compileEnv moduleLowering context ctorDeployDefs
  supportedExprTraverse supportedStmtTraverse constSubst list pair

Theorem build_compile_env_defaults:
  (build_compile_env tops vis mut name args ret bod trans).ce_func_defaults =
    build_func_defaults tops
Proof
  simp[build_compile_env_def] >> rpt (pairarg_tac >> gvs[])
QED

Theorem package_external_avoids_create:
  !tops trans keys target src.
    runtime_bodies_avoid_create tops /\
    MEM src (FST (classify_functions tops)) ==>
    external_package_avoids create_or_short_builtin_root
      (set_external_package_target target (package_external_fn tops trans keys src))
Proof
  rpt gen_tac >> PairCases_on `src` >> strip_tac >>
  `~supported_stmts_expr_exists create_or_short_builtin_root src7` by
    (fs[runtime_bodies_avoid_create_def] >> metis_tac[]) >>
  simp[package_external_fn_def, set_external_package_target_def,
       external_package_avoids_def, package_body_avoids_def] >>
  rpt CASE_TAC >>
  simp[update_cenv_ret_abi_def, update_cenv_nonreentrant_def, build_compile_env_defaults] >>
  metis_tac[runtime_bodies_avoid_create_func_defaults]
QED

Theorem package_internal_avoids_create:
  !tops trans keys target src ctor imm.
    runtime_bodies_avoid_create tops /\
    MEM src (FST (SND (classify_functions tops))) ==>
    internal_package_avoids create_or_short_builtin_root
      (set_internal_package_target target (package_internal_fn tops trans keys ctor imm src))
Proof
  rpt gen_tac >> PairCases_on `src` >> strip_tac >>
  `~supported_stmts_expr_exists create_or_short_builtin_root src7` by
    (fs[runtime_bodies_avoid_create_def] >> metis_tac[]) >>
  simp[package_internal_fn_def, set_internal_package_target_def,
       internal_package_avoids_def, package_body_avoids_def,
       update_cenv_nonreentrant_def, build_compile_env_defaults] >>
  metis_tac[runtime_bodies_avoid_create_func_defaults]
QED

Theorem package_fallback_avoids_create:
  runtime_bodies_avoid_create tops ==>
  fallback_package_avoids create_or_short_builtin_root
    (set_fallback_package_target target (package_fallback_fn tops trans keys
      (FST (SND (SND (classify_functions tops))))))
Proof
  strip_tac >> Cases_on `FST (SND (SND (classify_functions tops)))`
  >- simp[package_fallback_fn_def, set_fallback_package_target_def,
          fallback_package_avoids_def] >>
  rename1 `_ = SOME src` >> PairCases_on `src` >>
  `~supported_stmts_expr_exists create_or_short_builtin_root src7` by
    (fs[runtime_bodies_avoid_create_def] >> metis_tac[]) >>
  simp[package_fallback_fn_def, set_fallback_package_target_def,
       fallback_package_avoids_def, package_body_avoids_def] >>
  Cases_on `src6 = NoneT` >>
  simp[update_cenv_ret_abi_def, update_cenv_nonreentrant_def, build_compile_env_defaults] >>
  metis_tac[runtime_bodies_avoid_create_func_defaults]
QED

Theorem every_zip_defaults[local]:
  !args defs. LENGTH args = LENGTH defs /\
    EVERY (\e. ~supported_expr_exists create_or_short_builtin_root e) defs ==>
    EVERY (\(n,t,e). ~supported_expr_exists create_or_short_builtin_root e)
      (MAP (\((name,ty),default_e). (name,ty,default_e)) (ZIP (args,defs)))
Proof
  Induct >> Cases_on `defs` >> simp[pairTheory.FORALL_PROD]
QED

Theorem package_external_group_avoids_create:
  !tops trans keys target src.
    runtime_bodies_avoid_create tops /\
    MEM src (FST (classify_functions tops)) ==>
    external_group_avoids create_or_short_builtin_root
      (package_external_group tops target trans keys src)
Proof
  rpt gen_tac >> strip_tac >>
  `external_package_avoids create_or_short_builtin_root
    (set_external_package_target target (package_external_fn tops trans keys src))` by
    (irule package_external_avoids_create >> simp[]) >>
  PairCases_on `src` >>
  `LENGTH src5 <= LENGTH src4` by
    (fs[runtime_bodies_avoid_create_def] >> metis_tac[]) >>
  `EVERY (\e. ~supported_expr_exists create_or_short_builtin_root e) src5` by
    (fs[runtime_bodies_avoid_create_def] >> metis_tac[]) >>
  simp[package_external_group_def] >> IF_CASES_TAC
  >- simp[external_group_avoids_def] >>
  qmatch_asmsub_abbrev_tac `external_package_avoids _ pkg` >>
  PairCases_on `pkg` >>
  simp[external_group_avoids_def, kwarg_specs_avoid_def] >>
  fs[external_package_avoids_def] >>
  MATCH_MP_TAC every_zip_defaults >> simp[] >> decide_tac
QED
