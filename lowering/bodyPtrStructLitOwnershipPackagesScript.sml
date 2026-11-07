Theory bodyPtrStructLitOwnershipPackages
Ancestors bodyPtrStructLitOwnershipModuleEnvironment
  bodyPtrStructLitOwnershipSources compileVyper compileEnv
  loweringShapeProps loweringShapeDefs list pair

Theorem structlit_external_package_alloca_mode:
  !tops tr nk target src.
  (\(lbl,ce,args,cds,pay,nr,key,t,view,body,rt). ce.ce_alloca_locals)
    (set_external_package_target target (package_external_fn tops tr nk src))
Proof
  rpt gen_tac >> PairCases_on `src` >>
  simp[set_external_package_target_def, package_external_fn_def,
    update_cenv_ret_abi_def, update_cenv_nonreentrant_def,
    build_compile_env_alloca_locals] >>
  IF_CASES_TAC >> simp[build_compile_env_alloca_locals]
QED

Theorem structlit_fallback_package_alloca_mode:
  !tops tr nk target src.
  (case set_fallback_package_target target (package_fallback_fn tops tr nk src) of
     NONE => T | SOME (ce,pay,nr,key,trans,view,stmts,rt) => ce.ce_alloca_locals)
Proof
  rpt gen_tac >> Cases_on `src`
  >- simp[set_fallback_package_target_def, package_fallback_fn_def] >>
  PairCases_on `x` >>
  simp[set_fallback_package_target_def, package_fallback_fn_def,
    build_compile_env_alloca_locals]
QED

Theorem structlit_internal_package_label:
  !tops tr nk ctor ilen target src.
  internal_label_ok (FST (set_internal_package_target target
    (package_internal_fn tops tr nk ctor ilen src)))
Proof
  rpt gen_tac >> PairCases_on `src` >>
  SIMP_TAC bool_ss [set_internal_package_target_def, package_internal_fn_def,
    LET_THM, pairTheory.FST, internal_label_ok_def] >>
  REWRITE_TAC [internal_fn_label_prefix]
QED

Theorem structlit_internal_package_shape:
  !tops tr nk ctor ilen target src.
  supported_program tops /\ MEM src (FST (SND (classify_functions tops))) ==>
  internal_fn_shape_ok (set_internal_package_target target
    (package_internal_fn tops tr nk ctor ilen src))
Proof
  rpt gen_tac >> PairCases_on `src` >> strip_tac >>
  `~supported_stmts_expr_exists expr_shape_root src7` by
    (drule (iffLR MEM_classify_internal) >> strip_tac >>
     drule supported_program_runtime_bodies_shape_ok >>
     simp[runtime_bodies_shape_ok_def] >> strip_tac >>
     first_x_assum drule >> simp[]) >>
  simp[package_internal_fn_def, set_internal_package_target_def,
    update_cenv_nonreentrant_def, internal_fn_shape_ok_def,
    cenv_static_ok_def] >>
  metis_tac[build_compile_env_static, cenv_static_ok_def]
QED

Theorem structlit_constructor_package_environment:
  !tops tr nk target src.
  (\(ce,args,pay,nr,key,t,body,rt).
    cenv_static_ok ce /\ ce.ce_return_pc = NONE /\ ce.ce_alloca_locals)
    (set_constructor_package_target target (package_constructor tops tr nk src))
Proof
  rpt gen_tac >> PairCases_on `src` >>
  simp[set_constructor_package_target_def, package_constructor_def,
    update_cenv_nonreentrant_def, cenv_static_ok_def,
    build_compile_env_alloca_locals, build_compile_env_deploy_no_internal_return] >>
  metis_tac[build_compile_env_static, cenv_static_ok_def]
QED

Theorem structlit_constructor_package_body:
  !tops tr nk target mut nr rr name args defaults ret body.
  supported_program tops /\
  SND (SND (SND (classify_functions tops))) =
    SOME (mut,nr,rr,name,args,defaults,ret,body) ==>
  (\(ce,a,p,n,k,t,stmts,r).
    ~supported_stmts_expr_exists expr_shape_root stmts)
    (set_constructor_package_target target
      (package_constructor tops tr nk (mut,nr,rr,name,args,defaults,ret,body)))
Proof
  rpt gen_tac >> strip_tac >>
  simp[set_constructor_package_target_def, package_constructor_def] >>
  drule structlit_classify_constructor_source >> strip_tac >>
  drule_all structlit_supported_function_body >> simp[]
QED
