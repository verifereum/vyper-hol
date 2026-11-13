Theory bodyPtrStructLitOwnershipModuleEnvironment
Ancestors
  compileVyper loweringShapeProps

Theorem build_compile_env_alloca_locals:
  !tops vis mut fname args ret (body : stmt list) use_trans.
    (build_compile_env tops vis mut fname args ret body use_trans).
      ce_alloca_locals
Proof
  rpt gen_tac >> simp[build_compile_env_def] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem build_compile_env_noninternal_shape:
  !tops vis mut fname args ret (body : stmt list) use_trans st.
    vis <> Internal /\
    EVERY (\nd. ~supported_exprs_exists expr_shape_root (SND nd))
      (build_func_defaults tops) ==>
    cenv_shape_ok st
      (build_compile_env tops vis mut fname args ret body use_trans)
Proof
  rpt strip_tac >> irule cenv_static_ok_shape_ok >>
  drule build_compile_env_static >> strip_tac >> simp[] >>
  Cases_on `vis` >>
  gvs[build_compile_env_external_no_return_pc,
      build_compile_env_deploy_no_internal_return]
QED
