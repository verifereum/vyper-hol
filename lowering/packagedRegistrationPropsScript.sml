(* Registration properties at a target-adjusted external package. *)
Theory packagedRegistrationProps
Ancestors entryLocals entryStateRel intCallCallee compileVyper compileEnv
  moduleLowering list finite_map

Theorem target_external_registration_locals:
  !tops ut keys mut nr rr name args dflts ret fbody target lbl cenv0 pos_args
   rest off st cenv sa.
  set_external_package_target target
    (package_external_fn tops ut keys (mut,nr,rr,name,args,dflts,ret,fbody)) =
    (lbl,cenv0,pos_args,rest) /\
  compile_register_positional_args cenv0 pos_args off st = (cenv,sa) ==>
  local_ptrs_reserved cenv sa /\ cenv.ce_return_buf = NONE
Proof
  rpt gen_tac >> strip_tac >>
  `cenv0.ce_vars = (build_compile_env tops External mut name args ret fbody ut).ce_vars /\
   cenv0.ce_imm_alloca = NONE /\ cenv0.ce_return_buf = NONE /\
   MAP FST pos_args = MAP FST args` by
    (qpat_x_assum `set_external_package_target _ _ = _` mp_tac >>
     simp[set_external_package_target_def, package_external_fn_def,
       update_cenv_nonreentrant_def] >>
     rw[update_cenv_ret_abi_def] >>
     simp[build_compile_env_imm_alloca, build_positional_args_FST,
       build_compile_env_def, pairTheory.UNCURRY]) >>
  qspecl_then [`tops`, `External`, `mut`, `name`, `args`, `ret`, `fbody`, `ut`]
    strip_assume_tac build_compile_env_vars >>
  conj_tac
  >- (drule compile_register_positional_args_reserved >>
      impl_tac >- gvs[] >> simp[]) >>
  drule compile_register_positional_args_cenv >> strip_tac >>
  qpat_x_assum `cenv = _` SUBST1_TAC >> simp[]
QED
