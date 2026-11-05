Theory extRetOperandBoundaryPtr
Ancestors
  extRetFrameFactsPtr returnMetadataPtr loweringShapeProps exprLoweringProps
  compileVyper compileEnv bodySim finite_map

Theorem local_ptrs_reserved_result_binding:
  local_ptrs_reserved cenv st /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
  not_fresh_at st p
Proof
  rw[local_ptrs_reserved_def] >> metis_tac[]
QED

Theorem external_frame_module_static:
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut, nr, rr, name, args, defaults, ret, fbody)) =
    (lbl, cenv0, pos, cds, payable, nr', key, ut, view, body', rt) /\
  compile_register_positional_args cenv0 pos off st = (cenv, sa) /\
  same_frame cenv next /\
  FLOOKUP next.ce_module_vars id = SOME loc ==>
  static_loc loc
Proof
  strip_tac >> drule_all register_same_frame_metadata >>
  simp[compile_env_component_equality] >> strip_tac >>
  qpat_x_assum `set_external_package_target _ _ = _` mp_tac >>
  simp[package_external_fn_def, set_external_package_target_def] >>
  Cases_on `ret = NoneT` >>
  simp[update_cenv_nonreentrant_def, update_cenv_ret_abi_def] >>
  strip_tac >> gvs[] >>
  drule (cj 2 (REWRITE_RULE [cenv_static_ok_def] build_compile_env_static)) >>
  simp[]
QED
