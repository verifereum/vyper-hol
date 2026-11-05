Theory extRetFrameFactsPtr
Ancestors
  returnMetadataPtr extRetMetadataProbePtr compileVyper compileEnv bodySim
  finite_map structFieldsProps retAbiPlanProps

Theorem build_external_return_buf_none[local]:
  (build_compile_env tops External mut name args ret fbody use_trans).ce_return_buf = NONE
Proof
  simp[build_compile_env_def] >> rpt (pairarg_tac >> gvs[])
QED

Theorem external_frame_control_metadata:
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut, F, rr, name, args, defaults, ret, fbody)) =
    (lbl, cenv0, pos, cds, payable, nr, key, ut, view, body', rt) /\
  compile_register_positional_args cenv0 pos off st = (cenv, sa) /\
  same_frame cenv next ==>
  next.ce_return_pc = NONE /\ next.ce_return_buf = NONE /\
  next.ce_ctor_exit_label = NONE /\
  next.ce_nonreentrant = (F, keys name, use_trans, mut = View) /\
  next.ce_raw_return = rr
Proof
  strip_tac >> drule_all register_same_frame_metadata >>
  simp[compile_env_component_equality] >> strip_tac >>
  qpat_x_assum `set_external_package_target _ _ = _` mp_tac >>
  simp[package_external_fn_def, set_external_package_target_def] >>
  Cases_on `ret = NoneT` >>
  simp[update_cenv_nonreentrant_def, update_cenv_ret_abi_def,
       build_compile_env_external_no_return_pc] >>
  strip_tac >> gvs[build_compile_env_external_no_return_pc,
                       build_external_return_buf_none]
QED

Theorem consistent_empty_struct_lookup:
  sfields_tenv_consistent sf tenv /\
  FLOOKUP tenv id = SOME (StructArgs []) ==>
  FLOOKUP sf (nsid_to_string id) = SOME []
Proof
  rw[sfields_tenv_consistent_def] >>
  first_x_assum drule >> simp[]
QED

Theorem supported_empty_struct_map_lookup:
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
  supported_struct_fields tops id = SOME [] ==>
  FLOOKUP (make_struct_fields_map tops) (nsid_to_string id) = SOME []
Proof
  strip_tac >> drule make_struct_fields_map_consistent >> strip_tac >>
  drule supported_struct_fields_type_env >> strip_tac >>
  irule consistent_empty_struct_lookup >> simp[] >> metis_tac[]
QED
