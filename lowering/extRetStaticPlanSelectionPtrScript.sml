Theory extRetStaticPlanSelectionPtr
Ancestors returnMetadataPtr exprLowering compileEnv compileVyper

Theorem type_to_abi_enc_info_static_copy:
  ret <> NoneT /\ ~is_abi_dynamic cenv.ce_struct_fields ret ==>
  type_to_abi_enc_info sfields cenv ret = AbiCopy (type_memory_bytes cenv ret)
Proof
  strip_tac >> Cases_on `ret` >>
  gvs[type_to_abi_enc_info_def]
  >~ [`BaseT bt`]
  >- (Cases_on `bt` >> gvs[type_to_abi_enc_info_def, is_abi_dynamic_def] >>
      rename1 `BytesT bd` >> Cases_on `bd` >>
      gvs[type_to_abi_enc_info_def, is_abi_dynamic_def]) >>
  rename1 `ArrayT elem bd` >> Cases_on `bd` >>
  gvs[type_to_abi_enc_info_def, is_abi_dynamic_def]
QED

Theorem external_frame_static_copy_selection:
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut, nr, rr, name, args, defaults, ret, fbody)) =
    (lbl, cenv0, pos, cds, payable, nr', key, ut, view, fbody', rt) /\
  compile_register_positional_args cenv0 pos off st = (cenv, sa) /\
  same_frame cenv next /\ ret <> NoneT /\
  ~is_abi_dynamic next.ce_struct_fields ret ==>
  next.ce_ret_enc_info = AbiCopy (type_memory_bytes next ret)
Proof
  strip_tac >> drule_all register_same_frame_metadata >>
  simp[compile_env_component_equality] >> strip_tac >>
  `type_memory_bytes next ret = type_memory_bytes cenv0 ret` by
    (irule type_memory_bytes_struct_fields >> simp[]) >>
  `~is_abi_dynamic cenv0.ce_struct_fields ret` by metis_tac[] >>
  qpat_x_assum `set_external_package_target _ _ = _` mp_tac >>
  simp[package_external_fn_def, set_external_package_target_def] >>
  simp[update_cenv_nonreentrant_def, update_cenv_ret_abi_def] >>
  strip_tac >> gvs[] >>
  simp[type_to_abi_enc_info_static_copy] >>
  irule type_memory_bytes_struct_fields >> simp[]
QED
