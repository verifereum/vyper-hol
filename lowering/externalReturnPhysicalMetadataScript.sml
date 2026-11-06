Theory externalReturnPhysicalMetadata
Ancestors
  externalReturnPackage compileVyper compileEnv bodySim entryStateRel

Theorem return_package_return_table:
  package_external_fn tops use_trans nkey_map
    (mut,nr,rr,fname,fargs,dflts,ret,fbody) =
    (lbl,cenv,pos_args,min_cds,is_payable,nr',nkey,ut,iv,ss,rt) ==>
  cenv.ce_func_return_type = build_func_return_type tops
Proof
  Cases_on `ret = NoneT` >>
  simp[package_external_fn_def, update_cenv_nonreentrant_def] >>
  strip_tac >> gvs[] >> simp[update_cenv_ret_abi_def] >>
  simp[build_compile_env_def] >> rpt (pairarg_tac >> gvs[])
QED

Theorem return_register_return_table:
  compile_register_positional_args ce args off st = (ce',st') ==>
  ce'.ce_func_return_type = ce.ce_func_return_type
Proof
  strip_tac >> drule compile_register_positional_args_cenv >> strip_tac >>
  qpat_x_assum `ce' = _` (fn th => once_rewrite_tac[th]) >> simp[]
QED

Theorem return_same_frame_return_table:
  same_frame ce ce' ==>
  ce'.ce_func_return_type = ce.ce_func_return_type
Proof
  simp[same_frame_def, compile_env_component_equality]
QED

Theorem return_selected_same_frame_return_table:
  set_external_package_target target
    (package_external_fn tops F nkey_map
      (mut,F,rr,fname,args,[],ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut,iv,fbody,rt) /\
  compile_register_positional_args cenv0 pos_args off st = (cenv,sa) /\
  same_frame cenv cenv' ==>
  cenv'.ce_func_return_type = build_func_return_type tops
Proof
  strip_tac >> drule return_package_target_inversion >> strip_tac >>
  drule return_package_return_table >> strip_tac >>
  drule return_register_return_table >> strip_tac >>
  drule return_same_frame_return_table >> strip_tac >> gvs[]
QED
