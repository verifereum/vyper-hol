Theory externalReturnBoundaryPtr
Ancestors
  loweringHalt stmtLowering compileEnv emitHelper venomInst
  compileVyper entryStateRel bodySim

val _ = Parse.hide "body";

Theorem compile_return_none_external_code:
  compile_stmt cenv lctx ty (Return NONE) st = (x,st') /\
  cenv.ce_return_pc = NONE /\ cenv.ce_ctor_exit_label = NONE /\
  cenv.ce_nonreentrant = (nr,nkey,ut,iv) /\ (nr ==> iv) ==>
  st'.cs_current_bb = st.cs_current_bb /\
  st'.cs_current_insts = st.cs_current_insts ++
    [mk_inst st.cs_next_id STOP [] []]
Proof
  strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  simp[compile_stmt_def, optional_unlock_view, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, emit_inst_def,
       fresh_id_def, emit_def] >> rpt strip_tac >> gvs[]
QED

Theorem external_registered_no_ctor_exit:
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut,nr,rr,name,args,defaults,ret,body)) =
    (lbl,cenv0,pos,cds,payable,nr',key,ut,view,body',rt) /\
  compile_register_positional_args cenv0 pos off st = (cenv,sa) ==>
  cenv.ce_ctor_exit_label = NONE
Proof
  strip_tac >>
  drule compile_register_positional_args_cenv >> strip_tac >> gvs[] >>
  qpat_x_assum `set_external_package_target _ _ = _` mp_tac >>
  simp[package_external_fn_def, set_external_package_target_def] >>
  Cases_on `ret = NoneT` >>
  simp[update_cenv_nonreentrant_def, update_cenv_ret_abi_def] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `cenv = _` (fn th => once_rewrite_tac[th]) >> simp[]
QED
