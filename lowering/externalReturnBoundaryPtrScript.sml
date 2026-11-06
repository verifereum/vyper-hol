Theory externalReturnBoundaryPtr
Ancestors
  loweringHalt stmtLowering compileEnv emitHelper venomInst
  compileVyper entryStateRel bodySim bodyPtrDefs fragExecPtr fragExec stmtSim
  ptrSafeRun ptrDiscipline venomState venomExecSemantics contextCodegenRelProps

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

Theorem external_return_none_stmt_frag_ptr:
  cenv.ce_return_pc = NONE /\ cenv.ce_ctor_exit_label = NONE /\
  cenv.ce_nonreentrant = (nr,nkey,ut,iv) /\ (nr ==> iv) /\
  eval_stmt cx (Return NONE) es = (INR (ReturnException v),es') ==>
  stmt_frag_ptr d ctx PG func cx lctx (\v es gt r. T) cenv
    (stmt_env cenv lctx ret_ty (Return NONE)) es
    (INR (ReturnException v)) es'
Proof
  strip_tac >> simp[stmt_frag_ptr_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  drule_all compile_return_none_external_code >> strip_tac >>
  disj2_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s0.vs_inst_idx =
    SOME (mk_inst sa.cs_next_id STOP [] [])` by
    (qpat_x_assum `!i. _` (qspec_then `0` mp_tac) >> simp[]) >>
  `run_from 0 ctx func s0 = Halt (halt_state (s0 with vs_returndata := []))` by
    (irule run_from_halt >>
     qexistsl [`bb`, `mk_inst sa.cs_next_id STOP [] []`] >>
     simp[mk_inst_def, step_inst_non_invoke] >>
     PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> simp[mk_inst_def]) >>
  qexists `0` >> simp[exit_result_def, stmt_exit_ptr_def] >>
  irule ptr_safe_run_stop >> simp[] >>
  conj_tac >- (qexists `sa.cs_next_id` >> gvs[]) >>
  gvs[ghost_inv_def]
QED
