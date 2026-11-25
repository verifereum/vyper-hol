Theory entryCreateDeployLayout
Ancestors
  entryCreateDeploySelected entryCreateIntervalLayout
  ctorDeployLoweringCode ctorDeployLoweringCodeShape
  ctorDeployEntryLabels moduleLowering compileVyper compileEnv fragExec
  e2eDeployDefs ctorDeployDefs ctorDeployLoweringDefs loweringShapeDefs list

(* Recover occurrence distinctness from the actual package.  The function in
   deploy_ctor_code is not used to identify the list of compiler occurrences. *)
Theorem deploy_ctor_packaged_body_span[local]:
  !tops am tx rpolicy runtime_bc dunit body cenv nr nkey ut imm exit_lbl
   sa sb sj st_exit st_epilogue st_final func.
  deploy_source_ok tops am tx /\
  deploy_ctor_code tops rpolicy runtime_bc dunit
    (body,cenv,nr,nkey,ut,imm,exit_lbl,sa,sb,sj,st_exit,st_epilogue,st_final,func) ==>
  cs_extends sa sb /\ cs_extends sb st_final /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks st_final))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `deploy_ctor_code _ _ _ _ _` mp_tac >>
  simp[deploy_ctor_code_def] >> strip_tac >>
  drule_all deploy_constructor_package_not_view >> strip_tac >>
  drule_all ctor_code_tail_extensions >> strip_tac >>
  `cs_extends sb st_final` by metis_tac[cs_extends_trans] >>
  drule_all deploy_ctor_lowering_trace >> strip_tac >>
  gvs[] >>
  rename1 `set_constructor_package_target _ _ = (cenv0,pos_args,pay,nr,nkey,ut,ss,_)` >>
  `compile_generate_deploy T (LENGTH runtime_bc) (imm_len tops) pos_args 0 []
    cenv0 ss pay nr nkey ut (initial_compile_state "__deploy") = ((),st_final)` by
    (PURE_REWRITE_TAC [compile_generate_deploy_def, COND_CLAUSES,
       ctor_code_cond_not, ctor_lock_flag_select] >>
     simp_tac bool_ss [comp_ignore_bind_def, comp_bind_def, comp_get_def, LET_THM] >>
     rpt (pairarg_tac >> gvs[]) >>
     gvs[compile_internal_fn_bodies_def, comp_return_def]) >>
  drule deploy_entry_blocks_not_internal >> strip_tac >>
  `supported_program tops` by fs[deploy_source_ok_def] >>
  qmatch_asmsub_abbrev_tac `compile_internal_fn_bodies ifns st_final` >>
  `ifns = MAP (set_internal_package_target rpolicy.rpol_target o
      package_internal_fn tops T (K global_nonreentrant_slot) T (imm_len tops))
      (order_internals (deploy_internal_order (SOME cf) ints) ints)` by
    simp[Abbr `ifns`] >>
  `PERM (order_internals (deploy_internal_order (SOME cf) ints) ints)
      (FST (SND (classify_functions tops)))` by
    simp[PERM_order_deploy_internals] >>
  drule_all deploy_internal_package_labels >> strip_tac >>
  drule_all deploy_ctor_packaged_entry_by_labels >> strip_tac >>
  drule_all deploy_ctor_member_certificates >> simp[]
QED

Theorem deploy_ctor_body_layout_at:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx
   body cenv nr nkey ut imm exit_lbl sa sb sj st_exit st_epilogue st_final f.
  deploy_phases policy tops (deploy_bc,runtime_bc) (rpolicy,dunit,dout,prog,cplan) /\
  deploy_source_ok tops am tx /\
  deploy_ctor_code tops rpolicy runtime_bc dunit
    (body,cenv,nr,nkey,ut,imm,exit_lbl,sa,sb,sj,st_exit,st_epilogue,st_final,f) ==>
  create_layout sa sb
Proof
  rpt gen_tac >> strip_tac >> drule_all deploy_ctor_packaged_body_span >> strip_tac >>
  `cs_extends sa st_final` by metis_tac[cs_extends_trans] >>
  drule_all create_layout_of_all_blocks >> strip_tac >>
  metis_tac[create_layout_subinterval, cs_extends_refl]
QED

Theorem deploy_body_create_cut_rule_of_layout:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx os.
  deploy_phases policy tops (deploy_bc,runtime_bc) (rpolicy,dunit,dout,prog,cplan) /\
  deploy_source_ok tops am tx /\
  (let C = dunit.cu_context;
       cx = deploy_evaluation_context tops am tx;
       st0 = initial_state am [];
       DF = \H. deploy_dead H tops runtime_bc am tx;
       lo = imm_len tops in
   !body cenv f Csh fsh sa sb sha shb base src G tn d k before key hit i s.
    create_layout sa sb /\
    (?mut source_body am_c es0.
      deploy_ctor_start tops am tx (mut,F,source_body,am_c,es0) /\
      src = es0 with outcomes := SOME os) /\
    (?nkey ut imm exit_lbl sj st_exit st_epilogue st_final.
      deploy_ctor_code tops rpolicy runtime_bc dunit
        (body,cenv,F,nkey,ut,imm,exit_lbl,sa,sb,sj,st_exit,st_epilogue,st_final,f)) /\
    compile_stmts cenv NoLoop NoneT body sa = ((),sb) /\
    compile_stmts (gas_shadow_env T cenv) NoLoop NoneT (MAP gas_shadow_stmt body)
      sha = ((),shb) /\
    shadow_body_inv tops C Csh /\ gas_shadow_context C Csh /\
    gas_shadow_function f fsh /\ gas_shadow_state sa sha /\ gas_shadow_state sb shb /\
    fn_has_code sa sb f /\ fn_has_code sha shb fsh /\
    MEM f C.ctx_functions /\ MEM fsh Csh.ctx_functions /\
    fn_inst_ids_distinct f /\ ctx_inst_ids_distinct C /\
    (!label bb. lookup_block label f.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
    local_ptrs_reserved cenv sa /\ ~block_is_terminated sa /\
    ~base.vs_halted /\ base.vs_current_bb = sa.cs_current_bb /\
    base.vs_inst_idx = LENGTH sa.cs_current_insts /\
    return_buf_frame NONE cenv sa base /\ alloca_history f base /\
    (ctx_has_dalloca C ==> allocas_below_fmp base) /\
    (!fn inst s. frag_reachable C f base fn inst s ==> dalloca_fmp_headroom inst s) /\
    (!H. valid_horizon cx st0 H src.storage_trace ==>
      stmt_state_rel H C f cenv cx src base /\
      ghost_inv_at (DF H) lo NONE cenv cx src G tn base) /\
    create_trace_from [] d k C f base = before ++ [(key,hit,i,s)] /\
    run_from k C f base = Abort ExHalt_abort (halt_state (set_returndata [] s)) /\
    ~inst_create_size_ok i s ==>
    create_body_cut (gas_explicit_sites C Csh) tops cx st0 (eval_stmts cx body)
      (src,base) (before,(key,hit,i,s)) \/
    ?n u. gas_path C f base n (OK u) /\ ~block_is_terminated sb /\
          ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
          u.vs_inst_idx = LENGTH sb.cs_current_insts) ==>
  deploy_body_create_cut_rule tops runtime_bc rpolicy dunit am tx os
Proof
  rpt gen_tac >> simp_tac std_ss [deploy_body_create_cut_rule_def, LET_THM] >>
  strip_tac >> rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `?nkey ut imm exit_lbl sj st_exit st_epilogue st_final.
    deploy_ctor_code _ _ _ _ _` strip_assume_tac >>
  `create_layout sa sb` by (drule_all deploy_ctor_body_layout_at >> simp[]) >>
  qpat_x_assum `!body cenv f Csh fsh sa sb sha shb base src G tn d k before key hit i s.
    create_layout sa sb /\ _ ==> _` irule >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  (conj_tac >- metis_tac[]) >> metis_tac[]
QED
