(* Break, continue and no-reason raise use only their real compiler action
 * to construct the execution path.  The shadow action remains arbitrary.
 *)
Theory bodyFullExitActions
Ancestors
  bodyFullShared bodyFullHashKeccakFixed bodyFullPreds bodySimFull gasOutcomeFullCompose
  gasOutcomeFull fragGasEmitCtrl fragGasOriginPtr fragGasOrigin
  gasShadowState gasShadow bodyPtrDefs bodyMemoryDefs
  stmtSimProps stmtSimDefs exprSimDefs
  loweringPosts gasExemptCert fragGasPathPtr fragExec ptrDiscipline gasContext
  emitHelper emitHelperProps exprLoweringProps stmtLowering exprLowering
  compileEnv allocaHistory vyperStorageFootprint vyperStorageTrace
  vyperInterpreter vyperState vyperValue venomExecSemantics venomInst
  venomState list
Libs
  monadsyntax

Theorem compile_loop_jump_frag_full_action:
  !DF lo d ctx shadow_ctx PG func shadow_func cx lctx RetQ cenv ty st es shadow_action.
    (st = Break \/ st = Continue) ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ty st) shadow_action
      (eval_stmt cx st) es
Proof
  rpt gen_tac >>
  disch_then (DISJ_CASES_THEN SUBST_ALL_TAC) >> (
  pure_rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `lctx`
  >- (gvs[gas_admissible_def] >>
      first_x_assum (qspec_then `es.gas_obs` mp_tac) >>
      simp[Once evaluate_def, raise_def, stmt_res_ok_def]) >>
  rename1 `InLoop ex inc` >>
  qmatch_goalsub_abbrev_tac `eval_stmt cx st` >>
  qabbrev_tac `lbl = if st = Break then ex else inc` >>
  qabbrev_tac `exc = if st = Break then BreakException
                     else ContinueException` >>
  `eval_stmt cx st = raise exc` by
    (gvs[Abbr `exc`, Abbr `st`] >> simp[FUN_EQ_THM, Once evaluate_def]) >>
  `cenv' = cenv /\ emit_inst JMP [Label lbl] [] sa = ((), sb)` by
    (qpat_x_assum `stmt_env _ _ _ _ sa = _` mp_tac >>
     gvs[Abbr `lbl`, Abbr `st`] >>
     simp[stmt_env_def, declare_stmt_local_def, comp_ignore_bind_def,
          comp_bind_def, compile_stmt_def, comp_return_def] >>
     pairarg_tac >> simp[]) >>
  drule emit_inst_extends >> strip_tac >>
  `return_buf_frame d cenv sb s0` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`, `s0`, `sa`] >>
     simp[]) >>
  `alloca_history func (jump_to lbl s0)` by
    (irule alloca_history_jump >> simp[jump_to_def] >> metis_tac[]) >>
  irule gas_outcome_full_pure >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`G0`, `es`, `INR exc`, `jump_to lbl s0`, `tn0`] >>
  simp[raise_def] >> qx_gen_tac `H` >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `allocas_from lo s0` by fs[ghost_inv_at_def] >>
  conj_tac >- (irule emit_jmp_origin_ptr >> simp[] >> metis_tac[]) >>
  `stmt_state_rel H ctx func cenv cx (es with gas_obs := []) (jump_to lbl s0)`
    by (simp[stmt_state_rel_jump_to] >> drule msg_gas_state_frame >>
        disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`]
          mp_tac) >>
        simp[NoAsms]) >>
  `storage_well_formed_on cx (es with gas_obs := []) (FST H)` by
    (`(es with gas_obs := []).accounts = es.accounts /\
      (es with gas_obs := []).tStorage = es.tStorage` by simp[] >>
     metis_tac[storage_well_formed_on_backends]) >>
  `alloca_frame cenv es sa s0 cenv (es with gas_obs := []) (jump_to lbl s0)`
    by (irule alloca_frame_same >> simp[jump_to_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp (jump_to lbl s0)` by
    metis_tac[stmt_state_rel_allocas_below_fmp] >>
  qexists_tac `cenv` >>
  simp[stmt_lands_def, cenv_top_ext_refl, ghost_inv_at_jump_to,
       return_buf_frame_jump_to, return_buf_sep_jump, return_buf_sep_gas_obs] >>
  gvs[Abbr `lbl`, Abbr `exc`, Abbr `st`, jump_to_def, lookup_var_def])
QED

Theorem compile_raise_frag_full_action:
  !DF lo d ctx shadow_ctx PG func shadow_func cx lctx RetQ cenv ty rk es shadow_action.
    (rk = RaiseBare \/ rk = RaiseUnreachable) ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Raise rk)) shadow_action
      (eval_stmt cx (Raise rk)) es
Proof
  rpt gen_tac >>
  disch_then (DISJ_CASES_THEN SUBST_ALL_TAC) >> (
  pure_rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ sa = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  qmatch_goalsub_abbrev_tac `emit_inst opc ops [] sa` >>
  Cases_on `emit_inst opc ops [] sa` >> rename1 `_ = (u, sm)` >>
  Cases_on `u` >> simp[] >> strip_tac >> gvs[] >>
  fs[markerTheory.Abbrev_def] >>
  qmatch_goalsub_abbrev_tac `eval_stmt cx (Raise rk)` >>
  `?msg. !st. eval_stmt cx (Raise rk) st = (INR (AssertException msg), st) /\
              (opc = INVALID ==> msg = "UNREACHABLE")` by
    simp[Abbr `rk`, Once evaluate_def, raise_def] >>
  `?a t. step_inst_base (mk_inst sa.cs_next_id opc ops []) s0 = Abort a t /\
         expr_exit (INR (AssertException msg) : unit + exception) (Abort a t)` by
    (gvs[expr_exit_def] >> metis_tac[step_revert_zero, step_invalid]) >>
  `create_size_exit_ok ctx (INR (AssertException msg) : unit + exception) (Abort a t)` by
    (irule emit_abort_create_size_exit_ok >>
     qexistsl_tac [`func`, `opc`, `ops`, `s0`, `sa`, `sb`] >> simp[]) >>
  irule gas_outcome_full_exit >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`G0`, `es`, `Abort a t`, `INR (AssertException msg)`, `tn0`] >>
  simp[exit_result_def] >> qx_gen_tac `H` >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `allocas_from lo s0` by fs[ghost_inv_at_def] >>
  conj_tac >- (irule emit_abort_origin_ptr >> simp[] >> metis_tac[]) >>
  gvs[stmt_exit_ptr_def, halt_exit_def])
QED
