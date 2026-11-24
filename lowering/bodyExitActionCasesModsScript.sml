(* The no-operand control actions have no counted sites and leave the
   source state alone. A loop landing preserves every module's frame. *)
Theory bodyExitActionCasesMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods bodyFullShadowBodyInv bodyInvSplit
  bodyFullShared bodyMemoryDefs bodyPtrDefs bodySimFull gasOutcomeFullMods
  gasOutcomeFull gasStorage gasSummary gasContext fragGasEmitCtrl fragExec
  exprLoweringProps stmtLowering exprLowering compileEnv gasShadow
  stmtSimProps stmtSimDefs exprSimDefs loweringPosts loweringStateRelDefs
  allocaHistory ptrDiscipline emitHelper emitHelperProps vyperStorageFootprint
  vyperInterpreter vyperState venomExecSemantics venomInst venomState

Theorem gas_outcome_mods_unchanged[local]:
  ~s.vs_halted /\
  (!tail. source (es with gas_obs := tail) = (res, es with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
       (s, G, tn) [] (r, G', tn') /\
     ((?t. r = OK t /\ Q H res (es with gas_obs := []) G' tn' t) \/
      (exit_result r /\ R H res (es with gas_obs := []) (G', tn') r))) ==>
  gas_outcome_full_mods (DF, lo, explicit, ctx, func, PG) mods cx st0 source
    (es, s, G, tn) Q R
Proof
  strip_tac >> rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `[]` >>
  Cases_on `storage_trace_domain cx st0 es.storage_trace`
  >- (disj2_tac >> disj1_tac >> qexistsl_tac [`res`, `es`, `r`, `G'`, `tn'`] >>
      simp[gas_explicit_def]) >>
  disj1_tac >> conj_tac >- simp[gas_bad_storage_at_def, gas_explicit_def] >>
  qexistsl_tac [`ARB`, `func`, `PG`, `G`, `tn`, `s`] >>
  simp[gas_origin_ptr_focus_nil]
QED

Theorem immutable_frame_mods_jump[local]:
  immutable_frame_mods func cenv cx (es with gas_obs := gs) (jump_to lbl s) <=>
  immutable_frame_mods func cenv cx es s
Proof
  simp[immutable_frame_mods_def, immutables_rel_mods_def,
       immutable_alloca_sep_mods_def, immutables_rel_def, immutable_alloca_sep_def,
       jump_to_def, local_region_def, lookup_var_def]
QED

Theorem ghost_inv_at_mods_jump[local]:
  ghost_inv_at_mods D lo d cenv cx (es with gas_obs := gs) G tn (jump_to lbl s) <=>
  ghost_inv_at_mods D lo d cenv cx es G tn s
Proof
  simp[ghost_inv_at_mods_def, jump_to_def, ptr_covers_def, stor_taint_ok_at_def,
       lookup_var_def, allocas_from_def] >>
  Cases_on `d` >- simp[return_buf_ptr_def] >>
  PairCases_on `x` >> simp[return_buf_ptr_def, ptr_covers_def, lookup_var_def]
QED

Theorem loop_jump_frag_full_mods[local]:
  !DF lo d ctx shadow_ctx PG func shadow_func cx lctx RetQ cenv ty st es shadow_action.
    (st = Break \/ st = Continue) ==>
    stmt_frag_full_mods (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv (stmt_env cenv lctx ty st) shadow_action (eval_stmt cx st) es
Proof
  rpt gen_tac >> disch_tac >> pure_rewrite_tac[stmt_frag_full_mods_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `lctx`
  >- (qpat_x_assum `gas_admissible _ _ _` (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
      disch_then (qspec_then `es.gas_obs` mp_tac) >>
      qpat_x_assum `st = Break \/ st = Continue` (DISJ_CASES_THEN SUBST_ALL_TAC) >>
      simp[Once evaluate_def, raise_def, stmt_res_ok_def]) >>
  rename1 `InLoop ex inc` >>
  qabbrev_tac `lbl = if st = Break then ex else inc` >>
  qabbrev_tac `exc = if st = Break then BreakException else ContinueException` >>
  `eval_stmt cx st = raise exc` by
    (qpat_x_assum `st = Break \/ st = Continue` (DISJ_CASES_THEN SUBST_ALL_TAC) >>
     simp[Abbr `exc`, FUN_EQ_THM, Once evaluate_def]) >>
  `cenv' = cenv /\ emit_inst JMP [Label lbl] [] sa = ((), sb)` by
    (qpat_x_assum `stmt_env _ _ _ _ sa = _` mp_tac >>
     qpat_x_assum `st = Break \/ st = Continue` (DISJ_CASES_THEN SUBST_ALL_TAC) >>
     simp[Abbr `lbl`, stmt_env_def, declare_stmt_local_def, comp_ignore_bind_def,
          comp_bind_def, compile_stmt_def, comp_return_def] >> pairarg_tac >> simp[]) >>
  drule emit_inst_extends >> strip_tac >>
  `return_buf_frame d cenv sb s0` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`, `s0`, `sa`] >> simp[]) >>
  `alloca_history func (jump_to lbl s0)` by
    (irule alloca_history_jump >> simp[jump_to_def] >> qexists_tac `s0` >> simp[]) >>
  irule gas_outcome_mods_unchanged >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`G0`, `OK (jump_to lbl s0)`, `INR exc`, `tn0`] >>
  simp[raise_def] >> qx_gen_tac `H` >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` drule >> strip_tac >>
  `allocas_from lo s0` by fs[ghost_inv_at_mods_def] >>
  conj_tac >- (irule emit_jmp_origin_ptr >> simp[] >> qexistsl_tac [`sa`, `sb`] >> simp[]) >>
  `storage_well_formed_on cx (es with gas_obs := []) (FST H)` by
    (irule (iffLR storage_well_formed_on_backends) >> qexists_tac `es` >> simp[]) >>
  `alloca_frame cenv es sa s0 cenv es (jump_to lbl s0)` by
    (irule alloca_frame_same >> simp[jump_to_def]) >>
  `(allocas_below_fmp (jump_to lbl s0) <=> allocas_below_fmp s0)` by
    simp[allocas_below_fmp_def, jump_to_def] >>
  disj1_tac >> qexists_tac `cenv` >>
  simp[stmt_lands_def, cenv_top_ext_refl, ghost_inv_at_mods_jump, immutable_frame_mods_jump,
       stmt_state_rel_jump_to, return_buf_frame_jump_to, return_buf_sep_jump,
       return_buf_sep_gas_obs] >>
  qpat_x_assum `st = Break \/ st = Continue` (DISJ_CASES_THEN SUBST_ALL_TAC) >>
  gvs[Abbr `lbl`, Abbr `exc`, jump_to_def, lookup_var_def]
QED

Theorem raise_frag_full_mods[local]:
  !DF lo d ctx shadow_ctx PG func shadow_func cx lctx RetQ cenv ty rk es shadow_action.
    (rk = RaiseBare \/ rk = RaiseUnreachable) ==>
    stmt_frag_full_mods (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv (stmt_env cenv lctx ty (Raise rk)) shadow_action
      (eval_stmt cx (Raise rk)) es
Proof
  rpt gen_tac >> disch_tac >> pure_rewrite_tac[stmt_frag_full_mods_def] >>
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `opc = if rk = RaiseBare then REVERT else INVALID` >>
  qabbrev_tac `ops = if rk = RaiseBare then [Lit 0w; Lit 0w] else []` >>
  qabbrev_tac `msg = if rk = RaiseBare then "" else "UNREACHABLE"` >>
  `cenv' = cenv /\ emit_inst opc ops [] sa = ((), sb)` by
    (qpat_x_assum `stmt_env _ _ _ _ sa = _` mp_tac >>
     qpat_x_assum `rk = RaiseBare \/ rk = RaiseUnreachable` (DISJ_CASES_THEN SUBST_ALL_TAC) >>
     simp[Abbr `opc`, Abbr `ops`, stmt_env_def, declare_stmt_local_def,
          compile_stmt_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     pairarg_tac >> simp[]) >>
  `eval_stmt cx (Raise rk) = raise (AssertException msg)` by
    (qpat_x_assum `rk = RaiseBare \/ rk = RaiseUnreachable` (DISJ_CASES_THEN SUBST_ALL_TAC) >>
     simp[Abbr `msg`, FUN_EQ_THM, Once evaluate_def, raise_def]) >>
  `?a t. step_inst_base (mk_inst sa.cs_next_id opc ops []) s0 = Abort a t /\
         expr_exit (INR (AssertException msg) : unit + exception) (Abort a t)` by
    (qpat_x_assum `rk = RaiseBare \/ rk = RaiseUnreachable` (DISJ_CASES_THEN SUBST_ALL_TAC) >>
     gvs[Abbr `opc`, Abbr `ops`, Abbr `msg`, expr_exit_def]
     >- simp[step_revert_zero] >>
     qexists_tac `ExHalt_abort` >> simp[step_invalid]) >>
  irule gas_outcome_mods_unchanged >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`G0`, `Abort a t`, `INR (AssertException msg)`, `tn0`] >>
  simp[raise_def, exit_result_def, stmt_exit_ptr_def, halt_exit_def] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` drule >> strip_tac >>
  `allocas_from lo s0` by fs[ghost_inv_at_mods_def] >>
  irule emit_abort_origin_ptr >> simp[] >>
  qexistsl_tac [`opc`, `ops`, `sa`, `sb`] >> simp[] >>
  qpat_x_assum `rk = RaiseBare \/ rk = RaiseUnreachable` (DISJ_CASES_THEN SUBST_ALL_TAC) >>
  gvs[Abbr `opc`, Abbr `ops`]
QED

Theorem body_break_case_full_mods:
  !mods exps cx. body_stmt_full_ok_mods mods exps cx Break
Proof
  rw[body_stmt_full_ok_mods_def, gas_shadow_stmt_def] >>
  irule loop_jump_frag_full_mods >> simp[]
QED

Theorem body_continue_case_full_mods:
  !mods exps cx. body_stmt_full_ok_mods mods exps cx Continue
Proof
  rw[body_stmt_full_ok_mods_def, gas_shadow_stmt_def] >>
  irule loop_jump_frag_full_mods >> simp[]
QED

Theorem body_raise_bare_case_full_mods:
  !mods exps cx. body_stmt_full_ok_mods mods exps cx (Raise RaiseBare)
Proof
  rw[body_stmt_full_ok_mods_def, gas_shadow_stmt_def, gas_shadow_raise_reason_def] >>
  irule raise_frag_full_mods >> simp[]
QED

Theorem body_raise_unreachable_case_full_mods:
  !mods exps cx. body_stmt_full_ok_mods mods exps cx (Raise RaiseUnreachable)
Proof
  rw[body_stmt_full_ok_mods_def, gas_shadow_stmt_def, gas_shadow_raise_reason_def] >>
  irule raise_frag_full_mods >> simp[]
QED
