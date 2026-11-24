(* Bind the forced Boolean condition to the selected linked arm. *)
Theory bodyIfCountedFragmentMods
Ancestors
  bodyIfPairedIntervalsMods bodyIfConditionOutcomeMods bodyIfSelectedOutcomeMods
  bodyFullPostsMods gasOutcomeFullBindMods gasExemptCertMods stmtSimIfProps
  vyperStorageTrace vyperStorageFootprint vyperState

Theorem compile_if_stmt_frag_full_mods:
  expr_type e = BaseT BoolT /\
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (BaseT BoolT) e es /\
  (MEM func ctx.ctx_functions ==>
    !bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!gs b mid. bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
       (INL (BoolV b),mid) ==>
    stmt_frag_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cx lctx RetQ cenv (stmts_env cenv lctx ty (if b then yes else no))
      (stmts_env (gas_shadow_env T cenv) lctx ty
        (MAP gas_shadow_stmt (if b then yes else no)))
      (eval_stmts cx (if b then yes else no)) (mid with scopes := FEMPTY :: mid.scopes)) ==>
  stmt_frag_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx lctx RetQ cenv (stmt_env cenv lctx ty (If e yes no))
    (stmt_env (gas_shadow_env T cenv) lctx ty (gas_shadow_stmt (If e yes no)))
    (eval_stmt cx (If e yes no)) es
Proof
  strip_tac >> rewrite_tac[stmt_frag_full_mods_def] >> rpt gen_tac >> strip_tac >>
  drule_all if_paired_intervals_mods >> strip_tac >>
  qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by fs[] >>
  drule_all if_condition_outcome_mods >>
  disch_then (qspec_then `RetQ` assume_tac) >>
  asm_rewrite_tac[eval_stmt_if_forced] >>
  irule gas_outcome_full_mods_bind_all >>
  rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (BETA_TAC >> rpt strip_tac >> irule gas_exempt_cert_mods_bind_value >>
      qexistsl_tac [`mid`, `t`, `v`] >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- (irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_read_result])
  >~ [`storage_trace_frame _`]
  >- (rw[storage_trace_frame_raise] >>
      irule storage_trace_frame_ignore_bind >>
      simp[storage_trace_frame_state_updates] >>
      irule storage_trace_frame_finally >>
      simp[storage_trace_frame_pop_scope, evaluate_storage_trace_frame]) >>
  qmatch_assum_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ condQ condR` >>
  qexists_tac `condQ` >> conj_tac
  >~ [`storage_trace_domain _ _ _`]
  >- suspend "selected" >>
  qunabbrev_tac `condR` >> BETA_TAC >> first_assum ACCEPT_TAC
QED

Resume compile_if_stmt_frag_full_mods[selected]:
  qx_genl_tac [`marks`, `res`, `mid`, `G1`, `tn1`, `t`] >> strip_tac >>
  qunabbrev_tac `condQ` >> RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
  disj1_tac >> qexists_tac `BoolV b` >>
  simp_tac bool_ss [BETA_THM] >>
  `bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL (BoolV b),mid)` by
    (`mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
     qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     pop_assum (fn th => pure_rewrite_tac[listTheory.APPEND_NIL, th]) >> simp[]) >>
  qpat_x_assum `!gs b mid. _` drule >> strip_tac >>
  qpat_x_assum `!b. ?entry last after sentry slast cenvb. _`
    (qspec_then `b` strip_assume_tac) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
       (qspec_then `H` mp_tac) >> simp[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post_mods H ctx func cenv cx e es sa cond s0 mid (BoolV b) op t /\
    t.vs_current_bb = cond.cs_current_bb /\ t.vs_inst_idx = LENGTH cond.cs_current_insts /\
    alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at_mods (DF H) lo d cenv cx mid G1 tn1 t /\
    ptr_val_ok cx (post_value_type cenv e) (BoolV b) op G1 tn1 t /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> fs[]) >>
  `MAP gas_shadow_stmt (if b then yes else no) =
    (if b then MAP gas_shadow_stmt yes else MAP gas_shadow_stmt no)` by
    (Cases_on `b` >> simp[]) >>
  `~block_is_terminated last ==>
     emit_inst JMP [Label xl] [] last = ((),after) /\ fn_has_code last after func /\
     sb.cs_current_bb = xl /\ sb.cs_current_insts = []` by (strip_tac >> fs[]) >>
  `(if BoolV b = BoolV T then ignore_bind push_scope (finally (eval_stmts cx yes) pop_scope)
     else if BoolV b = BoolV F then ignore_bind push_scope (finally (eval_stmts cx no) pop_scope)
     else raise (Error (TypeError "not BoolV"))) =
   ignore_bind push_scope (finally (eval_stmts cx (if b then yes else no)) pop_scope)` by
    (Cases_on `b` >> simp[]) >>
  pop_assum (fn th => pure_rewrite_tac[th]) >>
  irule if_selected_outcome_mods >>
  rpt (conj_tac >- (first_assum ACCEPT_TAC ORELSE (disch_tac >> first_assum ACCEPT_TAC))) >>
  goal_assum (drule_at (Pat `emit_inst JNZ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `stmts_env cenv _ _ _ _ = _`)) >>
  qexistsl_tac [`after`, `cond`, `e`, `gas_explicit marks s0.vs_gas_readings`] >>
  qpat_assum `MAP _ _ = _` (fn th => pure_rewrite_tac [GSYM th]) >>
  goal_assum (drule_at (Pat `stmts_env (gas_shadow_env T cenv) _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `gas_shadow_function _ _`)) >>
  qexists_tac `xl` >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise compile_if_stmt_frag_full_mods
