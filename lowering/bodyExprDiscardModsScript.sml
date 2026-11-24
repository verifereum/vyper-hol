(* Expression statements discard the operand, not its linked execution frame. *)
Theory bodyExprDiscardMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods bodyFullShared bodyExprPreFacts bodySimFull
  bodyInvCodeProps bodyInvMetadataProps bodySim stmtSimExpr stmtSimDefs stmtSimProps
  supportedStmts supportedStmtTraverse supportedExprTraverse allocLimits allocLimitsProps
  vyperTypeSystem vyperTypeCallGraph vyperStorageTrace vyperStorageFootprint
  gasShadow gasShadowCompileStmtHelpers gasShadowState gasExemptCertMods
  gasOutcomeFullMods gasOutcomeFull gasStorage gasSummary gasContext
  fragGasOriginPtr fragGasOrigin fragGasMode fragGasPath fragExec
  assignPlaceEndpoint exprSimUnwrap exprLoweringProps bodyPtrDefs bodyMemoryDefs
  loweringPosts loweringStateRelDefs stmtLowering compileEnv exprSimDefs
  vyperInterpreter vyperState

Theorem expr_discard_initial_domain[local]:
  storage_trace_frame source /\ ~s.vs_halted /\
  (storage_trace_domain cx st0 es.storage_trace ==>
   gas_outcome_full_mods (DF, lo, explicit, ctx, func, PG) mods cx st0 source
     (es, s, G, tn) Q R) ==>
  gas_outcome_full_mods (DF, lo, explicit, ctx, func, PG) mods cx st0 source
    (es, s, G, tn) Q R
Proof
  strip_tac >> Cases_on `storage_trace_domain cx st0 es.storage_trace` >- simp[] >>
  rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `[]` >> disj1_tac >> conj_tac
  >- (simp[gas_bad_storage_at_def, gas_explicit_def] >> gen_tac >>
      Cases_on `source (es with gas_obs := tail)` >> simp[] >>
      irule storage_trace_frame_preserves_bad_domain >>
      qexistsl_tac [`source`, `q`, `es with gas_obs := tail`] >> simp[]) >>
  qexistsl_tac [`ARB`, `func`, `PG`, `G`, `tn`, `s`] >>
  simp[gas_origin_ptr_focus_nil]
QED

Theorem expr_discard_exempt[local]:
  gas_exempt_cert_mods memory mods (ctx,func)
    (ignore_bind (eval_expr cx e) (return ())) (es,s0)
    marks (err,ee) (leaf,fin) ==>
  gas_exempt_cert_mods memory mods (ctx,func)
    (ignore_bind (eval_stmt cx (Expr e)) (return ())) (es,s0)
    marks (err,ee) (leaf,fin)
Proof
  strip_tac >>
  `ignore_bind (eval_stmt cx (Expr e)) (return ()) =
   bind (eval_expr cx e)
     (\tv. ignore_bind (type_check (~is_HashMapRef tv) "Expr HashMapRef")
                       (return ()))` by
    (simp[Once evaluate_def, ignore_bind_def, FUN_EQ_THM, bind_def] >>
     gen_tac >> Cases_on `eval_expr cx e x` >> Cases_on `q` >> simp[]) >>
  pop_assum SUBST1_TAC >>
  irule gas_exempt_cert_mods_error_result >> simp[]
QED

Theorem expr_discard_eval[local]:
  gas_admissible (eval_stmt cx (Expr e)) (stmt_res_ok lctx) es /\
  eval_expr cx e (es with gas_obs := gs) = (res, ee) ==>
  eval_stmt cx (Expr e) (es with gas_obs := gs) =
    ((case res of INL tv => INL () | INR ex => INR ex), ee)
Proof
  strip_tac >> Cases_on `res`
  >- (drule_all expr_stmt_not_hashmap >> simp[eval_expr_stmt_success]) >>
  simp[eval_expr_stmt_exception]
QED

Theorem expr_discard_outcome[local]:
  gas_outcome_full_mods (DF, lo, explicit, ctx, func, PG) mods cx st0
    (eval_expr cx e) (es,s,G,tn) Q R ==>
  gas_admissible (eval_stmt cx (Expr e)) (stmt_res_ok lctx) es /\
  (!H marks res ee G' tn' t.
    gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
      (s,G,tn) marks (OK t,G',tn') /\ Q H res ee G' tn' t ==>
    Q' H (case res of INL tv => INL () | INR ex => INR ex) ee G' tn' t) /\
  (!H res ee gt r. R H res ee gt r ==>
    R' H (case res of INL tv => INL () | INR ex => INR ex) ee gt r) ==>
  gas_outcome_full_mods (DF, lo, explicit, ctx, func, PG) mods cx st0
    (eval_stmt cx (Expr e)) (es,s,G,tn) Q' R'
Proof
  disch_then (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_mods_def]) >>
  strip_tac >> rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks`
  >~ [`gas_bad_storage_at _ _ _ _ _ _`]
  >- (disj1_tac >> conj_tac >- (
        `eval_stmt cx (Expr e) = bind (eval_expr cx e)
           (\tv. type_check (~is_HashMapRef tv) "Expr HashMapRef")` by
           simp[Once evaluate_def] >>
        pop_assum SUBST1_TAC >> irule gas_bad_storage_at_bind_left >>
        simp[storage_trace_frame_checks]) >>
      metis_tac[])
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`case res of INL tv => INL () | INR ex => INR ex`,
                    `ee`, `r`, `G'`, `tn'`] >>
      conj_tac >- (gen_tac >> irule expr_discard_eval >> simp[] >> metis_tac[]) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      gen_tac >> disch_tac >> first_x_assum drule >> strip_tac >> simp[] >>
      first_x_assum strip_assume_tac >> gvs[] >> metis_tac[]) >>
  disj2_tac >> disj2_tac >>
  drule_then assume_tac expr_discard_exempt >> metis_tac[]
QED

Theorem compile_expr_discard_frag_mods[local]:
  !DF lo d ctx shadow_ctx PG func shadow_func cx lctx RetQ cenv ty e es.
    expr_vv_sim_full_mods (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx (expr_type e) e es ==>
    stmt_frag_full_mods (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Expr e))
      (stmt_env (gas_shadow_env T cenv) lctx ty (gas_shadow_stmt (Expr e)))
      (eval_stmt cx (Expr e)) es
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[stmt_frag_full_mods_def] >>
  rpt gen_tac >> strip_tac >>
  irule expr_discard_initial_domain >>
  simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ (Expr e) _ = _` mp_tac >>
  qpat_x_assum `stmt_env _ _ _ (gas_shadow_stmt (Expr e)) _ = _` mp_tac >>
  simp[gas_shadow_stmt_def, stmt_env_def, declare_stmt_local_def, compile_stmt_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  Cases_on `compile_expr cenv (expr_type e) e sa` >>
  Cases_on `compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) shadow_sa` >>
  simp[] >> rpt strip_tac >> gvs[] >>
  rename1 `compile_expr _ _ e sa = (vv, sm)` >>
  rename1 `compile_expr _ _ (gas_shadow_expr _) shadow_sa = (svv, shadow_sm)` >>
  `svv = vv` by
    (qspec_then `sa` (qspec_then `shadow_sa` mp_tac)
       (REWRITE_RULE [gas_shadow_compiles_def]
          (Q.INST [`ty` |-> `expr_type e`, `sd` |-> `T`]
             gas_shadow_stmt_compile_expr_env)) >> simp[]) >>
  pop_assum SUBST_ALL_TAC >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    (drule_then ACCEPT_TAC expr_stmt_admissible) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x`
    by fs[ret_pc_ok_def] >>
  qpat_x_assum `expr_vv_sim_full_mods _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_full_mods_def]) >>
  disch_then (qspecl_then [`st0`, `sa`, `sm`, `shadow_sa`, `shadow_sm`, `vv`,
                           `s0`, `G0`, `tn0`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (irule o MATCH_MP expr_discard_outcome) >>
  conj_tac >- suspend "normal" >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >> Cases_on `res` >> fs[expr_exit_def] >>
    rename1 `expr_exit (INR exc) r` >> simp[stmt_exit_ptr_def] >>
    Cases_on `r` >> Cases_on `exc` >> gvs[expr_exit_def, halt_exit_def] >>
    rename1 `Error err` >> Cases_on `err` >> gvs[expr_exit_def]) >>
  metis_tac[]
QED

Resume compile_expr_discard_frag_mods[normal]:
  simp[] >> rpt gen_tac >> strip_tac >> gvs[] >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var` by
    (qpat_assum `compile_expr _ _ e sa = _`
       (mp_tac o MATCH_MP compile_expr_extends) >> simp[]) >>
  drule_then (assume_tac o cj 1) gas_origin_ptr_path_projections >>
  drule_then assume_tac gas_origin_path_erase >>
  drule_then assume_tac gas_marked_path_exec >>
  drule_then (assume_tac o cj 1) gas_path_normal >>
  `~block_is_terminated sm` by
    (irule endpoint_path_open >>
     qexistsl_tac [`ctx`, `func`, `LENGTH marks`, `s0`, `sa`, `t`] >>
     simp[gas_marked_path_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace`
    by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  qhdtm_x_assum `vv_post_mods`
    (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  `MAP FDOM ee.scopes = MAP FDOM es.scopes` by fs[locals_kept_def] >>
  `!bw capacity. d = SOME (bw, capacity) ==> allocas_from (w2n bw + capacity) s0` by
    (rpt strip_tac >> fs[return_buf_sep_def]) >>
  `!bw capacity. d = SOME (bw, capacity) ==> allocas_from (w2n bw + capacity) t` by
    (drule return_buf_allocas_suffix >>
     disch_then (qspecl_then [`sa`, `d`, `cenv`] mp_tac) >> simp[]) >>
  `return_buf_frame d cenv sm t` by
    (drule return_buf_frame_frame >> simp[]) >>
  `return_buf_sep d cenv ee t` by
    (irule (INST_TYPE [alpha |-> ``:256``] return_buf_sep_locals_kept) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`storage_trace_horizon es.storage_trace`, `ctx`, `cx`, `es`,
                   `func`, `s0`, `sa`] >> simp[]) >>
  `alloca_frame cenv es sa s0 cenv ee t` by
    (irule (INST_TYPE [alpha |-> ``:256``] alloca_frame_of_mem_frame) >> simp[] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`storage_trace_horizon es.storage_trace`, `ctx`, `cx`, `func`] >> simp[]) >>
  fs[stmt_lands_def, cenv_top_ext_refl, ghost_kept_at_def] >>
  first_assum ACCEPT_TAC
QED

Finalise compile_expr_discard_frag_mods

Theorem expr_stmt_full_ok_mods:
  !mods exps cx e.
    (!ctx cenv src tops env es bindings s ret_ty env'.
       contract_inv mods exps ctx cenv cx /\
       module_body_inv mods src tops cenv cx /\
       expr_sim_inv_mods mods cenv cx env es /\
       body_const_cells_agree_mods mods cx env es /\
       supported_stmt tops bindings s /\ type_stmt env ret_ty s = SOME env' ==>
       EVERY (source_body_call_supported cx) (int_calls_stmt s)) ==>
    body_expr_full_ok_mods mods exps cx e ==>
    body_stmt_full_ok_mods mods exps cx (Expr e)
Proof
  rpt gen_tac >> disch_then (mk_asm "resolve") >> disch_tac >>
  rw[body_stmt_full_ok_mods_def] >>
  `EVERY (source_body_call_supported cx) (int_calls_stmt (Expr e))` by
    (asm "resolve" irule >> metis_tac[]) >>
  `supported_expr tops e` by fs[Once supported_stmt_def] >>
  drule_then assume_tac supported_expr_no_evm_run >>
  drule_then assume_tac contract_inv_cenv_modules >>
  drule_then assume_tac contract_inv_type_env >>
  `expr_body_pre_mods mods cenv cx env e es` by
    (irule (Q.INST [`calls` |-> `[]`] (SPEC_ALL stmt_expr_body_pre_mods)) >>
     fs[stmt_exprs_ok_flat, supported_stmt_expr_exists_def, type_stmt_def,
        int_calls_stmt_def, alloc_limits_stmt_def] >>
     metis_tac[alloc_limits_expr_not_extcode]) >>
  irule compile_expr_discard_frag_mods >>
  qpat_x_assum `body_expr_full_ok_mods _ _ _ _`
    (strip_assume_tac o SIMP_RULE bool_ss [IMP_CONJ_THM, FORALL_AND_THM] o
     ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
  first_assum irule >> metis_tac[]
QED
