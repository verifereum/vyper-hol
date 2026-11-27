(* Request-prefix companion to bodyFullStmtsCons. *)
Theory s1PrefixStmtsCons
Ancestors
  s1PrefixPreds bodyFullStmtsCons s1PrefixDefs s1PrefixCompose
  bodySimFull gasOutcomeFullCompose bodyFullIfExpReach
  gasShadowStmtEnv gasShadowCompileStmtBase bodyFullShared
  stmtFragPtr stmtSimSeqEnv stmtSimProps loweringPosts bodyPtrDefs bodyExprPreFacts
  stmtLoweringMono fragExec exprSimDefs compileEnv stmtLowering
  vyperState vyperStorageFootprint contextRawReachable ptrDiscipline

Theorem stmt_frag_prefix_cons_env:
  !DF lo d ctx shadow_ctx PG func shadow_func cx lctx RetQ cenv ty
   stmt ss es.
  (ctx_has_dalloca ctx /\ MEM func ctx.ctx_functions ==>
      !bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ty stmt)
      (stmt_env (gas_shadow_env T cenv) lctx ty (gas_shadow_stmt stmt))
      (eval_stmt cx stmt) es /\
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ty stmt)
      (stmt_env (gas_shadow_env T cenv) lctx ty (gas_shadow_stmt stmt))
      (eval_stmt cx stmt) es /\
  (!gs es1 c sa sm.
       eval_stmt cx stmt (es with gas_obs := gs) = (INL (), es1) /\
       stmt_env cenv lctx ty stmt sa = (c, sm) /\
       cenv_top_ext cenv c es1.scopes ==>
       stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
         cx lctx RetQ c
         (stmts_env c lctx ty ss)
         (stmts_env (gas_shadow_env T c) lctx ty (MAP gas_shadow_stmt ss))
         (eval_stmts cx ss) es1) /\
  (!gs es1 c sa sm.
       eval_stmt cx stmt (es with gas_obs := gs) = (INL (), es1) /\
       stmt_env cenv lctx ty stmt sa = (c, sm) /\
       cenv_top_ext cenv c es1.scopes ==>
       stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
         cx lctx RetQ c
         (stmts_env c lctx ty ss)
         (stmts_env (gas_shadow_env T c) lctx ty (MAP gas_shadow_stmt ss))
         (eval_stmts cx ss) es1) ==>
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmts_env cenv lctx ty (stmt::ss))
      (stmts_env (gas_shadow_env T cenv) lctx ty (MAP gas_shadow_stmt (stmt::ss)))
      (eval_stmts cx (stmt::ss)) es
Proof
  rpt gen_tac >> strip_tac >>
  `gas_shadow_compiles_env T (stmt_env cenv lctx ty stmt)
     (stmt_env (gas_shadow_env T cenv) lctx ty (gas_shadow_stmt stmt))` by
    irule gas_shadow_stmt_env_env >>
  simp[stmt_frag_prefix_def, stmt_frag_full_pre_def] >>
  rpt gen_tac >> strip_tac >>
  `ctx_has_dalloca ctx ==> !bb. MEM bb func.fn_blocks ==>
      phi_prefix_length bb.bb_instructions = 0` by
    (qpat_x_assum `ctx_has_dalloca ctx /\ MEM func ctx.ctx_functions ==> _`
       mp_tac >> simp[]) >>
  qpat_x_assum `stmts_env _ _ _ (stmt::ss) _ = _` mp_tac >>
  simp[stmts_env_cons, comp_bind_def] >> pairarg_tac >> simp[] >>
  strip_tac >> rename1 `stmt_env cenv lctx ty stmt sa = (c, sm)` >>
  `~block_is_terminated shadow_sa` by metis_tac[gas_shadow_terminated] >>
  qpat_x_assum `stmts_env _ _ _ (gas_shadow_stmt stmt::MAP gas_shadow_stmt ss) _ = _` mp_tac >>
  simp[stmts_env_cons, comp_bind_def] >> pairarg_tac >> simp[] >>
  strip_tac >>
  rename1 `stmt_env _ _ _ (gas_shadow_stmt stmt) shadow_sa = (c', shadow_sm)` >>
  `c' = gas_shadow_env T c /\ gas_shadow_state sm shadow_sm` by
    (qpat_x_assum `gas_shadow_compiles_env _ _ _` mp_tac >>
     simp[gas_shadow_compiles_env_def] >>
     disch_then (qspecl_then [`sa`, `shadow_sa`] mp_tac) >> simp[]) >>
  gvs[] >>
  qspecl_then [`cenv`, `lctx`, `ty`, `stmt`, `sa`, `c`, `sm`] mp_tac
    stmt_env_reserved >>
  simp[cj 1 compile_stmt_cs_mono] >> strip_tac >>
  `cs_extends sm sb` by metis_tac[stmts_env_cs_mono, cs_mono_def] >>
  `cs_extends shadow_sa shadow_sm` by
    (`stmts_env (gas_shadow_env T cenv) lctx ty [gas_shadow_stmt stmt] shadow_sa =
        (gas_shadow_env T c, shadow_sm)` by
       simp[stmts_env_cons, comp_bind_def, stmts_env_def, comp_return_def] >>
     metis_tac[stmts_env_cs_mono, cs_mono_def]) >>
  `cs_extends shadow_sm shadow_sb` by
    metis_tac[stmts_env_cs_mono, cs_mono_def] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_split] >>
  `fn_has_code shadow_sa shadow_sm shadow_func /\
   fn_has_code shadow_sm shadow_sb shadow_func` by
    metis_tac[fn_has_code_split] >>
  `gas_admissible (eval_stmt cx stmt) (stmt_res_ok lctx) es` by
    (irule gas_admissible_stmts_head >> qexists_tac `ss` >> simp[]) >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (eval_stmt cx stmt) (es,s0,G0,tn0)` by
    (qpat_x_assum `stmt_frag_prefix _ _ _ _ _ (stmt_env _ _ _ _) _ _ _` mp_tac >>
     simp[stmt_frag_prefix_def, stmt_frag_full_pre_def] >>
     disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,
                             `s0`,`G0`,`tn0`,`c`] mp_tac) >>
     simp[] >> (impl_tac >- first_assum ACCEPT_TAC) >> simp[]) >>
  qpat_x_assum `stmt_frag_full _ _ _ _ _ (stmt_env _ _ _ _) _ _ _` mp_tac >>
  simp[stmt_frag_full_def] >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,
                          `s0`,`G0`,`tn0`,`c`] mp_tac) >>
  simp[] >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  suspend "compose"
QED

Resume stmt_frag_prefix_cons_env[compose]:
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ headQ headR` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (eval_stmt cx stmt) (es,s0,G0,tn0)
     (\H res ee G tn t. headQ H res ee G tn t /\
       ?cm. gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (s0,G0,tn0) cm (OK t,G,tn)) headR` by
    (irule gas_outcome_full_post_path >>
     qpat_assum `gas_outcome_full _ _ _ _ _ _ headQ headR` (irule_at Any) >>
     rpt strip_tac >> simp[] >> goal_assum (drule_at Any)) >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ pathQ headR` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (eval_stmt cx stmt) (es,s0,G0,tn0)
     (\H res ee G tn t. pathQ H res ee G tn t /\ ee.gas_obs = []) headR` by
    (irule gas_outcome_full_post_source >>
     qpat_assum `gas_outcome_full _ _ _ _ _ _ pathQ headR` (irule_at Any) >> simp[]) >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ midQ headR` >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ midQ headR`
    (mp_then Any irule gas_prefix_full_stmts_cons) >>
  simp[] >> reverse conj_tac
  >- (simp[Abbr `headR`, stmt_exit_ptr_def, expr_exit_def] >>
      rpt gen_tac >> Cases_on `res` >> simp[expr_exit_def]) >>
  suspend "tail"
QED

Resume stmt_frag_prefix_cons_env[tail]:
  rpt gen_tac >> strip_tac >>
  qunabbrev_tac `midQ` >> qunabbrev_tac `pathQ` >> qunabbrev_tac `headQ` >>
  RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> gvs[stmt_lands_def] >>
  `!fn inst s. frag_reachable ctx func t fn inst s ==> dalloca_fmp_headroom inst s` by
    (Cases_on `ctx_has_dalloca ctx`
     >- (`!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by fs[] >>
         qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) _ (OK t,G1,tn1)`
           (mp_then Any mp_tac gas_origin_ptr_path_dalloca_fmp_headroom) >>
         simp[] >> disch_then (fn reach =>
           qx_genl_tac [`f`,`i`,`u`] >> disch_tac >>
           qspecl_then [`f`,`i`,`u`] mp_tac reach) >>
         (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
     rpt strip_tac >> drule_all frag_reachable_members >> strip_tac >>
     simp[unitTransformDefsTheory.dalloca_fmp_headroom_def] >> strip_tac >>
     `ctx_has_dalloca ctx` by
       (simp_tac bool_ss [ctx_has_dalloca_def, listTheory.EXISTS_MEM] >>
        qexists_tac `fn` >> conj_tac >- first_assum ACCEPT_TAC >>
        qexists_tac `inst` >> simp[]) >> fs[]) >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  `eval_stmt cx stmt
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL (), mid)` by
    (qpat_assum `!tail. eval_stmt _ _ _ = _` (qspec_then `[]` mp_tac) >>
     qpat_assum `mid with gas_obs := [] = mid`
       (fn th => rewrite_tac[listTheory.APPEND_NIL, th])) >>
  `gas_admissible (eval_stmts cx ss) (stmt_res_ok lctx) mid` by
    (qpat_assum `mid with gas_obs := [] = mid` (SUBST1_TAC o SYM) >>
     irule gas_admissible_stmts_tail >> metis_tac[]) >>
  `c.ce_return_pc = cenv.ce_return_pc /\
   c.ce_return_buf = cenv.ce_return_buf /\
   (c.ce_is_ctor <=> cenv.ce_is_ctor)` by
    metis_tac[cenv_top_ext_return_pc, cenv_top_ext_return_buf,
              cenv_top_ext_is_ctor] >>
  `c.ce_modules = cenv.ce_modules` by
    (qpat_assum `cenv_top_ext cenv c _` mp_tac >>
     simp[cenv_top_ext_def] >> strip_tac >>
     qpat_x_assum `_ = cenv` (SUBST1_TAC o SYM) >> simp[]) >>
  `!H. dead_lo_ok H (DF H) lo c cx` by fs[dead_lo_ok_def] >>
  `ret_pc_ok c sm t` by (irule ret_pc_ok_frame >> metis_tac[]) >>
  `!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule stmtFragPtrTheory.not_fresh_at_mono >> qexists_tac `sa` >>
     metis_tac[]) >>
  qpat_x_assum `!gs es1 c sa sm. _ ==> stmt_frag_prefix _ _ _ _ _ _ _ _ _`
    (qspecl_then [`gas_explicit marks s0.vs_gas_readings`, `mid`, `c`, `sa`, `sm`] mp_tac) >>
  (impl_tac >- simp[]) >>
  simp[stmt_frag_prefix_def, stmt_frag_full_pre_def] >>
  disch_then (qspecl_then [`st0`, `sm`, `sb`, `shadow_sm`, `shadow_sb`, `t`, `G1`,
                           `tn1`, `cenv'`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]
QED

Finalise stmt_frag_prefix_cons_env
