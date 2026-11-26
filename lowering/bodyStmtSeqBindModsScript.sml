(* Sequence composition at the actual normal endpoint of the head. *)
Theory bodyStmtSeqBindMods
Ancestors
  bodyFullPostsMods bodyFullShadowBodyInv bodySimFull bodyFullIfExpReach
  gasOutcomeFullMods gasOutcomeFullBindMods gasOutcomeFullPostMods
  gasExemptCertMods fragGasOriginPtr gasShadowState gasShadowCompileBase
  gasShadowStmtEnv gasShadowCompileStmtBase bodyFullShared
  stmtFragPtr stmtSimSeqEnv stmtSimProps stmtSimDefs loweringPosts
  bodyMemoryDefs bodyPtrDefs bodyExprPreFacts stmtLoweringMono fragExec exprSimDefs
  bodySim compileEnv stmtLowering vyperInterpreter vyperState
  vyperStorageTrace vyperEvalPreservesScopes vyperStorageFootprint
  contextRawReachable unitMemInv ptrDiscipline list

Theorem linked_post_path[local]:
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source
    (es,s,G,tn) Q R /\
  (!marks H res ee G' tn' t.
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
      (s,G,tn) marks (OK t,G',tn') /\ Q H res ee G' tn' t ==>
    Q' H res ee G' tn' t) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source
    (es,s,G,tn) Q' R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_mods_def]) >>
  rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks`
  >- (disj1_tac >> metis_tac[])
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >>
      rpt conj_tac >- simp[] >- simp[] >>
      rpt strip_tac >> first_x_assum drule >> strip_tac >> gvs[]
      >- (disj1_tac >> first_x_assum irule >> simp[] >>
          qexists_tac `marks` >> simp[]) >>
      disj2_tac >> simp[]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

Theorem stmt_frag_cons_bind_mods:
  !DF lo d ctx shadow_ctx PG func shadow_func cx lctx RetQ cenv ty
   stmt ss es.
    (ctx_has_dalloca ctx /\ MEM func ctx.ctx_functions ==>
      !bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
    stmt_frag_full_mods (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ty stmt)
      (stmt_env (gas_shadow_env T cenv) lctx ty (gas_shadow_stmt stmt))
      (eval_stmt cx stmt) es /\
    (!gs es1 c sa sm.
       eval_stmt cx stmt (es with gas_obs := gs) = (INL (), es1) /\
       stmt_env cenv lctx ty stmt sa = (c, sm) /\
       cenv_top_ext cenv c es1.scopes ==>
       stmt_frag_full_mods (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
         cx lctx RetQ c
         (stmts_env c lctx ty ss)
         (stmts_env (gas_shadow_env T c) lctx ty (MAP gas_shadow_stmt ss))
         (eval_stmts cx ss) es1) ==>
    stmt_frag_full_mods (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmts_env cenv lctx ty (stmt::ss))
      (stmts_env (gas_shadow_env T cenv) lctx ty (MAP gas_shadow_stmt (stmt::ss)))
      (eval_stmts cx (stmt::ss)) es
Proof
  rpt gen_tac >> strip_tac >>
  `gas_shadow_compiles_env T (stmt_env cenv lctx ty stmt)
     (stmt_env (gas_shadow_env T cenv) lctx ty (gas_shadow_stmt stmt))` by
    irule gas_shadow_stmt_env_env >>
  simp[stmt_frag_full_mods_def] >> rpt gen_tac >> strip_tac >>
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
  rename1 `stmt_env _ _ _ (gas_shadow_stmt _) shadow_sa = (c', shadow_sm)` >>
  `c' = gas_shadow_env T c /\ gas_shadow_state sm shadow_sm` by
    (qpat_x_assum `gas_shadow_compiles_env _ _ _` mp_tac >>
     simp[gas_shadow_compiles_env_def] >>
     disch_then (qspecl_then [`sa`, `shadow_sa`] mp_tac) >> simp[]) >>
  gvs[] >> suspend "head"
QED

Resume stmt_frag_cons_bind_mods[head]:
  qspecl_then [`cenv`, `lctx`, `ty`, `stmt`, `sa`, `c`, `sm`] mp_tac
    stmt_env_reserved >>
  simp[cj 1 compile_stmt_cs_mono] >> strip_tac >>
  `cs_extends sm sb /\ sm.cs_next_var <= sb.cs_next_var` by
    (qspecl_then [`c`, `lctx`, `ty`, `ss`] mp_tac stmts_env_cs_mono >>
     simp[cs_mono_def] >> metis_tac[]) >>
  `cs_extends shadow_sa shadow_sm` by
    (`stmts_env (gas_shadow_env T cenv) lctx ty [gas_shadow_stmt stmt] shadow_sa =
        (gas_shadow_env T c, shadow_sm)` by
       simp[stmts_env_cons, comp_bind_def, stmts_env_def, comp_return_def] >>
     qspecl_then [`gas_shadow_env T cenv`, `lctx`, `ty`, `[gas_shadow_stmt stmt]`] mp_tac
       stmts_env_cs_mono >>
     simp[cs_mono_def] >> metis_tac[]) >>
  `cs_extends shadow_sm shadow_sb` by
    (qspecl_then [`gas_shadow_env T c`, `lctx`, `ty`, `MAP gas_shadow_stmt ss`] mp_tac
       stmts_env_cs_mono >>
     simp[cs_mono_def] >> metis_tac[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_split] >>
  `fn_has_code shadow_sa shadow_sm shadow_func /\
   fn_has_code shadow_sm shadow_sb shadow_func` by
    metis_tac[fn_has_code_split] >>
  `gas_admissible (eval_stmt cx stmt) (stmt_res_ok lctx) es` by
    (irule gas_admissible_stmts_head >> qexists_tac `ss` >> simp[]) >>
  qpat_x_assum `stmt_frag_full_mods _ _ _ _ _ (stmt_env _ _ _ _) _ _ _` mp_tac >>
  simp[stmt_frag_full_mods_def] >>
  disch_then (qspecl_then [`st0`, `sa`, `sm`, `shadow_sa`, `shadow_sm`, `s0`,
                           `G0`, `tn0`, `c`] mp_tac) >>
  simp[] >> (impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >>
    rpt strip_tac >> first_x_assum drule >> simp[])) >> strip_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ headQ headR` >>
  `gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cenv.ce_modules cx st0 (eval_stmt cx stmt) (es,s0,G0,tn0)
     (\H res ee G tn t. headQ H res ee G tn t /\
       ?cm. gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (s0,G0,tn0) cm (OK t,G,tn)) headR` by
    (irule linked_post_path >>
     qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ headQ headR` (irule_at Any) >>
     rpt strip_tac >> simp[] >> goal_assum (drule_at Any)) >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ _ _ headQ headR` kall_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ pathQ headR` >>
  suspend "bind"
QED

Resume stmt_frag_cons_bind_mods[bind]:
  simp[Once evaluate_def, ignore_bind_def] >>
  irule gas_outcome_full_mods_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_unit >> simp[] >>
      qexistsl_tac [`mid`, `t`] >> Cases_on `v` >> fs[])
  >~ [`gas_exempt_cert_mods _ _ _ (ignore_bind (eval_stmt _ _) _)`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_unit >> simp[])
  >~ [`storage_trace_frame (eval_stmt _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >~ [`storage_trace_frame _`]
  >- simp[evaluate_storage_trace_frame] >>
  qexists_tac `\H res ee G tn t. pathQ H res ee G tn t /\
                    ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac >- suspend "continue" >>
  irule gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` (irule_at Any) >>
  conj_tac >- simp[] >>
  simp[Abbr `headR`] >> rpt strip_tac >>
  Cases_on `res` >> simp[halt_exit_def] >>
  qpat_x_assum `!tail. stmt_exit_ptr _ (_ with gas_obs := tail) _ _ _`
    (qspec_then `[]` mp_tac) >>
  simp[stmt_exit_ptr_def, expr_exit_def] >> fs[halt_exit_def] >>
  metis_tac[]
QED

Resume stmt_frag_cons_bind_mods[continue]:
  qx_genl_tac [`marks`, `res`, `mid`, `G1`, `tn1`, `t`] >>
  BETA_TAC >> strip_tac >>
  qunabbrev_tac `pathQ` >> qunabbrev_tac `headQ` >> RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  Cases_on `res`
  >- (rename1 `INL u` >> Cases_on `u` >> gvs[] >>
      suspend "tail") >>
  rename1 `INR exc` >> disj2_tac >> qexists_tac `exc` >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `H` mp_tac) >> simp[] >>
  disch_then (CONJUNCTS_THEN2 (qx_choose_then `cfin` strip_assume_tac) (K all_tac)) >>
  qexists_tac `cfin` >> fs[stmt_lands_def] >>
  `return_buf_frame d cfin sb t` by
    (irule return_buf_frame_frame >>
     qexistsl_tac [`cfin`, `t`, `sm`] >> simp[]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume stmt_frag_cons_bind_mods[tail]:
  `!fn inst s. frag_reachable ctx func t fn inst s ==> dalloca_fmp_headroom inst s` by
    (Cases_on `ctx_has_dalloca ctx`
     >- (`!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by fs[] >>
         match_mp_tac (GEN_ALL gas_origin_ptr_path_dalloca_fmp_headroom) >>
         qpat_assum `gas_origin_ptr_path _ _ _ (OK t,G1,tn1)` (irule_at Any) >>
         conj_tac >> first_assum ACCEPT_TAC) >>
     rpt strip_tac >> drule_all frag_reachable_members >> strip_tac >>
     simp[unitTransformDefsTheory.dalloca_fmp_headroom_def] >> strip_tac >>
     `ctx_has_dalloca ctx` by
       (simp_tac bool_ss [ctx_has_dalloca_def, EXISTS_MEM] >>
        qexists_tac `fn` >> conj_tac >- first_assum ACCEPT_TAC >>
        qexists_tac `inst` >> simp[]) >> fs[]) >>
  `mid with gas_obs := [] = mid` by
    gvs[evaluation_state_component_equality] >>
  `eval_stmt cx stmt
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL (), mid)` by
    (qpat_assum `!tail. eval_stmt _ _ _ = _` (qspec_then `[]` mp_tac) >>
     qpat_assum `mid with gas_obs := [] = mid`
       (fn th => rewrite_tac[APPEND_NIL, th])) >>
  `gas_admissible (eval_stmts cx ss) (stmt_res_ok lctx) mid` by
    (qpat_assum `mid with gas_obs := [] = mid` (SUBST1_TAC o SYM) >>
     irule gas_admissible_stmts_tail >> metis_tac[]) >>
  `c.ce_return_pc = cenv.ce_return_pc /\
   c.ce_return_buf = cenv.ce_return_buf /\
   (c.ce_is_ctor <=> cenv.ce_is_ctor)` by
    metis_tac[cenv_top_ext_return_pc, cenv_top_ext_return_buf,
              cenv_top_ext_is_ctor] >>
  `c.ce_modules = cenv.ce_modules` by
    (drule cenv_top_ext_same_frame >> simp[same_frame_def] >>
     disch_then (mp_tac o AP_TERM ``compile_env_ce_modules`` o CONJUNCT1) >> simp[]) >>
  `!H. dead_lo_ok_mods H (DF H) lo c cx` by fs[dead_lo_ok_mods_def] >>
  `ret_pc_ok c sm t` by (irule ret_pc_ok_frame >> metis_tac[]) >>
  `!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >>
     metis_tac[]) >>
  `t.vs_current_bb = sm.cs_current_bb /\
   t.vs_inst_idx = LENGTH sm.cs_current_insts` by fs[stmt_lands_def] >>
  qpat_x_assum `!gs es1 c sa sm. _`
    (qspecl_then [`gas_explicit marks s0.vs_gas_readings`, `mid`, `c`, `sa`, `sm`] mp_tac) >>
  (impl_tac >- simp[]) >>
  simp[stmt_frag_full_mods_def] >>
  disch_then (qspecl_then [`st0`, `sm`, `sb`, `shadow_sm`, `shadow_sb`, `t`, `G1`,
                           `tn1`, `cenv'`] mp_tac) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> strip_tac >>
  irule gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ (eval_stmts _ _) _ _ _` (irule_at Any) >>
  conj_tac >- suspend "post" >> simp[]
QED

(* bind_all has already restricted the path horizon at the midpoint.
   The remaining allocation and taint facts are horizon-independent. *)
Resume stmt_frag_cons_bind_mods[post]:
  rpt strip_tac >> gvs[] >>
  rename1 `cenv_top_ext c cfin _` >>
  qpat_assum `!tail. eval_stmts _ _ _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `sa.cs_next_id <= sm.cs_next_id` by
    (qpat_assum `stmt_env cenv _ _ stmt sa = (c,sm)`
       (mp_then Any mp_tac stmt_env_next_id) >> simp[]) >>
  drule eval_stmts_preserves_scopes_dom >> strip_tac >>
  qexists_tac `cfin` >> simp[] >>
  rpt conj_tac
  >~ [`cenv_top_ext`]
  >- (irule cenv_top_ext_trans >> qexistsl_tac [`c`, `mid.scopes`] >>
      gvs[preserves_scopes_dom_def])
  >~ [`alloca_frame`]
  >- (irule alloca_frame_trans >>
      qpat_assum `alloca_frame cenv es sa s0 c mid t` (irule_at Any) >>
      qexists_tac `sm` >> simp[] >> first_assum ACCEPT_TAC) >>
  match_mp_tac (GEN_ALL alloca_taint_kept_trans) >>
  qpat_assum `alloca_frame cenv es sa s0 c mid t` (irule_at Any) >>
  qexistsl_tac [`tn1`,`sm`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise stmt_frag_cons_bind_mods
