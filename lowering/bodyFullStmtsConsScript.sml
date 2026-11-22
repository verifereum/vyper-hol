(*
 * The statement-list cons case of the full body induction, over the
 * finite-horizon joint judgment: the head's joint fragment and the tail's,
 * composed through one source/memory/pointer witness, the head's landing
 * state feeding the tail's entry.
 *
 * TOP-LEVEL:
 *   stmt_frag_full_cons_env -- body_stmts_cons_case_full's composition
 *)
Theory bodyFullStmtsCons
Ancestors
  bodySimFull gasOutcomeFullCompose gasOutcomeFullStmts fragGasOriginPtr
  bodyFullIfExpReach
  gasShadowState gasShadowCompileBase gasShadowStmtEnv gasShadowCompileStmtBase bodyFullShared
  stmtFragPtr stmtSimSeqEnv stmtSimProps stmtSimDefs
  loweringPosts bodyMemoryDefs bodyPtrDefs bodyExprPreFacts
  stmtLoweringMono fragExec gasSummaryCompose gasExemptCert exprSimDefs
  compileEnv stmtLowering vyperInterpreter vyperState vyperStorageTrace
  vyperEvalPreservesScopes vyperStorageFootprint contextRawReachable unitMemInv
  ptrDiscipline list

(* Notes for the proof (may be ignored):
   - A pre-horizon proof of this composition, over a generic shadow
     statement with two shadow premises, is in git at 53fe3b2d9
     (lowering/bodyFullStmtsConsScript.sml).  Under the horizon its
     gas_outcome_full_bind_lands step no longer fits: the tail's input
     block is guarded by every horizon valid for the head's end trace.
     bodyFullIf's compile_if_stmt_frag_full composes the same way through
     gas_outcome_full_bind_all, reading H-free facts of the midpoint at
     storage_trace_horizon mid.storage_trace.
   - The shadow head is live by gas_shadow_terminated (bodyFullShared).
     Its returned environment and compile state are related to the original
     results by gas_shadow_stmt_env_env; the shadow tail starts from those
     returned values.
   - dead_lo_ok depends on the environment only through ce_is_ctor, which
     cenv_top_ext preserves (cenv_top_ext_is_ctor). *)
Theorem stmt_frag_full_cons_env:
  !DF lo d ctx shadow_ctx PG func shadow_func cx lctx RetQ cenv ty
   stmt ss es.
    (ctx_has_dalloca ctx /\ MEM func ctx.ctx_functions ==>
      !bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
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
         (eval_stmts cx ss) es1) ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmts_env cenv lctx ty (stmt::ss))
      (stmts_env (gas_shadow_env T cenv) lctx ty (MAP gas_shadow_stmt (stmt::ss)))
      (eval_stmts cx (stmt::ss)) es
Proof
  rpt gen_tac >> strip_tac >>
  `gas_shadow_compiles_env T (stmt_env cenv lctx ty stmt)
     (stmt_env (gas_shadow_env T cenv) lctx ty (gas_shadow_stmt stmt))` by
    irule gas_shadow_stmt_env_env >>
  simp[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
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
  qpat_x_assum `stmt_frag_full _ _ _ _ _ (stmt_env _ _ _ _) _ _ _` mp_tac >>
  simp[stmt_frag_full_def] >>
  disch_then (qspecl_then [`st0`, `sa`, `sm`, `shadow_sa`, `shadow_sm`, `s0`,
                           `G0`, `tn0`, `c`] mp_tac) >>
  simp[] >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ headQ headR` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (eval_stmt cx stmt) (es,s0,G0,tn0)
     (\H res ee G tn t. headQ H res ee G tn t /\
       ?cm. gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (s0,G0,tn0) cm (OK t,G,tn)) headR` by
    (irule gas_outcome_full_post_path >>
     qpat_assum `gas_outcome_full _ _ _ _ _ _ headQ headR` (irule_at Any) >>
     rpt strip_tac >> simp[] >> goal_assum (drule_at Any)) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ headQ headR` kall_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ pathQ headR` >>
  simp[Once evaluate_def, ignore_bind_def] >>
  irule gas_outcome_full_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec`]
  >- (rpt strip_tac >> irule (cj 2 gas_exempt_cert_rules) >> simp[] >>
      qexistsl_tac [`mid`, `t`] >> Cases_on `v` >> fs[])
  >~ [`gas_exempt_cert _ _ _ (ignore_bind (eval_stmt _ _) _)`]
  >- (rpt strip_tac >> irule (cj 3 gas_exempt_cert_rules) >> simp[])
  >~ [`storage_trace_frame (eval_stmt _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >~ [`storage_trace_frame _`]
  >- simp[evaluate_storage_trace_frame] >>
  qexists_tac `\H res ee G tn t. pathQ H res ee G tn t /\
                    ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac >- suspend "continue" >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  conj_tac >- simp[] >>
  simp[Abbr `headR`] >> rpt strip_tac >>
  Cases_on `res` >> simp[halt_exit_def] >>
  qpat_x_assum `!tail. stmt_exit_ptr _ (_ with gas_obs := tail) _ _ _`
    (qspec_then `[]` mp_tac) >>
  simp[stmt_exit_ptr_def, expr_exit_def] >> fs[halt_exit_def] >>
  metis_tac[]
QED

Resume stmt_frag_full_cons_env[continue]:
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

Resume stmt_frag_full_cons_env[tail]:
  `!fn inst s. frag_reachable ctx func t fn inst s ==> dalloca_fmp_headroom inst s` by
    (Cases_on `ctx_has_dalloca ctx`
     >- (`!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by fs[] >>
         qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) _ (OK t,G1,tn1)` (fn path =>
         qpat_assum `!bb. MEM bb func.fn_blocks ==> _` (fn no_phi =>
         qpat_assum `!fn inst s. frag_reachable ctx func s0 fn inst s ==> _`
           (fn safe => ACCEPT_TAC (MATCH_MP gas_origin_ptr_path_dalloca_fmp_headroom
             (LIST_CONJ [path,no_phi,safe])))))) >>
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
  `!H. dead_lo_ok H (DF H) lo c cx` by fs[dead_lo_ok_def] >>
  `ret_pc_ok c sm t` by (irule ret_pc_ok_frame >> metis_tac[]) >>
  `!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >>
     metis_tac[]) >>
  `t.vs_current_bb = sm.cs_current_bb /\
   t.vs_inst_idx = LENGTH sm.cs_current_insts` by fs[stmt_lands_def] >>
  qpat_x_assum `!gs es1 c sa sm. _`
    (qspecl_then [`gas_explicit marks s0.vs_gas_readings`, `mid`, `c`, `sa`, `sm`] mp_tac) >>
  (impl_tac >- simp[]) >>
  simp[stmt_frag_full_def] >>
  disch_then (qspecl_then [`st0`, `sm`, `sb`, `shadow_sm`, `shadow_sb`, `t`, `G1`,
                           `tn1`, `cenv'`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ (eval_stmts _ _) _ _ _` (irule_at Any) >>
  conj_tac >- suspend "post" >> simp[]
QED

Resume stmt_frag_full_cons_env[post]:
  rpt strip_tac >> gvs[] >>
  rename1 `cenv_top_ext c cfin _` >>
  qpat_x_assum `!tail. eval_stmts _ _ _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  drule eval_stmts_preserves_scopes_dom >> strip_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  qexists_tac `cfin` >> simp[] >>
  `sa.cs_next_id <= sm.cs_next_id` by 
    (qspecl_then [`cenv`, `lctx`, `ty`, `stmt`, `sa`, `c`, `sm`] mp_tac
       stmt_env_next_id >> simp[]) >>
  rpt conj_tac
  >~ [`cenv_top_ext`]
  >- (irule cenv_top_ext_trans >> qexistsl_tac [`c`, `mid.scopes`] >>
      gvs[preserves_scopes_dom_def])
  >~ [`alloca_frame`]
  >- (mp_tac (Q.INST [`c0` |-> `cenv`, `e0` |-> `es`, `sa0` |-> `sa`,
                      `c1` |-> `c`, `e1` |-> `mid`, `s1` |-> `t`, `sa1` |-> `sm`,
                      `c2` |-> `cfin`, `e2` |-> `ee`, `s2` |-> `t'`]
                     alloca_frame_trans) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then ACCEPT_TAC) >>
  mp_tac (Q.INST [`c0` |-> `cenv`, `e0` |-> `es`, `sa0` |-> `sa`,
                  `c1` |-> `c`, `e1` |-> `mid`, `s1` |-> `t`, `sa1` |-> `sm`,
                  `tn2` |-> `tn'`] alloca_taint_kept_trans) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED

Finalise stmt_frag_full_cons_env
