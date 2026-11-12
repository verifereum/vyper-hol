(*
 * The statement-list cons case of the full body induction: the head's
 * joint fragment and the tail's, composed through one source/memory/
 * pointer witness, the head's landing state feeding the tail's entry.
 *
 * TOP-LEVEL:
 *   stmt_frag_full_cons_env -- the joint twin of stmtFragPtr's
 *     stmt_frag_cons_env_ptr, over paired original/shadow compilations
 *)
Theory bodyFullStmtsCons
Ancestors
  bodySimFull gasOutcomeFull gasOutcomeFullCompose fragGasOriginPtr
  gasShadowState stmtFragPtr stmtSimSeqEnv stmtSimProps stmtSimDefs
  loweringPosts bodyMemoryDefs bodyPtrDefs bodyExprPreFacts
  stmtLoweringMono fragExec gasSummaryCompose gasExemptCert exprSimDefs
  compileEnv stmtLowering vyperInterpreter vyperState
  vyperEvalPreservesScopes list

(* The first two premises are the shadow compiler facts the cons case
   needs: termination agrees across shadow states, and the head's
   stmt_env commutes with gas_shadow_stmt. They are instances of
   gas_shadow_state_terminated and of gas_shadow_compile_stmt with
   gas_shadow_compiles_declare_stmt_local, which this base lacks. *)
Theorem stmt_frag_full_cons_env:
  !D lo d ctx shadow_ctx PG func shadow_func cx lctx RetQ cenv ty
   stmt shadow_stmt ss shadow_ss es.
    (!s t. gas_shadow_state s t ==>
           (block_is_terminated s <=> block_is_terminated t)) /\
    gas_shadow_compiles (stmt_env cenv lctx ty stmt)
      (stmt_env cenv lctx ty shadow_stmt) /\
    stmt_frag_full (D, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ty stmt) (stmt_env cenv lctx ty shadow_stmt)
      (eval_stmt cx stmt) es /\
    (!gs es1 c sa sm.
       eval_stmt cx stmt (es with gas_obs := gs) = (INL (), es1) /\
       stmt_env cenv lctx ty stmt sa = (c, sm) /\
       cenv_top_ext cenv c es1.scopes ==>
       stmt_frag_full (D, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
         cx lctx RetQ c
         (stmts_env c lctx ty ss) (stmts_env c lctx ty shadow_ss)
         (eval_stmts cx ss) es1) ==>
    stmt_frag_full (D, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmts_env cenv lctx ty (stmt::ss))
      (stmts_env cenv lctx ty (shadow_stmt::shadow_ss))
      (eval_stmts cx (stmt::ss)) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmts_env _ _ _ (stmt::ss) _ = _` mp_tac >>
  simp[stmts_env_cons, comp_bind_def] >> pairarg_tac >> simp[] >>
  strip_tac >> rename1 `stmt_env cenv lctx ty stmt sa = (c, sm)` >>
  `~block_is_terminated shadow_sa` by metis_tac[] >>
  qpat_x_assum `stmts_env _ _ _ (shadow_stmt::shadow_ss) _ = _` mp_tac >>
  simp[stmts_env_cons, comp_bind_def] >> pairarg_tac >> simp[] >>
  strip_tac >>
  rename1 `stmt_env cenv lctx ty shadow_stmt shadow_sa = (c', shadow_sm)` >>
  `c' = c /\ gas_shadow_state sm shadow_sm` by
    (qpat_x_assum `gas_shadow_compiles _ _` mp_tac >>
     simp[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`, `shadow_sa`] mp_tac) >> simp[]) >>
  gvs[] >>
  qspecl_then [`cenv`, `lctx`, `ty`, `stmt`, `sa`, `c`, `sm`] mp_tac
    stmt_env_reserved >>
  simp[cj 1 compile_stmt_cs_mono] >> strip_tac >>
  `cs_extends sm sb /\ sm.cs_next_var <= sb.cs_next_var` by
    (qspecl_then [`c`, `lctx`, `ty`, `ss`] mp_tac stmts_env_cs_mono >>
     simp[cs_mono_def] >> metis_tac[]) >>
  `cs_extends shadow_sa shadow_sm` by
    (`stmts_env cenv lctx ty [shadow_stmt] shadow_sa = (c, shadow_sm)` by
       simp[stmts_env_cons, comp_bind_def, stmts_env_def, comp_return_def] >>
     qspecl_then [`cenv`, `lctx`, `ty`, `[shadow_stmt]`] mp_tac
       stmts_env_cs_mono >>
     simp[cs_mono_def] >> metis_tac[]) >>
  `cs_extends shadow_sm shadow_sb` by
    (qspecl_then [`c`, `lctx`, `ty`, `shadow_ss`] mp_tac stmts_env_cs_mono >>
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
  disch_then (qspecl_then [`sa`, `sm`, `shadow_sa`, `shadow_sm`, `s0`,
                           `G0`, `tn0`, `c`] mp_tac) >>
  simp[] >> strip_tac >>
  simp[Once evaluate_def, ignore_bind_def] >>
  irule gas_outcome_full_bind_lands >> rpt conj_tac
  >~ [`gas_marked_exec`]
  >- (rpt strip_tac >> irule (cj 2 gas_exempt_cert_rules) >> simp[] >>
      qexistsl_tac [`mid`, `t`] >> Cases_on `v` >> fs[])
  >~ [`gas_exempt_cert _ _ _ (ignore_bind (eval_stmt _ _) _)`]
  >- (rpt strip_tac >> irule (cj 3 gas_exempt_cert_rules) >> simp[]) >>
  qpat_x_assum `gas_outcome_full _ _ (eval_stmt _ _) _ _ _`
    (irule o MATCH_MP
       (REWRITE_RULE [GSYM AND_IMP_INTRO] gas_outcome_full_post_source)) >>
  reverse conj_tac
  >- (rpt strip_tac >> fs[] >> Cases_on `res` >> simp[] >>
      qpat_x_assum `!tail. stmt_exit_ptr _ (_ with gas_obs := tail) _ _ _`
        (qspec_then `[]` mp_tac) >>
      simp[stmt_exit_ptr_def, expr_exit_def]) >>
  rpt strip_tac >> gvs[] >>
  Cases_on `res`
  >- (rename1 `INL u` >> Cases_on `u` >> gvs[] >> suspend "tail") >>
  rename1 `INR exc` >> gvs[] >>
  qexists_tac `cenv''` >> fs[stmt_lands_def] >>
  irule return_buf_frame_frame >>
  qexistsl_tac [`cenv''`, `t`, `sm`] >> simp[]
QED

Resume stmt_frag_full_cons_env[tail]:
  rename1 `!tail. eval_stmt cx stmt (es with gas_obs := xs ++ tail) =
             (INL (), ee0 with gas_obs := tail)` >>
  `ee0 with gas_obs := [] = ee0` by
    gvs[evaluation_state_component_equality] >>
  `eval_stmt cx stmt (es with gas_obs := xs) = (INL (), ee0)` by
    (qpat_assum `!tail. eval_stmt _ _ _ = _` (qspec_then `[]` mp_tac) >>
     qpat_assum `ee0 with gas_obs := [] = ee0`
       (fn th => rewrite_tac[APPEND_NIL, th])) >>
  `gas_admissible (eval_stmts cx ss) (stmt_res_ok lctx) ee0` by
    (qpat_assum `ee0 with gas_obs := [] = ee0` (SUBST1_TAC o SYM) >>
     irule gas_admissible_stmts_tail >> metis_tac[]) >>
  `c.ce_return_pc = cenv.ce_return_pc /\
   c.ce_return_buf = cenv.ce_return_buf /\
   (c.ce_is_ctor <=> cenv.ce_is_ctor)` by
    metis_tac[cenv_top_ext_return_pc, cenv_top_ext_return_buf,
              cenv_top_ext_is_ctor] >>
  `dead_lo_ok D lo c cx` by fs[dead_lo_ok_def] >>
  `ret_pc_ok c sm t` by (irule ret_pc_ok_frame >> metis_tac[]) >>
  `!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >>
     metis_tac[]) >>
  `t.vs_current_bb = sm.cs_current_bb /\
   t.vs_inst_idx = LENGTH sm.cs_current_insts` by fs[stmt_lands_def] >>
  qpat_x_assum `!gs es1 c sa sm. _`
    (qspecl_then [`xs`, `ee0`, `c`, `sa`, `sm`] mp_tac) >>
  impl_tac >- simp[] >>
  simp[stmt_frag_full_def] >>
  disch_then (qspecl_then [`sm`, `sb`, `shadow_sm`, `shadow_sb`, `t`, `G'`,
                           `tn'`, `cenv'`] mp_tac) >>
  impl_tac >- simp[] >>
  strip_tac >>
  qpat_x_assum `gas_outcome_full _ _ (eval_stmts _ _) _ _ _`
    (irule o MATCH_MP
       (REWRITE_RULE [GSYM AND_IMP_INTRO] gas_outcome_full_post_source)) >> simp[] >>
  rpt strip_tac >> gvs[] >>
  rename1 `cenv_top_ext c cfin _` >>
  qpat_x_assum `!tail. eval_stmts _ _ _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  drule eval_stmts_preserves_scopes_dom >> strip_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >>
     simp[]) >>
  qexists_tac `cfin` >> simp[] >>
  irule cenv_top_ext_trans >> qexistsl_tac [`c`, `ee0.scopes`] >>
  gvs[preserves_scopes_dom_def]
QED

Finalise stmt_frag_full_cons_env
