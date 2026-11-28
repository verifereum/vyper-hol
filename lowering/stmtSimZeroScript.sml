(* Zero-code statement paths retain the concrete entry state. *)
Theory stmtSimZero
Ancestors
  stmtSimDefs loweringPosts gasOutcome gasSummary gasContext fragGasMode
  fragGasPath fragGasPathMem stmtLowering compileEnv loweringSlice exprLoweringProps
  vyperInterpreter vyperState bodySimFull gasOutcomeFull fragGasOriginPtr bodyPtrDefs
  vyperStorageFootprint gasOutcomeFullMods gasOutcomeFullCompose[qualified]

Theorem stmt_framed_frag_zero:
  stmt_framed_frag (alloca_prefix 0) ctx func cx lctx RetQ cenv m source es
  <=> stmt_frag ctx func cx lctx RetQ cenv m source es
Proof
  simp[stmt_framed_frag_def, stmt_frag_def, alloca_prefix_def]
QED

Theorem stmt_post_nil[local]:
  stmt_state_rel H ctx func cenv cx es s /\
  storage_well_formed_on cx es (FST H) /\ ~s.vs_halted /\
  ~block_is_terminated sa /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  stmt_post H ctx func cx lctx cenv cenv sa sa es s (INL ())
    (es with gas_obs := []) s
Proof
  strip_tac >>
  `stmt_state_rel H ctx func cenv cx (es with gas_obs := []) s` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s.vs_gas_readings`, `s.vs_inst_idx`, `[]`] mp_tac) >>
     simp[stmt_state_rel_inst_idx]) >>
  `storage_well_formed_on cx (es with gas_obs := []) (FST H) <=>
   storage_well_formed_on cx es (FST H)` by
    (irule storage_well_formed_on_backends >> simp[]) >>
  pure_rewrite_tac[stmt_post_def] >> qexists_tac `cenv` >>
  gvs[stmt_lands_def, cenv_top_ext_def, compile_env_component_equality,
      alloca_frame_same]
QED

Theorem stmt_frag_nil:
  !ctx func cx lctx RetQ cenv ty es.
    stmt_frag ctx func cx lctx RetQ cenv (stmts_env cenv lctx ty []) (eval_stmts cx []) es
Proof
  rw[stmt_frag_def, stmt_framed_frag_def, stmts_env_def, comp_return_def] >>
  PURE_REWRITE_TAC[gas_outcome_def] >> qexists_tac `[]` >>
  disj2_tac >> disj1_tac >>
  PURE_REWRITE_TAC[gas_summary_at_def] >>
  qexistsl_tac [`INL ()`, `es`, `OK s0`] >>
  conj_tac
  >- simp[gas_marked_exec_def, gas_marked_path_def, gas_path_rules,
          Once evaluate_def, return_def] >>
  simp[fragExecTheory.exit_result_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  irule stmt_post_nil >> simp[]
QED

Theorem stmt_frag_nil_mem:
  !d ctx func cx lctx RetQ cenv ty es.
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmts_env cenv lctx ty []) (eval_stmts cx []) es
Proof
  rw[stmt_frag_mem_def, stmts_env_def, comp_return_def] >>
  PURE_REWRITE_TAC[gas_outcome_def] >> qexists_tac `[]` >>
  disj2_tac >> disj1_tac >>
  PURE_REWRITE_TAC[gas_summary_at_def] >>
  qexistsl_tac [`INL ()`, `es`, `OK s0`] >>
  conj_tac
  >- simp[gas_marked_exec_def, gas_marked_path_def, gas_path_mem_rules,
          Once evaluate_def, return_def] >>
  simp[fragExecTheory.exit_result_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  `stmt_post H ctx func cx lctx cenv cenv sa sa es s0 (INL ())
     (es with gas_obs := []) s0` by (irule stmt_post_nil >> simp[]) >>
  gvs[stmt_post_def] >> qexists_tac `cenv` >> simp[]
QED

Theorem stmt_frag_nil_full:
  !DF lo d ctx shadow_ctx PG func shadow_func cx lctx RetQ cenv ty es.
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmts_env cenv lctx ty []) (stmts_env (gas_shadow_env T cenv) lctx ty [])
      (eval_stmts cx []) es
Proof
  rw[stmt_frag_full_def, stmts_env_def, comp_return_def] >>
  `!tail. eval_stmts cx [] (es with gas_obs := tail) =
          (INL (), es with gas_obs := tail)` by
    simp[Once evaluate_def, return_def] >>
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- (irule gasOutcomeFullComposeTheory.gas_outcome_full_mods_bad_nil >> simp[]) >>
  PURE_REWRITE_TAC[gas_outcome_full_mods_def] >>
  qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`INL ()`, `es`, `OK s0`, `G0`, `tn0`] >>
  conj_tac >- simp[gas_explicit_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  conj_tac >- simp[gas_origin_ptr_path_rules] >>
  disj1_tac >> qexists_tac `s0` >> simp[] >>
  `stmt_post H ctx func cx lctx cenv cenv sa sa es s0 (INL ())
     (es with gas_obs := []) s0` by (irule stmt_post_nil >> simp[]) >>
  `return_buf_sep d cenv (es with gas_obs := []) s0` by
    (Cases_on `d` >> simp[return_buf_sep_def] >>
     rename1 `return_buf_sep (SOME buf) _ _ _` >> PairCases_on `buf` >>
     fs[return_buf_sep_def] >> first_assum ACCEPT_TAC) >>
  `ghost_inv_at (DF H) lo d cenv cx (es with gas_obs := []) G0 tn0 s0` by
    (qpat_assum `ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0` mp_tac >>
     simp_tac (srw_ss()) [ghost_inv_at_def] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  gvs[stmt_post_def] >> qexists_tac `cenv` >> simp[]
QED
