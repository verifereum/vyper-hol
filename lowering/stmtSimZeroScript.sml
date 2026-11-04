(* Zero-code statement paths retain the concrete entry state. *)
Theory stmtSimZero
Ancestors
  stmtSimDefs loweringPosts gasOutcome gasSummary gasContext fragGasMode
  fragGasPath fragGasPathMem stmtLowering compileEnv loweringSlice exprLoweringProps
  vyperInterpreter vyperState

Theorem stmt_framed_frag_zero:
  stmt_framed_frag (alloca_prefix 0) ctx func cx lctx RetQ cenv m source es
  <=> stmt_frag ctx func cx lctx RetQ cenv m source es
Proof
  simp[stmt_framed_frag_def, stmt_frag_def, alloca_prefix_def]
QED

Theorem stmt_post_nil[local]:
  stmt_state_rel ctx func cenv cx es s /\ ~s.vs_halted /\
  ~block_is_terminated sa /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  stmt_post ctx func cx lctx cenv cenv sa sa s (INL ())
    (es with gas_obs := []) s
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) s` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s.vs_gas_readings`, `s.vs_inst_idx`, `[]`] mp_tac) >>
     simp[stmt_state_rel_inst_idx]) >>
  pure_rewrite_tac[stmt_post_def] >> qexists_tac `cenv` >>
  simp[stmt_lands_def, cenv_top_ext_def, compile_env_component_equality]
QED

Theorem stmt_frag_nil:
  !ctx func cx lctx RetQ cenv ty es.
    stmt_frag ctx func cx lctx RetQ cenv (stmts_env cenv lctx ty []) (eval_stmts cx []) es
Proof
  rw[stmt_frag_def, stmt_framed_frag_def, stmts_env_def, comp_return_def] >>
  PURE_REWRITE_TAC[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  PURE_REWRITE_TAC[gas_summary_at_def] >>
  qexistsl_tac [`INL ()`, `es`, `OK s0`] >>
  conj_tac
  >- simp[gas_marked_exec_def, gas_marked_path_def, gas_path_rules,
          Once evaluate_def, return_def] >>
  simp[fragExecTheory.exit_result_def] >>
  irule stmt_post_nil >> simp[]
QED

Theorem stmt_frag_nil_mem:
  !d ctx func cx lctx RetQ cenv ty es.
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmts_env cenv lctx ty []) (eval_stmts cx []) es
Proof
  rw[stmt_frag_mem_def, stmts_env_def, comp_return_def] >>
  PURE_REWRITE_TAC[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  PURE_REWRITE_TAC[gas_summary_at_def] >>
  qexistsl_tac [`INL ()`, `es`, `OK s0`] >>
  conj_tac
  >- simp[gas_marked_exec_def, gas_marked_path_def, gas_path_mem_rules,
          Once evaluate_def, return_def] >>
  simp[fragExecTheory.exit_result_def] >>
  `stmt_post ctx func cx lctx cenv cenv sa sa s0 (INL ())
     (es with gas_obs := []) s0` by (irule stmt_post_nil >> simp[]) >>
  gvs[stmt_post_def] >> qexists_tac `cenv` >> simp[]
QED

