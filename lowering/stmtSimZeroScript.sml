(* Zero-code statement paths retain the concrete entry state. *)
Theory stmtSimZero
Ancestors
  stmtSimDefs loweringPosts gasOutcome gasSummary gasContext fragGasMode
  fragGasPath stmtLowering compileEnv loweringSlice exprLoweringProps
  vyperInterpreter vyperState

Theorem stmt_framed_frag_zero:
  stmt_framed_frag (alloca_prefix 0) ctx func cx lctx RetQ cenv m source es
  <=> stmt_frag ctx func cx lctx RetQ cenv m source es
Proof
  simp[stmt_framed_frag_def, stmt_frag_def, alloca_prefix_def]
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
  simp[stmt_post_def, fragExecTheory.exit_result_def] >>
  fs[stmt_lands_def,
       cenv_top_ext_def, compile_env_component_equality,
       stmt_state_rel_def, state_rel_def, storage_rel_def, transient_rel_def,
       accounts_rel_def, immutables_rel_def, logs_rel_def,
       immutable_alloca_sep_def]
QED

