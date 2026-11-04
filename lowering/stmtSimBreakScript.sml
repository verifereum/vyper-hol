(* Counted actual-source simulation for a loop break. *)
Theory stmtSimBreak
Ancestors
  stmtSimDefs stmtSimProps loweringPosts gasOutcome gasSummary gasContext fragGasMode
  gasCount fragGasPath stmtLowering compileEnv emitHelper emitHelperProps loweringSlice
  exprLoweringProps vyperInterpreter vyperState venomInst venomState
  venomExecSemantics venomExecProofs fragExec list finite_map
Libs
  monadsyntax


Theorem stmt_post_break:
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted ==>
  stmt_post ctx func cx (InLoop ex inc) cenv cenv sa sb s0
    (INR BreakException) (es with gas_obs := []) (jump_to ex s0)
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) s0` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`] mp_tac) >>
     simp[stmt_state_rel_inst_idx]) >>
  pure_rewrite_tac[stmt_post_def] >> qexists_tac `cenv` >>
  simp[stmt_lands_def, cenv_top_ext_refl, stmt_state_rel_jump_to,
       jump_to_def, lookup_var_def]
QED

Theorem compile_break_frag:
  !ctx func cx RetQ cenv ty ex inc es.
    stmt_frag ctx func cx (InLoop ex inc) RetQ cenv
      (stmt_env cenv (InLoop ex inc) ty Break)
      (eval_stmt cx Break) es
Proof
  rw[stmt_frag_def, stmt_framed_frag_def] >>
  qpat_x_assum `_ sa = (cenv', sb)` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, comp_ignore_bind_def,
       comp_bind_def, compile_stmt_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `emit_inst _ _ _ sa = (_, sj)` >>
  drule emit_inst_extends >> strip_tac >>
  pure_rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  pure_rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INR BreakException`, `es`, `OK (jump_to ex s0)`] >>
  conj_tac
  >- (simp[gas_marked_exec_def, gas_marked_path_def, Once evaluate_def,
           raise_def] >> irule emit_jump_zero_path >> simp[] >>
      qexistsl_tac [`sa`, `sj`] >> simp[]) >>
  simp[fragExecTheory.exit_result_def] >>
  irule stmt_post_break >> simp[]
QED

