(* Counted actual-source simulation for a loop break. *)
Theory stmtSimBreak
Ancestors
  stmtSimDefs stmtSimProps loweringPosts gasOutcome gasSummary gasContext fragGasMode
  gasCount fragGasPath stmtLowering compileEnv emitHelper emitHelperProps loweringSlice
  exprLoweringProps vyperInterpreter vyperState venomInst venomState
  venomExecSemantics venomExecProofs fragExec list finite_map
Libs
  monadsyntax

Theorem break_jump_path[local]:
  emit_inst JMP [Label ex] [] sa = (u,sb) /\
  fn_has_code sa sb func /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s0.vs_halted ==>
  gas_path ctx func s0 0 (OK (jump_to ex s0))
Proof
  Cases_on `u` >> strip_tac >> drule emit_inst_extends >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH sa.cs_current_insts) =
    SOME (mk_inst sa.cs_next_id JMP [Label ex] [])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `gas_path_edge ctx func s0 0 (OK (jump_to ex s0))` by
    (rewrite_tac[gas_path_edge_def] >> simp[] >>
     qexists_tac `0:num` >>
     simp[step_inst_non_invoke, mk_inst_def, step_jmp_behavior,
          gas_count_step_def, is_terminator_def] >> metis_tac[]) >>
  drule (cj 2 gas_path_rules) >>
  disch_then (qspec_then `0` mp_tac) >>
  simp[jump_to_def, Once (cj 1 gas_path_rules)]
QED

Theorem stmt_post_break[local]:
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
  pure_rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  pure_rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INR BreakException`, `es`, `OK (jump_to ex s0)`] >>
  conj_tac
  >- (simp[gas_marked_exec_def, gas_marked_path_def, Once evaluate_def,
           raise_def] >> irule break_jump_path >> simp[] >>
      goal_assum (drule_at Any) >> simp[]) >>
  simp[fragExecTheory.exit_result_def] >>
  irule stmt_post_break >> simp[]
QED

val () =
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag compile_break_frag)
  in
    if null axioms andalso null (Thm.hyp compile_break_frag) andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then
      print "STMT_BREAK_AUDIT compile_break_frag OK\n"
    else raise Fail "compile_break_frag: admitted proof dependency"
  end;
