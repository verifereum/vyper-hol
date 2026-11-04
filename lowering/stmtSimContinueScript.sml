(* Counted actual-source simulation for a loop continue. *)
Theory stmtSimContinue
Ancestors
  stmtSimDefs stmtSimProps loweringPosts gasOutcome gasSummary gasContext fragGasMode
  gasCount fragGasPath stmtLowering compileEnv emitHelper emitHelperProps loweringSlice
  exprLoweringProps vyperInterpreter vyperState venomInst venomState
  venomExecSemantics venomExecProofs fragExec list finite_map
Libs
  monadsyntax

Theorem continue_jump_path[local]:
  sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++
    [mk_inst sa.cs_next_id JMP [Label inc] []] /\
  fn_has_code sa sb func /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted ==>
  gas_path ctx func s 0 (OK (jump_to inc s))
Proof
  strip_tac >> drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH sa.cs_current_insts) =
    SOME (mk_inst sa.cs_next_id JMP [Label inc] [])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `gas_path_edge ctx func s 0 (OK (jump_to inc s))` by
    (rewrite_tac[gas_path_edge_def] >> simp[] >>
     qexists_tac `0:num` >>
     simp[step_inst_non_invoke, mk_inst_def, gas_count_step_def,
          step_jmp_behavior, is_terminator_def] >>
     metis_tac[]) >>
  `~(jump_to inc s).vs_halted` by simp[jump_to_def] >>
  metis_tac[gas_path_rules, arithmeticTheory.ADD_CLAUSES]
QED

Theorem continue_jump_post[local]:
  stmt_state_rel ctx func cenv cx es s /\ ~s.vs_halted ==>
  stmt_post ctx func cx (InLoop ex inc) cenv cenv sa sb s
    (INR ContinueException) (es with gas_obs := []) (jump_to inc s)
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) s` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s.vs_gas_readings`, `s.vs_inst_idx`, `[]`] mp_tac) >>
     simp[stmt_state_rel_inst_idx]) >>
  pure_rewrite_tac[stmt_post_def] >> qexists_tac `cenv` >>
  simp[stmt_lands_def, cenv_top_ext_refl, stmt_state_rel_jump_to,
       jump_to_def, lookup_var_def]
QED

Theorem compile_continue_frag:
  !ctx func cx RetQ cenv ty ex inc es.
    stmt_frag ctx func cx (InLoop ex inc) RetQ cenv
      (stmt_env cenv (InLoop ex inc) ty Continue)
      (eval_stmt cx Continue) es
Proof
  rw[stmt_frag_def, stmt_framed_frag_def, stmt_env_def,
     declare_stmt_local_def, comp_bind_def, comp_return_def] >>
  qpat_x_assum `_ sa = (cenv', sb)` mp_tac >>
  simp[comp_ignore_bind_def, comp_bind_def, compile_stmt_def,
       comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `emit_inst _ _ _ sa = (_, sj)` >>
  drule emit_inst_extends >> strip_tac >>
  pure_rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  pure_rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INR ContinueException`, `es`, `OK (jump_to inc s0)`] >>
  conj_tac
  >- (simp[gas_marked_exec_def, gas_marked_path_def, Once evaluate_def,
           raise_def] >> irule continue_jump_path >> simp[] >>
      qexistsl_tac [`sa`, `sj`] >> simp[]) >>
  simp[fragExecTheory.exit_result_def] >>
  irule continue_jump_post >> simp[]
QED

val () =
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag compile_continue_frag)
  in
    if null axioms andalso null (Thm.hyp compile_continue_frag) andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then
      print "CONTINUE_AUDIT compile_continue_frag OK\n"
    else raise Fail "compile_continue_frag: admitted proof dependency"
  end;
