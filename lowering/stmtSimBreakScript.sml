(* Counted actual-source simulation for a loop break. *)
Theory stmtSimBreak
Ancestors
  stmtSimDefs stmtSimProps loweringPosts gasOutcome gasSummary gasContext fragGasMode
  fragGasPath stmtLowering compileEnv emitHelper emitHelperProps loweringSlice
  exprLoweringProps vyperInterpreter vyperState venomInst venomState
  venomExecSemantics venomExecProofs fragExec list finite_map
Libs
  monadsyntax

Theorem compile_break_frag:
  !ctx func cx RetQ cenv ty ex inc es.
    stmt_frag ctx func cx (InLoop ex inc) RetQ cenv
      (stmt_env cenv (InLoop ex inc) ty Break)
      (eval_stmt cx Break) es
Proof
  rw[stmt_frag_def, stmt_env_def, declare_stmt_local_def, comp_bind_def,
     comp_return_def] >>
  qpat_x_assum `_ sa = (cenv', sb)` mp_tac >>
  simp[comp_ignore_bind_def, comp_bind_def, compile_stmt_def,
       comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `emit_inst _ _ _ sa = (_, sj)` >>
  disj1_tac >> qexistsl_tac [`jump_to ex s0`, `cenv`] >>
  imp_res_tac emit_inst_extends >>
  qspecl_then [`ctx`, `func`, `sa`, `sj`, `s0`,
               `mk_inst sa.cs_next_id JMP [Label ex] []`, `ex`]
    mp_tac run_from_jump_end >>
  impl_tac
  >- simp[venomInstTheory.mk_inst_def, is_terminator_def, step_jmp_behavior] >>
  strip_tac >>
  simp[stmt_lands_def, cenv_top_ext_refl, stmt_state_rel_jump_to] >>
  rpt conj_tac >> TRY (simp[jump_to_def, lookup_var_def] >> NO_TAC) >>
  rpt strip_tac >> metis_tac[]
QED
