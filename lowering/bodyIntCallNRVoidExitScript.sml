(* Normal void fallthrough executes the optional guard release before RET. *)
Theory bodyIntCallNRVoidExit
Ancestors
  bodyIntCallSharpReturn externalReturnSelectedSuffix stmtSimReturn
  emitHelperProps exprLoweringProps compileEnv loweringStateRelDefs fragExec

Theorem intcall_void_unlock_ret:
  compile_return_unlock ce sa = ((),su) /\
  emit_inst RET [rpc] [] su = ((),sb) /\ fn_has_code sa sb func /\
  stmt_state_rel ctx func ce cx (es with scopes := []) s /\
  ce.ce_returns_count = 0 /\ ce.ce_return_buf = NONE /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (?pc. eval_operand rpc s = SOME pc) ==>
  ?n. gas_path ctx func s n
        (IntRet <|iret_values := []; iret_adopt_fmp := NONE|>
          (return_unlock_state ce s)) /\
      intret_q func ce cx NoneTV NoneV (es with scopes := [])
        (IntRet <|iret_values := []; iret_adopt_fmp := NONE|>
          (return_unlock_state ce s)) /\
      (return_unlock_state ce s).vs_memory = s.vs_memory
Proof
  strip_tac >>
  `cs_extends sa su /\ cs_extends su sb` by
    metis_tac[compile_return_unlock_shape, cs_extends_emit_inst] >>
  `fn_has_code sa su func /\ fn_has_code su sb func` by
    metis_tac[fn_has_code_split] >>
  `~s.vs_call_ctx.cc_static` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `?n r. gas_path ctx func s n r /\ exit_result r /\
    r = IntRet <|iret_values := []; iret_adopt_fmp := NONE|>
          (return_unlock_state ce s)` by
    (ho_match_mp_tac (Q.INST
       [`Q` |-> `\t. t = return_unlock_state ce s`, `sb` |-> `su`]
       return_normalizing_prefix_path) >>
     simp[] >> conj_tac
     >- (irule compile_return_unlock_frag >> simp[]) >>
     rpt strip_tac >> qexists_tac `0` >> simp[exit_result_def] >>
     irule emitted_memory_ret_path >> simp[] >>
     qexistsl_tac [`rpc`, `su`, `sb`] >> simp[eval_operand_return_unlock]) >>
  gvs[] >> qexists_tac `n` >> simp[] >>
  simp[intret_q_def] >> qexists_tac `s` >>
  simp[result_rel_def, intret_vals_match_def] >>
  fs[stmt_state_rel_def]
QED
