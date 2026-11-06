(* A terminal RETURN reads only its explicitly bounded output window. *)
Theory terminalReturnMem
Ancestors
  fragExecMem fragExec memSafeRun instMemFrontier venomExecSemantics
  venomInst venomState words arithmetic emitHelper compileEnv

Theorem terminal_return_safe_exit:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id RETURN [dst;len] []) /\
  eval_operand dst s = SOME (n2w d) /\
  eval_operand len s = SOME (n2w n) /\
  d + n <= s.vs_alloca_next /\ ~s.vs_halted ==>
  ?fuel r. run_from fuel ctx fn s = r /\ exit_result r /\
           mem_safe_run fuel ctx fn s
Proof
  rpt strip_tac >>
  `?q. step_inst 0 ctx (mk_inst id RETURN [dst;len] []) s = Halt q` by
    simp[step_inst_non_invoke, step_inst_base_def, mk_inst_def] >>
  `inst_mem_below_frontier (mk_inst id RETURN [dst;len] []) s` by
    (simp[below_frontier_RETURN] >>
     `w2n (n2w d : bytes32) <= d /\
      w2n (n2w n : bytes32) <= n` by simp[w2n_n2w, MOD_LESS_EQ] >>
     gvs[w2n_n2w] >> decide_tac) >>
  `mem_safe_step 0 ctx (mk_inst id RETURN [dst;len] []) s` by
    simp[mem_safe_step_non_invoke, mk_inst_def] >>
  drule run_from_step_exit >> disch_then drule >>
  disch_then drule >> simp[] >> strip_tac >>
  qexists_tac `0` >> simp[exit_result_def]
QED

Theorem emit_return_safe_exit:
  emit_inst RETURN [dst;len] [] st = (x,en) /\
  fn_has_code st en fn /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  eval_operand dst s = SOME (n2w d) /\
  eval_operand len s = SOME (n2w n) /\ d+n <= s.vs_alloca_next ==>
  ?fuel r. run_from fuel ctx fn s = r /\ exit_result r /\
           mem_safe_run fuel ctx fn s
Proof
  strip_tac >>
  qpat_x_assum `emit_inst _ _ _ _ = _` mp_tac >>
  simp[emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[] >>
  drule fn_has_code_same_block >> simp[] >> strip_tac >>
  metis_tac[terminal_return_safe_exit]
QED
