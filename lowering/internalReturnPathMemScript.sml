(* Counted memory-safe terminal steps of an internal return. *)
Theory internalReturnPathMem
Ancestors
  fragGasPathMem fragExec gasCount memSafeRun instMemFrontier
  venomExecSemantics venomState venomInst emitHelperProps stmtSimReturn

Theorem internal_ret_path_mem:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst iid RET ops []) /\
  step_inst_base (mk_inst iid RET ops []) s = IntRet ir t ==>
  gas_path_mem ctx func s 0 (IntRet ir t)
Proof
  strip_tac >> irule (cj 3 gas_path_mem_rules) >> simp[exit_result_def] >>
  simp[gas_path_mem_edge_def] >> qexists_tac `0` >>
  simp[step_inst_non_invoke, gas_count_step_def, mk_inst_def,
       mem_safe_step_non_invoke, below_frontier_no_ranges,
       inst_dload_in_section_def, exit_result_def]
QED

Theorem emit_internal_ret_path_mem:
  emit_inst RET (ops ++ [Var rpc]) [] sa = ((),sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operands ops s = SOME vals /\ lookup_var rpc s = SOME pc ==>
  gas_path_mem ctx func s 0
    (IntRet <|iret_values := vals; iret_adopt_fmp := NONE|> s)
Proof
  strip_tac >> drule emit_inst_extends >> strip_tac >>
  `?bb. lookup_block sa.cs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sa.cs_current_insts) =
      SOME (mk_inst sa.cs_next_id RET (ops ++ [Var rpc]) [])` by
    (drule fn_has_code_same_block >>
     disch_then (qspec_then `[mk_inst sa.cs_next_id RET (ops ++ [Var rpc]) []]`
       mp_tac) >> simp[] >> metis_tac[arithmeticTheory.ADD_CLAUSES]) >>
  irule internal_ret_path_mem >> simp[] >>
  qexistsl_tac [`sa.cs_next_id`, `ops ++ [Var rpc]`] >>
  simp[] >> irule stmtSimReturnTheory.step_ret_values >> simp[] >> metis_tac[]
QED
