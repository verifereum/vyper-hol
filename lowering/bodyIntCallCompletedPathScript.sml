Theory bodyIntCallCompletedPath
Ancestors
  bodyIntCallCountedPath bodyIntCallCallerFrame fragGasFocus intCallStep
  fragGasMode fragGasPath gasSummary fragExec venomInst

Theorem invoke_abort_counted_path:
  gas_invoke_entry (ctx,func) t callee entered /\
  gas_path ctx callee entered n (Abort a cs) ==>
  gas_path ctx func t n (Abort a cs)
Proof
  rw[gas_invoke_entry_def] >>
  drule_all counted_invoke_abort >> strip_tac >>
  irule (cj 3 gas_path_rules) >> simp[exit_result_def] >>
  simp[gas_path_edge_def] >>
  qexists_tac `fuel` >>
  simp[exit_result_def]
QED

Theorem invoke_intret_counted_path:
  gas_invoke_entry (ctx,func) t callee entered /\
  gas_path ctx callee entered n (IntRet ir cs) /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  bind_outputs inst.inst_outputs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state t cs)) = SOME u ==>
  gas_path ctx func t n (OK (u with vs_inst_idx := SUC t.vs_inst_idx))
Proof
  rw[gas_invoke_entry_def] >>
  gvs[] >>
  drule_all counted_invoke_intret >> strip_tac >>
  drule_all step_inst_invoke_OK_control >> strip_tac >>
  `gas_path_edge ctx func t n
     (OK (u with vs_inst_idx := SUC t.vs_inst_idx))` by
    (simp[gas_path_edge_def] >> qexists_tac `fuel` >>
     simp[is_terminator_def]) >>
  `gas_path ctx func (u with vs_inst_idx := SUC t.vs_inst_idx) 0
     (OK (u with vs_inst_idx := SUC t.vs_inst_idx))` by
    (irule (cj 1 gas_path_rules) >> simp[]) >>
  metis_tac[gas_path_rules, arithmeticTheory.ADD_0]
QED

Theorem invoke_intret_data_section:
  gas_invoke_entry (ctx,func) t callee entered /\
  gas_path ctx callee entered n (IntRet ir cs) ==>
  cs.vs_data_section = t.vs_data_section
Proof
  rw[gas_invoke_entry_def] >>
  `?fuel. run_blocks fuel ctx callee setup = IntRet ir cs /\
          gas_count_blocks fuel ctx callee setup = n` by
    (irule counted_path_exit_run_blocks >> simp[exit_result_def] >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  drule_all setup_run_intret_data_section >> simp[]
QED
