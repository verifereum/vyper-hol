Theory makeSsaCurrentDemandRuntime
Ancestors
  makeSsaCurrentDemand makeSsaCurrentExecRuntime makeSsaCurrentReturnRuntime
  venomWf venomInst venomExecSemantics venomExecProps list
Libs
  stepInstBaseLib

Theorem current_demand_successor_unwritten:
  lookup_block l fn.fn_blocks = SOME bb /\ i < LENGTH bb.bb_instructions /\
  ~MEM v (EL i bb.bb_instructions).inst_outputs /\
  current_demand fn v l (SUC i) ==>
  current_demand fn v l i
Proof
  strip_tac >> irule (cj 3 current_demand_rules) >>
  simp[inst_defs_def] >> metis_tac[]
QED

Theorem current_demand_step_defined:
  fn_inst_wf fn /\
  lookup_block l fn.fn_blocks = SOME bb /\ i < LENGTH bb.bb_instructions /\
  (!v. current_demand fn v l i ==> IS_SOME (lookup_var v st)) /\
  step_inst fuel C (EL i bb.bb_instructions) st = OK t ==>
  !v. current_demand fn v l (SUC i) ==> IS_SOME (lookup_var v t)
Proof
  strip_tac >>
  `inst_wf (EL i bb.bb_instructions)` by
    metis_tac[fn_inst_wf_def, lookup_block_MEM, EL_MEM] >>
  `(EL i bb.bb_instructions).inst_opcode <> PHI` by
    (strip_tac >>
     fs[step_inst_non_invoke] >> stepInstBaseLib.with_opcode_clause fs) >>
  rpt strip_tac >> Cases_on `MEM v (EL i bb.bb_instructions).inst_outputs`
  >- metis_tac[current_exec_lookup_written] >>
  `current_demand fn v l i` by metis_tac[current_demand_successor_unwritten] >>
  metis_tac[current_exec_lookup_unwritten]
QED

Theorem current_demand_return_defined:
  lookup_block l fn.fn_blocks = SOME bb /\ i < LENGTH bb.bb_instructions /\
  (!v. current_demand fn v l i ==> IS_SOME (lookup_var v st)) /\
  bind_outputs (EL i bb.bb_instructions).inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state st e)) = SOME t ==>
  !v. current_demand fn v l (SUC i) ==> IS_SOME (lookup_var v t)
Proof
  strip_tac >> rpt strip_tac >>
  Cases_on `MEM v (EL i bb.bb_instructions).inst_outputs`
  >- metis_tac[current_return_bind_written] >>
  `current_demand fn v l i` by metis_tac[current_demand_successor_unwritten] >>
  metis_tac[current_return_bind_unwritten]
QED
