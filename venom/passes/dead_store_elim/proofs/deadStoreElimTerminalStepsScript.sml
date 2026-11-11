Theory deadStoreElimTerminalSteps
Ancestors
  deadStoreElimLocal deadStoreElimPending deadStoreElimSafety
  deadStoreElimDefs deadStoreElimTerminalEquiv
  venomExecSemantics venomState venomEffects venomInst list

Theorem dse_local_agrees_eval_operands:
  !ops. dse_local_agrees sp P s t ==>
  eval_operands ops s = eval_operands ops t
Proof
  Induct >- simp[eval_operands_def] >> rpt strip_tac >>
  `eval_operand h s = eval_operand h t` by
    (fs[dse_local_agrees_def] >>
     metis_tac[dse_safety_agrees_eval_operand]) >>
  simp[eval_operands_def]
QED

Theorem dse_terminal_retained:
  inst.inst_opcode IN {STOP; SINK; RET; RETFMP} /\
  sp IN {AddrSp_Memory; AddrSp_Storage; AddrSp_Transient} ==>
  dse_inst ids sp inst = inst
Proof
  simp[] >> strip_tac >>
  simp[dse_inst_def, is_memory_def_opcode_def, write_effects_def,
       empty_effects_def, effects_in_space_def]
QED

Theorem dse_stop_halt_step:
  inst.inst_opcode IN {STOP; SINK} /\ dse_local_agrees sp P s t /\
  step_inst fuel ctx inst s = Halt s1 ==>
  ?t1. step_inst fuel ctx inst t = Halt t1 /\ dse_equiv sp s1 t1
Proof
  strip_tac >>
  `dse_equiv sp s t` by
    metis_tac[dse_local_agrees_def, dse_pending_space_equiv] >>
  fs[] >> gvs[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  rewrite_tac[GSYM set_returndata_def] >>
  simp[dse_equiv_halt_state, dse_equiv_set_returndata]
QED

Theorem dse_stop_result_cases:
  inst.inst_opcode IN {STOP; SINK} ==>
  ?s1. step_inst fuel ctx inst s = Halt s1
Proof
  simp[] >> strip_tac >> simp[step_inst_non_invoke, step_inst_base_opcode_eqs]
QED

Theorem dse_ret_intret_step:
  inst.inst_opcode IN {RET; RETFMP} /\ dse_local_agrees sp P s t /\
  step_inst fuel ctx inst s = IntRet rv s1 ==>
  ?t1. step_inst fuel ctx inst t = IntRet rv t1 /\ dse_equiv sp s1 t1
Proof
  strip_tac >>
  `!ops. eval_operands ops s = eval_operands ops t` by
    metis_tac[dse_local_agrees_eval_operands] >>
  `s.vs_fmp = t.vs_fmp` by
    fs[dse_local_agrees_def, dse_operational_agrees_def] >>
  `dse_equiv sp s t` by
    metis_tac[dse_local_agrees_def, dse_pending_space_equiv] >>
  fs[] >> gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()]
QED

Theorem dse_ret_result_cases:
  inst.inst_opcode IN {RET; RETFMP} ==>
  (?rv s1. step_inst fuel ctx inst s = IntRet rv s1) \/
  (?e. step_inst fuel ctx inst s = Error e)
Proof
  simp[] >> strip_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  namedCases_on `eval_operands inst.inst_operands s` ["", "values"] >> simp[] >>
  Cases_on `values` >> simp[]
QED
