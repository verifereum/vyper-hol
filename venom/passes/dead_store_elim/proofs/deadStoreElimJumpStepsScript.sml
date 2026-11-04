Theory deadStoreElimJumpSteps
Ancestors
  deadStoreElimLocal deadStoreElimSafety deadStoreElimDefs
  venomExecSemantics venomState venomEffects venomInst list

Theorem dse_local_agrees_jump_to:
  dse_local_agrees sp P s t ==>
  dse_local_agrees sp P (jump_to lbl s) (jump_to lbl t)
Proof
  strip_tac >>
  `s.vs_current_bb = t.vs_current_bb` by
    fs[dse_local_agrees_def, dse_operational_agrees_def] >>
  simp[jump_to_def, dse_local_agrees_prev_bb,
       dse_local_agrees_current_bb, dse_local_agrees_inst_idx]
QED

Theorem dse_jump_retained:
  inst.inst_opcode IN {JMP; JNZ; DJMP} /\
  sp IN {AddrSp_Memory; AddrSp_Storage; AddrSp_Transient} ==>
  dse_inst ids sp inst = inst
Proof
  simp[] >> strip_tac >>
  simp[dse_inst_def, is_memory_def_opcode_def, write_effects_def,
       empty_effects_def, effects_in_space_def]
QED

Theorem dse_jump_local_step:
  inst.inst_opcode IN {JMP; JNZ; DJMP} /\
  dse_local_agrees sp P s t /\ step_inst fuel ctx inst s = OK s1 ==>
  ?t1. step_inst fuel ctx inst t = OK t1 /\
       dse_local_agrees sp P s1 t1 /\
       s1.vs_allocas = s.vs_allocas /\ t1.vs_allocas = t.vs_allocas
Proof
  strip_tac >>
  `!op. eval_operand op s = eval_operand op t` by
    (fs[dse_local_agrees_def] >>
     metis_tac[dse_safety_agrees_eval_operand]) >>
  fs[] >>
  gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  simp[dse_local_agrees_jump_to, jump_to_def]
QED

Theorem dse_jump_result_cases:
  inst.inst_opcode IN {JMP; JNZ; DJMP} ==>
  (?s1. step_inst fuel ctx inst s = OK s1) \/
  (?e. step_inst fuel ctx inst s = Error e)
Proof
  simp[] >> strip_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  namedCases_on `inst.inst_operands` ["", "operand operands"] >> simp[]
  >- (Cases_on `operand` >> simp[] >> Cases_on `operands` >> simp[])
  >- (namedCases_on `operands` ["", "second rest"] >> simp[] >>
      Cases_on `second` >> simp[] >>
      namedCases_on `rest` ["", "third tailops"] >> simp[] >>
      Cases_on `third` >> simp[] >> Cases_on `tailops` >> simp[] >>
      Cases_on `eval_operand operand s` >> simp[] >> IF_CASES_TAC >> simp[]) >>
  Cases_on `eval_operand operand s` >> simp[] >>
  Cases_on `extract_labels operands` >> simp[] >> IF_CASES_TAC >> simp[]
QED
