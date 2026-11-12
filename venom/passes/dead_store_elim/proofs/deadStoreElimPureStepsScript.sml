Theory deadStoreElimPureSteps
Ancestors
  deadStoreElimLocal deadStoreElimPending deadStoreElimLiveness
  deadStoreElimDefs basePtrDefs memLocDefs venomExecSemantics
  venomState venomEffects venomInst list

(* Unlike valid_state_rel, this boundary needs only operand agreement;
   it also exposes the common update needed for pending footprints. *)
Theorem exec_pure1_common_update:
  (!op. eval_operand op s = eval_operand op t) /\
  exec_pure1 f inst s = OK s1 ==>
  ?out w. s1 = update_var out w s /\
    exec_pure1 f inst t = OK (update_var out w t)
Proof
  simp[exec_pure1_def] >> strip_tac >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem exec_pure2_common_update:
  (!op. eval_operand op s = eval_operand op t) /\
  exec_pure2 f inst s = OK s1 ==>
  ?out w. s1 = update_var out w s /\
    exec_pure2 f inst t = OK (update_var out w t)
Proof
  simp[exec_pure2_def] >> strip_tac >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem exec_pure3_common_update:
  (!op. eval_operand op s = eval_operand op t) /\
  exec_pure3 f inst s = OK s1 ==>
  ?out w. s1 = update_var out w s /\
    exec_pure3 f inst t = OK (update_var out w t)
Proof
  simp[exec_pure3_def] >> strip_tac >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem exec_pure1_result_cases:
  (?s1. exec_pure1 f inst s = OK s1) \/
  (?e. exec_pure1 f inst s = Error e)
Proof
  simp[exec_pure1_def] >> rpt (CASE_TAC >> simp[])
QED

Theorem exec_pure2_result_cases:
  (?s1. exec_pure2 f inst s = OK s1) \/
  (?e. exec_pure2 f inst s = Error e)
Proof
  namedCases_on `inst.inst_operands` ["", "op1 ops"]
  >- simp[exec_pure2_def] >>
  namedCases_on `ops` ["", "op2 rest"]
  >- simp[exec_pure2_def] >>
  Cases_on `rest`
  >- (Cases_on `eval_operand op1 s` >> simp[exec_pure2_def] >>
      Cases_on `eval_operand op2 s` >> simp[] >>
      namedCases_on `inst.inst_outputs` ["", "out outs"]
      >- simp[] >> Cases_on `outs` >> simp[]) >>
  simp[exec_pure2_def]
QED

Theorem exec_pure3_result_cases:
  (?s1. exec_pure3 f inst s = OK s1) \/
  (?e. exec_pure3 f inst s = Error e)
Proof
  namedCases_on `inst.inst_operands` ["", "op1 ops"]
  >- simp[exec_pure3_def] >>
  namedCases_on `ops` ["", "op2 rest"]
  >- simp[exec_pure3_def] >>
  namedCases_on `rest` ["", "op3 tailops"]
  >- simp[exec_pure3_def] >>
  Cases_on `tailops`
  >- (Cases_on `eval_operand op1 s` >> simp[exec_pure3_def] >>
      Cases_on `eval_operand op2 s` >> simp[] >>
      Cases_on `eval_operand op3 s` >> simp[] >>
      namedCases_on `inst.inst_outputs` ["", "out outs"]
      >- simp[] >> Cases_on `outs` >> simp[]) >>
  simp[exec_pure3_def]
QED

Definition dse_pure_opcode_def:
  dse_pure_opcode opc <=>
    opc IN {ADD; SUB; MUL; Div; Mod; SDIV; SMOD; Exp;
      ADDMOD; MULMOD; EQ; LT; GT; SLT; SGT; ISZERO;
      AND; OR; XOR; NOT; SHL; SHR; SAR; SIGNEXTEND; BYTE}
End

Theorem dse_pure_common_update:
  dse_pure_opcode inst.inst_opcode /\
  (!op. eval_operand op s = eval_operand op t) /\
  step_inst fuel ctx inst s = OK s1 ==>
  ?out w. s1 = update_var out w s /\
    step_inst fuel ctx inst t = OK (update_var out w t)
Proof
  simp[dse_pure_opcode_def] >> strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  metis_tac[exec_pure1_common_update, exec_pure2_common_update,
            exec_pure3_common_update]
QED

Theorem dse_pure_result_cases:
  dse_pure_opcode inst.inst_opcode ==>
  (?s1. step_inst fuel ctx inst s = OK s1) \/
  (?e. step_inst fuel ctx inst s = Error e)
Proof
  simp[dse_pure_opcode_def] >> strip_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs,
       exec_pure1_result_cases, exec_pure2_result_cases,
       exec_pure3_result_cases]
QED

Theorem dse_pure_write_location:
  dse_pure_opcode inst.inst_opcode ==>
  bp_get_write_location bp inst sp = ml_empty
Proof
  simp[dse_pure_opcode_def] >> strip_tac >> Cases_on `sp` >>
  gvs[bp_get_write_location_def, is_raw_fmp_opcode_def, write_effects_def,
      empty_effects_def]
QED

Theorem dse_pure_no_clobber:
  dse_pure_opcode inst.inst_opcode /\
  loc.ml_size = SOME n /\ 0 < n ==>
  ~dse_inst_clobbers bp sp loc inst
Proof
  strip_tac >> drule dse_pure_write_location >>
  disch_then (qspec_then `sp` assume_tac) >>
  simp[dse_inst_clobbers_def, ml_empty_def, completely_contains_def]
QED

Theorem dse_pure_pending_step:
  dse_pure_opcode inst.inst_opcode /\
  dse_pending_at cfg bp sp fn bb idx P s /\
  EL idx bb.bb_instructions = inst ==>
  dse_pending_at cfg bp sp fn bb (SUC idx) P (update_var out w s)
Proof
  strip_tac >> irule dse_pending_at_allocas_extend >>
  qexists_tac `s` >> simp[update_var_def] >>
  irule dse_pending_at_step >> simp[] >>
  rpt gen_tac >> disch_tac >>
  drule_all dse_pending_at_member >> strip_tac >>
  irule dse_pure_no_clobber >> metis_tac[]
QED

Theorem dse_local_agrees_pure_step:
  dse_pure_opcode inst.inst_opcode /\
  dse_local_agrees sp P s t /\
  dse_pending_at cfg bp sp fn bb s.vs_inst_idx P s /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  step_inst fuel ctx inst s = OK s1 ==>
  ?t1. step_inst fuel ctx inst t = OK t1 /\
    dse_local_agrees sp P (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx) /\
    dse_pending_at cfg bp sp fn bb (SUC s.vs_inst_idx) P s1
Proof
  strip_tac >>
  `EL s.vs_inst_idx bb.bb_instructions = inst` by
    fs[get_instruction_def, AllCaseEqs()] >>
  `!op. eval_operand op s = eval_operand op t` by
    (fs[dse_local_agrees_def] >>
     metis_tac[deadStoreElimSafetyTheory.dse_safety_agrees_eval_operand]) >>
  drule_all dse_pure_common_update >> strip_tac >>
  qexists_tac `update_var out w t` >> simp[] >>
  `s.vs_inst_idx = t.vs_inst_idx` by
    fs[dse_local_agrees_def, dse_operational_agrees_def] >>
  conj_tac
  >- (gvs[] >> irule dse_local_agrees_inst_idx >>
      irule dse_local_agrees_update_var >> simp[]) >>
  gvs[] >> irule dse_pure_pending_step >> simp[] >> metis_tac[]
QED
