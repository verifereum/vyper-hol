Theory deadStoreElimContinuation
Ancestors
  deadStoreElimLocal deadStoreElimPending deadStoreElimStructure
  deadStoreElimCallSteps deadStoreElimDelegateCallSteps
  deadStoreElimDefs venomExecSemantics venomInst venomState

Theorem dse_pending_at_inst_idx:
  dse_pending_at cfg bp sp fn bb idx P s ==>
  dse_pending_at cfg bp sp fn bb idx P (s with vs_inst_idx := next)
Proof
  strip_tac >> irule dse_pending_at_allocas_extend >>
  qexists_tac `s` >> simp[]
QED

Theorem dse_indexed_continuation:
  (?t1 P1. step_inst fuel ctx transformed t = OK t1 /\
     dse_local_agrees sp P1 s1 t1 /\
     dse_pending_at cfg bp sp fn bb (SUC idx) P1 s1) ==>
  ?t1 P1. step_inst fuel ctx transformed t = OK t1 /\
    dse_local_agrees sp P1 (s1 with vs_inst_idx := SUC idx)
      (t1 with vs_inst_idx := SUC idx) /\
    dse_pending_at cfg bp sp fn bb (SUC idx) P1
      (s1 with vs_inst_idx := SUC idx)
Proof
  strip_tac >> qexistsl_tac [`t1`, `P1`] >>
  simp[dse_local_agrees_inst_idx, dse_pending_at_inst_idx]
QED

Theorem dse_nonempty_outputs_retained:
  wf_function fn /\ all_dead_stores ids cfg aliases bp sp fn /\
  MEM inst (fn_insts fn) /\ inst.inst_outputs <> [] ==>
  dse_inst ids sp inst = inst
Proof
  strip_tac >> Cases_on `inst.inst_id IN ids`
  >- (drule_all all_dead_stores_occurrence >> simp[]) >>
  simp[dse_inst_def]
QED

Theorem dse_external_call_ok_outputs:
  inst.inst_opcode IN {CALL; STATICCALL; DELEGATECALL} /\
  step_inst fuel ctx inst s = OK s1 ==> inst.inst_outputs <> []
Proof
  strip_tac >> Cases_on `inst.inst_outputs = []` >> simp[] >>
  fs[] >> gvs[step_inst_non_invoke, step_inst_base_opcode_eqs,
    AllCaseEqs(), exec_ext_call_def, exec_delegatecall_def,
    Excl "consume_call_outcome_eq"] >>
  pairarg_tac >> gvs[Excl "consume_call_outcome_eq"]
QED

Theorem dse_external_call_retained:
  wf_function fn /\ all_dead_stores ids cfg aliases bp sp fn /\
  MEM inst (fn_insts fn) /\
  inst.inst_opcode IN {CALL; STATICCALL; DELEGATECALL} /\
  step_inst fuel ctx inst s = OK s1 ==>
  dse_inst ids sp inst = inst
Proof
  strip_tac >> drule_all dse_external_call_ok_outputs >> strip_tac >>
  irule dse_nonempty_outputs_retained >> metis_tac[]
QED
