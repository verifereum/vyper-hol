Theory deadStoreElimFrameReadSteps
Ancestors
  deadStoreElimLocal deadStoreElimPending deadStoreElimLiveness
  deadStoreElimSafety deadStoreElimEquiv deadStoreElimDefs
  basePtrDefs memLocDefs venomExecSemantics venomState venomEffects venomInst list
Libs
  deadStoreElimFrameLib

val _ = augment_srw_ss [deadStoreElimFrameLib.frame_ss];

Theorem exec_read0_common_update:
  f s = f t /\ exec_read0 f inst s = OK s1 ==>
  ?out w. s1 = update_var out w s /\
    exec_read0 f inst t = OK (update_var out w t)
Proof
  simp[exec_read0_def] >> strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem exec_read1_common_update:
  (!op. eval_operand op s = eval_operand op t) /\
  (!v. f v s = f v t) /\ exec_read1 f inst s = OK s1 ==>
  ?out w. s1 = update_var out w s /\
    exec_read1 f inst t = OK (update_var out w t)
Proof
  simp[exec_read1_def] >> strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem exec_read0_result_cases:
  (?s1. exec_read0 f inst s = OK s1) \/
  (?e. exec_read0 f inst s = Error e)
Proof
  simp[exec_read0_def] >> rpt (CASE_TAC >> simp[])
QED

Theorem exec_read1_result_cases:
  (?s1. exec_read1 f inst s = OK s1) \/
  (?e. exec_read1 f inst s = Error e)
Proof
  simp[exec_read1_def] >> rpt (CASE_TAC >> simp[])
QED

Definition dse_frame_read_opcode_def:
  dse_frame_read_opcode opc <=>
    opc IN {CALLER; ADDRESS; CALLVALUE; GAS; ORIGIN; GASPRICE; CHAINID;
      COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE; BLOBBASEFEE;
      BLOCKHASH; BLOBHASH; CALLDATASIZE; CALLDATALOAD; RETURNDATASIZE; CODESIZE; DLOAD}
End

Theorem dse_local_agrees_frame:
  dse_local_agrees sp P s t ==>
  s.vs_call_ctx = t.vs_call_ctx /\ s.vs_tx_ctx = t.vs_tx_ctx /\
  s.vs_block_ctx = t.vs_block_ctx /\ s.vs_returndata = t.vs_returndata /\
  s.vs_code = t.vs_code /\ s.vs_data_section = t.vs_data_section
Proof
  simp[dse_local_agrees_def, dse_pending_space_def, dse_equiv_def]
QED

Theorem dse_frame_read_common_update:
  dse_frame_read_opcode inst.inst_opcode /\ dse_local_agrees sp P s t /\
  step_inst fuel ctx inst s = OK s1 ==>
  ?out w. s1 = update_var out w s /\
    step_inst fuel ctx inst t = OK (update_var out w t)
Proof
  strip_tac >>
  `!op. eval_operand op s = eval_operand op t` by
    (fs[dse_local_agrees_def] >> metis_tac[dse_safety_agrees_eval_operand]) >>
  drule dse_local_agrees_frame >> strip_tac >>
  fs[dse_frame_read_opcode_def] >>
  gvs[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  FIRST [irule exec_read0_common_update, irule exec_read1_common_update] >>
  simp[] >> metis_tac[]
QED

Theorem dse_frame_read_result_cases:
  dse_frame_read_opcode inst.inst_opcode ==>
  (?s1. step_inst fuel ctx inst s = OK s1) \/
  (?e. step_inst fuel ctx inst s = Error e)
Proof
  simp[dse_frame_read_opcode_def] >> strip_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs,
       exec_read0_result_cases, exec_read1_result_cases]
QED

(* Failed interface attempt, E0038: DLOAD has a nonempty static Memory
   write footprint. Preserved for diagnosis; this is not an exported lemma.
Theorem dse_frame_read_write_location:
  dse_frame_read_opcode inst.inst_opcode ==>
  bp_get_write_location bp inst sp = ml_empty
Proof
  simp[dse_frame_read_opcode_def] >> strip_tac >> Cases_on `sp` >>
  gvs[bp_get_write_location_def, is_raw_fmp_opcode_def, write_effects_def,
      empty_effects_def]
QED
*)
