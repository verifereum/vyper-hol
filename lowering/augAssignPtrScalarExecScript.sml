Theory augAssignPtrScalarExec
Ancestors augAssignPtrScalarCertificate venomExecSemantics venomState
  venomInst stateFrame list pred_set

Theorem scalar_pure1_result:
  (exec_pure1 f i s = OK u ==> ?v w. u = update_var v w s) /\
  exec_pure1 f i s <> Halt t
Proof
  simp[exec_pure1_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem scalar_pure2_result:
  (exec_pure2 f i s = OK u ==> ?v w. u = update_var v w s) /\
  exec_pure2 f i s <> Halt t
Proof
  simp[exec_pure2_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem scalar_exec_result:
  scalar_shape i ==>
  (step_inst_base i s = OK u ==> u = s \/ ?v w. u = update_var v w s) /\
  step_inst_base i s <> Halt t
Proof
  simp[scalar_shape_def, scalar_binary_def, scalar_unary_def,
       LENGTH_EQ_NUM_compute] >> strip_tac >>
  fs[step_inst_base_opcode_eqs] >>
  simp[exec_pure1_def, exec_pure2_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem scalar_exec_state_frame:
  scalar_shape i /\ step_inst_base i s = OK u ==>
  state_frame u = state_frame s
Proof
  strip_tac >> drule_all (cj 1 scalar_exec_result) >>
  strip_tac >> gvs[] >> simp[]
QED

Theorem scalar_step_shape:
  scalar_shape i ==>
  (!u. step_inst_base i s = OK u ==>
    u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp /\
    u.vs_requests = s.vs_requests) /\
  (!u. step_inst_base i s <> Halt u)
Proof
  strip_tac >> reverse conj_tac
  >- metis_tac[scalar_exec_result] >>
  rpt strip_tac >> drule_all (cj 1 scalar_exec_result) >>
  strip_tac >> gvs[update_var_def]
QED
