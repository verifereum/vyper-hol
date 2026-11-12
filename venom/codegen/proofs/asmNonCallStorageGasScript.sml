(* Storage instruction charges, before exception handling. *)
Theory asmNonCallStorageGas
Ancestors
  asmFrameRel asmRunBounded frameStep asmFrameLocalStep asmCallGasArithmetic
  vfmExecution vfmExecutionProp vfmConstants vfmOperation

Theorem step_tload_gas_budget:
  es.contexts = (c,rb)::rest /\ wf_context c /\
  100 <= B /\ B <= c.msgParams.gasLimit - c.gasUsed /\
  step_sload T es = (r,s') ==>
  r <> INR (SOME OutOfGas) /\
  frame_gas_left es <= frame_gas_left s' + B
Proof
  strip_tac >>
  gvs[step_sload_def, pop_stack_def, consume_gas_def,
      push_stack_def, get_callee_def, get_tStorage_def,
      bind_def, ignore_bind_def, get_current_context_def, return_def,
      set_current_context_def, assert_def, fail_def, LET_THM,
      warm_access_cost_def, wf_context_def, AllCaseEqs()] >>
  gvs[frame_gas_left_def] >> decide_tac
QED

Theorem step_tstore_gas_budget:
  es.contexts = (c,rb)::rest /\ wf_context c /\
  100 <= B /\ B <= c.msgParams.gasLimit - c.gasUsed /\
  step_sstore T es = (r,s') ==>
  r <> INR (SOME OutOfGas) /\
  frame_gas_left es <= frame_gas_left s' + B
Proof
  strip_tac >>
  gvs[step_sstore_def, pop_stack_def, consume_gas_def,
      get_callee_def, get_tStorage_def, get_static_def, assert_not_static_def,
      write_transient_storage_def, set_tStorage_def,
      bind_def, ignore_bind_def, get_current_context_def, return_def,
      set_current_context_def, assert_def, fail_def, LET_THM,
      warm_access_cost_def, wf_context_def, AllCaseEqs()] >>
  gvs[frame_gas_left_def] >> decide_tac
QED

Theorem step_sload_gas_budget:
  es.contexts = (c,rb)::rest /\ wf_context c /\
  2100 <= B /\ B <= c.msgParams.gasLimit - c.gasUsed /\
  step_sload F es = (r,s') ==>
  r <> INR (SOME OutOfGas) /\
  frame_gas_left es <= frame_gas_left s' + B
Proof
  strip_tac >>
  gvs[step_sload_def, pop_stack_def, consume_gas_def,
      push_stack_def, get_callee_def, get_accounts_def,
      access_slot_def, domain_check_def, set_domain_def,
      bind_def, ignore_bind_def, get_current_context_def, return_def,
      set_current_context_def, assert_def, fail_def, LET_THM,
      warm_access_cost_def, cold_sload_cost_def, wf_context_def,
      AllCaseEqs()] >>
  rpt IF_CASES_TAC >>
  gvs[frame_gas_left_def, bind_def, ignore_bind_def, return_def,
      assert_def, fail_def, set_current_context_def, push_stack_def,
      get_current_context_def] >> decide_tac
QED

