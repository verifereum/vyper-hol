Theory rawFmpCreateTransport
Ancestors
  lowerDloadPtrCreateInterfaces readonlyInvokeCopyFwdStepsExternalErrors
  instIdxIndep venomExecSemantics venomCallOracleDefs venomState

Theorem exec_create_fmp_update:
  !inst s value off sz salt p i e.
    exec_create inst
      (s with <|vs_fmp := p; vs_initial_fmp := i;
                vs_call_entry_fmp := e|>) value off sz salt =
    exec_result_map
      (\t. t with <|vs_fmp := p; vs_initial_fmp := i;
                     vs_call_entry_fmp := e|>)
      (exec_create inst s value off sz salt)
Proof
  rpt gen_tac >> Cases_on `exec_create inst s value off sz salt` >>
  gvs[exec_result_map_def, exec_create_not_Halt, exec_create_not_IntRet]
  >- (gvs[dload_exec_create_success_iff] >>
      simp[dload_exec_create_success_iff] >>
      gvs[consume_create_outcome_eq, venom_create_request_def,
          read_memory_def, update_var_def])
  >- gvs[exec_create_abort_iff, halt_state_def, set_returndata_def]
  >> gvs[ricf_create_error_iff]
QED
