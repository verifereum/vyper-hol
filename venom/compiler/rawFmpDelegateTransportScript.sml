Theory rawFmpDelegateTransport
Ancestors
  instIdxIndep venomCallOracleDefs venomExecSemantics venomState list

Theorem exec_delegatecall_fmp_update:
  !inst s p i e gas addr off sz ro rs.
    exec_delegatecall inst
      (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>)
      (gas:bytes32) addr off sz (ro:bytes32) (rs:bytes32) =
    exec_result_map
      (\t. t with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>)
      (exec_delegatecall inst s gas addr off sz ro rs)
Proof
  rpt gen_tac >>
  namedCases_on `inst.inst_outputs` ["", "out outs"]
  >- simp[exec_delegatecall_def, exec_result_map_def] >>
  Cases_on `outs` >>
  simp[exec_delegatecall_def, venom_call_request_def, read_memory_def,
       consume_call_outcome_eq, write_memory_with_expansion_def, update_var_def,
       halt_state_def, set_returndata_def, exec_result_map_def] >>
  Cases_on `s.vs_outcomes = []` >> simp[exec_result_map_def]
QED
