Theory rawFmpExternalCallTransport
Ancestors
  instIdxIndep venomCallOracleDefs venomExecSemantics venomState list

Theorem exec_ext_call_fmp_update:
  !inst s p i e gas addr value off sz ro rs static.
    exec_ext_call inst
      (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>)
      gas addr value off sz ro rs static =
    exec_result_map
      (\s. s with <|vs_fmp := p; vs_initial_fmp := i;
                     vs_call_entry_fmp := e|>)
      (exec_ext_call inst s gas addr value off sz ro rs static)
Proof
  rpt gen_tac >>
  namedCases_on `inst.inst_outputs` ["", "out outs"]
  >- simp[exec_ext_call_def, exec_result_map_def] >>
  Cases_on `outs` >>
  simp[exec_ext_call_def, venom_call_request_def, read_memory_def,
       consume_call_outcome_eq, write_memory_with_expansion_def, update_var_def,
       halt_state_def, set_returndata_def, exec_result_map_def] >>
  Cases_on `s.vs_outcomes = []` >> simp[exec_result_map_def]
QED
