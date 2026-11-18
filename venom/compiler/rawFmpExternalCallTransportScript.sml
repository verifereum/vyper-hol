Theory rawFmpExternalCallTransport
Ancestors
  instIdxIndep lowerDloadExternalBackward venomCallOracleProps
  deadStoreElimCallSteps readonlyInvokeCopyFwdStepsExternalErrors
  venomCallOracleDefs venomExecSemantics venomState list

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
  qmatch_goalsub_abbrev_tac `exec_ext_call inst us` >>
  Cases_on `?t. exec_ext_call inst s gas addr value off sz ro rs static = OK t`
  >- (pop_assum strip_assume_tac >>
      `?u. exec_ext_call inst us gas addr value off sz ro rs static = OK u` by
        (qspecl_then [`us`, `static`] mp_tac
           (Q.GENL [`s`, `is_static`] dse_exec_ext_call_results) >>
         disch_then DISJ_CASES_TAC >- metis_tac[] >>
         pop_assum strip_assume_tac >>
         metis_tac[ricf_ext_call_error_iff]) >>
      pop_assum strip_assume_tac >>
      qpat_assum `exec_ext_call _ s _ _ _ _ _ _ _ _ = OK _`
        (mp_then (Pat `exec_ext_call _ _ _ _ _ _ _ _ _ _ = OK _`)
          mp_tac ld_exec_ext_call_backward) >>
      disch_then (qspecl_then [`s`, `0w:bytes32`, `off`] mp_tac) >>
      simp[Excl "consume_call_outcome_eq"] >> strip_tac >>
      qpat_x_assum `exec_ext_call _ _ _ _ _ _ _ (0w:bytes32) _ _ = _` kall_tac >>
      qpat_x_assum `consume_call_outcome _ 0 _ _ = _` kall_tac >>
      qpat_assum `exec_ext_call _ us _ _ _ _ _ _ _ _ = OK _`
        (mp_then (Pat `exec_ext_call _ _ _ _ _ _ _ _ _ _ = OK _`)
          mp_tac ld_exec_ext_call_backward) >>
      disch_then (qspecl_then [`us`, `0w:bytes32`, `off`] mp_tac) >>
      simp[Excl "consume_call_outcome_eq"] >> strip_tac >>
      qpat_x_assum `exec_ext_call _ _ _ _ _ _ _ (0w:bytes32) _ _ = _` kall_tac >>
      qpat_x_assum `consume_call_outcome _ 0 _ _ = _` kall_tac >>
      qpat_assum `consume_call_outcome _ _ _ s = _`
        (mp_then (Pat `consume_call_outcome _ _ _ _ = _`)
          mp_tac consume_call_outcome_state_transport) >>
      disch_then (qspecl_then [`us`, `w2n ro`] mp_tac) >>
      simp[Abbr `us`, Excl "consume_call_outcome_eq"] >> strip_tac >>
      gvs[venom_call_request_def, read_memory_def,
          write_memory_with_expansion_def, update_var_def,
          exec_result_map_def, Excl "consume_call_outcome_eq"] >>
      gvs[venom_state_component_equality]) >>
  `?err. exec_ext_call inst s gas addr value off sz ro rs static = Error err` by
    metis_tac[dse_exec_ext_call_results] >>
  `exec_ext_call inst us gas addr value off sz ro rs static = Error err` by
    (qpat_x_assum `exec_ext_call _ _ _ _ _ _ _ _ _ _ = Error _` mp_tac >>
     simp[ricf_ext_call_error_iff]) >>
  simp[exec_result_map_def]
QED
