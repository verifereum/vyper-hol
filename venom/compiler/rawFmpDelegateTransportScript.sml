Theory rawFmpDelegateTransport
Ancestors
  concretizeLayoutDelegate deadStoreElimDelegateCallSteps
  readonlyInvokeCopyFwdStepsExternalErrors venomCallOracleProps
  venomExecSemantics venomState venomCallOracleDefs instIdxIndep list

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
  Cases_on `?out. inst.inst_outputs = [out]`
  >- ( `?post. exec_delegatecall inst s gas addr off sz ro rs = OK post` by
         metis_tac[dse_exec_delegatecall_results, ricf_delegatecall_error_iff] >>
       `?post'. exec_delegatecall inst
          (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>)
          gas addr off sz ro rs = OK post'` by
         metis_tac[dse_exec_delegatecall_results, ricf_delegatecall_error_iff] >>
       simp[exec_result_map_def] >>
       qpat_assum `exec_delegatecall inst s _ _ _ _ _ _ = OK _`
         (mp_then Any strip_assume_tac delegate_success_envelope) >>
       qpat_assum `exec_delegatecall inst (_ with vs_fmp := _) _ _ _ _ _ _ = OK _`
         (mp_then Any strip_assume_tac delegate_success_envelope) >>
       gvs[Excl "consume_call_outcome_eq"] >>
       rev_drule_at (Pat `consume_call_outcome _ _ _ _ = _`)
         consume_call_outcome_state_transport >>
       disch_then (qspecl_then
         [`s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>`,
          `w2n ro`] mp_tac) >>
       simp[Excl "consume_call_outcome_eq"] >> strip_tac >>
       gvs[venom_call_request_def, read_memory_def,
           write_memory_with_expansion_def, update_var_def,
           venom_state_component_equality, Excl "consume_call_outcome_eq"]) >>
  `exec_delegatecall inst s gas addr off sz ro rs =
     Error "delegatecall requires single output"` by
    metis_tac[ricf_delegatecall_error_iff] >>
  `exec_delegatecall inst
      (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>)
      gas addr off sz ro rs = Error "delegatecall requires single output"` by
    metis_tac[ricf_delegatecall_error_iff] >>
  simp[exec_result_map_def]
QED
