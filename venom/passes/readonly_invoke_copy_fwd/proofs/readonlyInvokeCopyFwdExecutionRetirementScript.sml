(* Only cross certificates are weakened. Histories, maps and support remain. *)
Theory readonlyInvokeCopyFwdExecutionRetirement
Ancestors
  readonlyInvokeCopyFwdExecution readonlyInvokeCopyFwdHeterogeneousLedger
  readonlyInvokeCopyFwdProtectionRetirement readonlyInvokeCopyFwdHistoryPhase
  readonlyInvokeCopyFwdRel internalReturnCopyFwdSim list pred_set

Theorem ricf_phase_certificate_subset[local]:
  set next SUBSET set certificates ==>
  ricf_phase_ranges depth next SUBSET ricf_phase_ranges depth certificates
Proof
  simp[ricf_phase_ranges_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem ricf_execution_certificates_subset:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H certificates E sites maps targets rt /\
  set next SUBSET set certificates ==>
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H next E sites maps targets rt
Proof
  simp[ricf_execution_invariant_def] >> strip_tac >>
  `ricf_heterogeneous_source_ledger vs C stk PG G tn fn inst s
     n a U B HP H next` by
    (fs[ricf_heterogeneous_source_ledger_def, EVERY_MEM, SUBSET_DEF] >> metis_tac[]) >>
  `ircf_cross rt (ricf_phase_ranges 0 next) s t` by
    metis_tac[ircf_cross_subset, ricf_phase_certificate_subset] >>
  `ricf_cert_crosses rt (ricf_phase_stack_ranges stk next) stk s t` by
    (irule ricf_cert_crosses_subset >>
     qexists_tac `ricf_phase_stack_ranges stk certificates` >>
     simp[ricf_phase_stack_ranges_def, ricf_phase_certificate_subset]) >>
  simp[]
QED
