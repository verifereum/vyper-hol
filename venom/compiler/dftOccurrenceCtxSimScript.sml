Theory dftOccurrenceCtxSim
Ancestors
  dftOccurrenceTerminal dftTerminalResult o1PassContract dftOpenAdequacy
  dftOccurrenceReplay dftOpenMachine venomExecSemantics passSimulationDefs


Theorem dft_occ_terminal_transport_ctx_sim:
  C.ctx_entry = SOME name /\ lookup_function name C.ctx_functions = SOME entry /\
  fn_entry_label entry = SOME lbl /\
  C'.ctx_entry = SOME name' /\ lookup_function name' C'.ctx_functions = SOME entry' /\
  fn_entry_label entry' = SOME lbl' /\
  (!fuel. terminates (run_context fuel C s) ==>
    (?t. run_context fuel C s = Halt t) \/
    (?z t. run_context fuel C s = Abort z t)) /\
  dft_sparse_oracle a s.vs_gas_readings /\
  dft_sparse_oracle a' s'.vs_gas_readings /\
  (!j. dft_occ_prefix_compatible w a C (dft_occ_start entry lbl s) j) /\
  (!k. dft_occ_prefix_compatible w' a' C' (dft_occ_start entry' lbl' s') k) /\
  (!j n rr. ((?t. rr = Halt t) \/ (?z t. rr = Abort z t)) /\
    (FUNPOW (dft_occ_oracle_next w C) j (dft_occ_start entry lbl s)).dft_occ_core =
      DftOpen (DftDone rr) [] n ==>
    ?k m rr'. (FUNPOW (dft_occ_oracle_next w' C') k
      (dft_occ_start entry' lbl' s')).dft_occ_core = DftOpen (DftDone rr') [] m /\
      (rr' = rr \/ (?z t u. rr = Abort z t /\ rr' = Abort z u))) ==>
  ctx_sim D C C' s s'
Proof
  strip_tac >> rewrite_tac[ctx_sim_def] >> rpt strip_tac >>
  `(?t. run_context fuel C s = Halt t) \/
   (?z t. run_context fuel C s = Abort z t)` by
    metis_tac[] >>
  `?j n rr. ((?t. rr = Halt t) \/ (?z t. rr = Abort z t)) /\
    (FUNPOW (dft_occ_oracle_next w C) j (dft_occ_start entry lbl s)).dft_occ_core =
      DftOpen (DftDone rr) [] n /\
    run_context fuel C s = dft_open_materialize_result s.vs_gas_readings n rr` by
    (irule dft_occ_terminal_extract >> metis_tac[]) >>
  qpat_x_assum `!j n rr. _`
    (qspecl_then [`j`, `n`, `rr`] mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  `(?t. rr' = Halt t) \/ (?z t. rr' = Abort z t)` by metis_tac[] >>
  `?fuel'. run_context fuel' C' s' =
    dft_open_materialize_result s'.vs_gas_readings m rr'` by
    (irule dft_occ_terminal_realize >> metis_tac[]) >>
  qexists_tac `fuel'` >> simp[] >>
  irule dft_materialized_mixed_terminal_dead_result_rel >> metis_tac[]
QED
