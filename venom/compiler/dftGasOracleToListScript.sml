(*
 * An oracle run (dftGasOracleDefs) whose oracle reads nonzero at only
 * finitely many events is a run that reads GAS from a list: the oracle's
 * words in the order the run meets their events, up to the last nonzero
 * one it meets (an exhausted list reads 0w).
 *
 * TOP-LEVEL:
 *   gas_oracle_to_list - the reading list of an oracle run
 *)
Theory dftGasOracleToList
Ancestors
  dftGasOracleDefs contextRawReachable o1PassContract venomExecSemantics
  dftGasToListCompact dftGasToListReplay dftGasToListReachWitness
  dftGasToListVisitReplay

Theorem gas_oracle_to_list_traced:
  EVERY wf_function ctx.ctx_functions /\ FINITE {e | orc e <> 0w} ==>
  ?W. (?j. W = MAP orc (trace_events (trace_context orc j ctx s))) /\
      (!fuel. agrees orc W (trace_events (trace_context orc fuel ctx s))) /\
      (!fuel. gas_res_rel (run_context fuel ctx (s with vs_gas_readings := W))
                          (ev_context orc fuel ctx s)) /\
      (!p d fn inst t. ev_reachable orc s ctx p d fn inst t ==>
         ?ws. raw_reachable (s with vs_gas_readings := W) ctx fn inst
                (t with vs_gas_readings := ws))
Proof
  strip_tac >> drule context_agreement_prefix_exists >>
  disch_then (qspecl_then [`s`, `ctx`] strip_assume_tac) >>
  qabbrev_tac `ws = MAP orc (trace_events (trace_context orc j ctx s))` >>
  qexists_tac `ws` >> conj_tac
  >- (qexists_tac `j` >> simp[Abbr `ws`]) >>
  conj_tac >- simp[Abbr `ws`] >> conj_tac
  >- (gen_tac >> first_x_assum (qspec_then `fuel` mp_tac) >>
      strip_tac >> drule replay_context >> strip_tac >>
      metis_tac[residual_result_gas_rel]) >>
  rpt strip_tac >> drule_all ev_reachable_trace_witness >> strip_tac >>
  qexists_tac `DROP n ws` >> irule replay_context_visit >>
  metis_tac[]
QED

Theorem gas_oracle_to_list:
  EVERY wf_function ctx.ctx_functions /\ FINITE {e | orc e <> 0w} ==>
  ?W. (!fuel. gas_res_rel (run_context fuel ctx (s with vs_gas_readings := W))
                          (ev_context orc fuel ctx s)) /\
      (!p d fn inst t. ev_reachable orc s ctx p d fn inst t ==>
         ?ws. raw_reachable (s with vs_gas_readings := W) ctx fn inst
                (t with vs_gas_readings := ws))
Proof
  metis_tac[gas_oracle_to_list_traced]
QED
