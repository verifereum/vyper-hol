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

Theorem gas_oracle_to_list:
  EVERY wf_function ctx.ctx_functions /\ FINITE {e | orc e <> 0w} ==>
  ?W. (!fuel. gas_res_rel (run_context fuel ctx (s with vs_gas_readings := W))
                          (ev_context orc fuel ctx s)) /\
      (!p d fn inst t. ev_reachable orc s ctx p d fn inst t ==>
         ?ws. raw_reachable (s with vs_gas_readings := W) ctx fn inst
                (t with vs_gas_readings := ws))
Proof
  cheat
QED
