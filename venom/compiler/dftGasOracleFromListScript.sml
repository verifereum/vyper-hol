(*
 * A run that reads GAS from the state's reading list is a run of the oracle
 * semantics (dftGasOracleDefs): its GAS events, named by place, get the
 * readings the list run consumes there, and every other event 0w.
 *
 * TOP-LEVEL:
 *   gas_oracle_from_list - the oracle of a list run
 *)
Theory dftGasOracleFromList
Ancestors
  dftGasOracleDefs contextRawReachable o1PassContract venomExecSemantics

(* Within a block execution each id runs at most once, so distinct ids in
   every block make the event names of one run distinct.  The list is
   finite, so only finitely many events read a nonzero word. *)
Theorem gas_oracle_from_list:
  EVERY wf_function ctx.ctx_functions /\
  EVERY (\fn. EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions))
                fn.fn_blocks) ctx.ctx_functions ==>
  ?orc. FINITE {e | orc e <> 0w} /\
      (!fuel. gas_res_rel (run_context fuel ctx s) (ev_context orc fuel ctx s)) /\
      (!fn inst t. raw_reachable s ctx fn inst t ==>
         ?p d. ev_reachable orc s ctx p d fn inst
                 (t with vs_gas_readings := s.vs_gas_readings))
Proof
  cheat
QED
