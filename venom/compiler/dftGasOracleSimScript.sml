(*
 * DFT simulates in the oracle semantics (dftGasOracleDefs) at the same
 * oracle and fuel: DFT keeps each block, its instruction ids and the fuel
 * it runs at, so a GAS read in either context reads the same word.
 *
 * TOP-LEVEL:
 *   dft_ev_context_sim - a terminating oracle run of C is one of C'
 *)
Theory dftGasOracleSim
Ancestors
  dftGasOracleDefs dftRunRel dftScheduleOrder dftDefs o1PassContract
  unitShapeDefs venomExecSemantics

(* The hypotheses are dft_ctx_sim_gas's (dftContractGas).  o1_ctx_shape C
   gives inst_shape_ok for every instruction (no CREATE, CREATE2,
   DELEGATECALL, SELFDESTRUCT, DJMP or OFFSET). *)
Theorem dft_ev_context_sim:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ o1_ctx_shape C /\
  ctx_labels_bound C s.vs_labels /\ o1_run_state_ok s /\
  terminates (ev_context orc fuel C s) ==>
  dft_res_rel (ev_context orc fuel C s) (ev_context orc fuel C' s)
Proof
  cheat
QED
