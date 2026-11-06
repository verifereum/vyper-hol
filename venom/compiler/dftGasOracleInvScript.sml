(*
 * DFT keeps the lowered memory fact (o1PassContract's lowered_mem_fact) on
 * the oracle-reachable states (dftGasOracleDefs) of one oracle and initial
 * state: every memory access C' reaches, C reaches at the same event frame
 * with the same operand values, and DFT keeps revert forwardings.
 *
 * TOP-LEVEL:
 *   dft_ev_lowered_inv - the fact on C's oracle-reachable states gives it
 *                        on C''s
 *)
Theory dftGasOracleInv
Ancestors
  dftGasOracleDefs dftRunRel dftScheduleOrder dftDefs o1PassContract
  unitMemInv unitShapeDefs contextCodegenRel venomExecSemantics

(* The hypotheses before the last are dft_ctx_sim_gas's (dftContractGas).
   o1_ctx_shape C gives inst_shape_ok for every instruction (no CREATE,
   CREATE2, DELEGATECALL, SELFDESTRUCT, DJMP or OFFSET), so no memory
   access moves past an instruction that can abort or stop. *)
Theorem dft_ev_lowered_inv:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ o1_ctx_shape C /\
  ctx_labels_bound C s.vs_labels /\ o1_run_state_ok s /\
  (!p d fn inst t. ev_reachable orc s C p d fn inst t ==>
     lowered_mem_fact eom C fn inst t) ==>
  !p d fn inst t. ev_reachable orc s C' p d fn inst t ==>
    lowered_mem_fact eom C' fn inst t
Proof
  cheat
QED
