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
  dftGasInvMemoryRanges dftGasInvForwardActive dftGasInvCrossingProbe
  dftGasInvPairedHistory
  dftGasOracleDefs dftRunRel dftScheduleOrder dftDefs o1PassContract
  unitMemInv unitShapeDefs contextCodegenRel venomExecSemantics

(* The hypotheses before the last are dft_ctx_sim_gas's (dftContractGas).
   o1_ctx_shape C gives inst_shape_ok for every instruction (no DJMP or
   OFFSET); a memory access crosses only instructions that step OK
   (dftGasInvCrossingProbe's inv_crossed_predecessor_total). *)
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
  rpt strip_tac >> rename1 `ev_reachable orc s C' p d fn' inst t` >>
  `active_inst fn' inst t` by
    (qpat_x_assum `ev_reachable orc s C' p d fn' inst t` mp_tac >>
     rewrite_tac[Once ev_reachable_cases] >> metis_tac[]) >>
  Cases_on `inv_memory_observation inst.inst_opcode`
  >- (drule_all inv_reachable_memory_ranges >> strip_tac >>
      `lowered_mem_fact eom C fn inst sS` by metis_tac[] >>
      `active_inst fn inst sS` by
        (qpat_x_assum `ev_reachable orc s C p d fn inst sS` mp_tac >>
         rewrite_tac[Once ev_reachable_cases] >> metis_tac[]) >>
      qpat_x_assum `lowered_mem_fact eom C fn inst sS` mp_tac >>
      simp[lowered_mem_fact_def, lowered_mem_ok_def] >> strip_tac
      >- (simp[lowered_mem_fact_def, lowered_mem_ok_def] >> disj1_tac >>
          irule inv_forward_active >> metis_tac[]) >>
      simp[lowered_mem_fact_def, lowered_mem_ok_def]) >>
  drule inv_paired_history >> disch_then (qspec_then `C` mp_tac) >>
  simp[] >> strip_tac >>
  `inst_shape_ok inst` by (irule inv_target_active_shape >> metis_tac[]) >>
  `inst_mem_ranges inst t = []` by metis_tac[inv_memory_observation_covers_ranges] >>
  simp[lowered_mem_fact_def, lowered_mem_ok_def]
QED
