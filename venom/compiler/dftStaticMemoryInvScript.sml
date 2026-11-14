(* DFT memory safety from actual reachability and restricted shadow prefixes. *)
Theory dftStaticMemoryInv
Ancestors
  dftStaticMemoryObservation dftGasOracleInv dftGasInvMemoryRanges
  dftGasInvTerminalReach dftGasInvForwardActive dftGasInvCrossingProbe
  dftGasInvPairedHistory dftGasOracleDefs dftRunRel dftScheduleOrder
  dftDefs o1PassContract unitMemInv unitShapeDefs contextCodegenRel
  venomExecSemantics staticAbortMemDefs

Theorem dft_ev_lowered_inv_static:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ o1_ctx_shape C /\
  ctx_labels_bound C s.vs_labels /\ o1_initial_state_ok s /\
  s.vs_fmp = s.vs_initial_fmp /\ code_layout_valid s /\
  (!p d fn inst t. ev_reachable orc s C p d fn inst t ==>
     static_mem_ok eom C fn inst t) /\
  (s.vs_call_ctx.cc_static ==>
    !p d fn inst sS.
      ev_shadow_prefix_reachable orc s C p d fn inst sS /\
      inv_memory_observation inst.inst_opcode /\ inst.inst_opcode <> DRET ==>
      static_mem_ok eom C fn inst sS) ==>
  !p d fn inst t. ev_reachable orc s C' p d fn inst t ==>
    static_mem_ok eom C' fn inst t
Proof
  strip_tac >> Cases_on `s.vs_call_ctx.cc_static`
  >- (rpt strip_tac >> rename1 `ev_reachable orc s C' p d fn' inst t` >>
      `active_inst fn' inst t` by
        (qpat_x_assum `ev_reachable orc s C' p d fn' inst t` mp_tac >>
         rewrite_tac[Once ev_reachable_cases] >> metis_tac[]) >>
      Cases_on `inv_memory_observation inst.inst_opcode`
      >- (Cases_on `inst.inst_opcode = DRET`
          >- (drule_all inv_reachable_dret_exact_static >> strip_tac >>
              `static_mem_ok eom C fn inst t` by metis_tac[] >>
              `active_inst fn inst t` by
                (qpat_x_assum `ev_reachable orc s C p d fn inst t` mp_tac >>
                 rewrite_tac[Once ev_reachable_cases] >> metis_tac[]) >>
              qpat_x_assum `static_mem_ok eom C fn inst t` mp_tac >>
              simp[static_mem_ok_def] >> strip_tac
              >- (simp[static_mem_ok_def] >> disj1_tac >>
                  irule inv_forward_active >> metis_tac[]) >>
              simp[static_mem_ok_def]) >>
          drule_all inv_reachable_memory_observation_shadow >> strip_tac >>
          `static_mem_ok eom C fn inst sS` by metis_tac[] >>
          `inst_mem_ranges inst sS = inst_mem_ranges inst t` by
            metis_tac[inv_non_dret_ranges_cong] >>
          qpat_x_assum `static_mem_ok eom C fn inst sS` mp_tac >>
          simp[static_mem_ok_def] >> strip_tac
          >- (simp[static_mem_ok_def] >> disj1_tac >>
              irule inv_forward_active >> metis_tac[]) >>
          simp[static_mem_ok_def]) >>
      drule inv_paired_history_static >> disch_then (qspec_then `C` mp_tac) >>
      simp[] >> strip_tac >>
      `inst_shape_ok inst` by (irule inv_target_active_shape >> metis_tac[]) >>
      `inst_mem_ranges inst t = []` by
        metis_tac[inv_memory_observation_covers_ranges] >>
      simp[static_mem_ok_def]) >>
  `o1_run_state_ok s` by simp[o1_run_state_ok_def] >>
  mp_tac (Q.INST [`C:venom_context` |-> `C`, `C':venom_context` |-> `C'`,
                  `s:venom_state` |-> `s`, `orc` |-> `orc`, `eom` |-> `eom`]
                 dft_ev_lowered_inv) >> asm_rewrite_tac[]
QED
