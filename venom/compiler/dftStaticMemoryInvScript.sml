(* DFT memory safety from actual reachability and restricted shadow prefixes. *)
Theory dftStaticMemoryInv
Ancestors
  dftStaticMemoryObservation dftGasOracleInv dftGasInvMemoryRanges
  dftGasInvTerminalReach dftGasInvForwardActive dftGasInvCrossingProbe
  dftGasInvPairedHistory dftGasOracleDefs dftRunRel dftScheduleOrder
  dftDefs o1PassContract unitMemInv unitShapeDefs contextCodegenRel
  venomExecSemantics staticAbortMemDefs
  dftStaticAbortCompletion dftStaticAbortInterval dftStaticAbortExtension
  dftGasInvOracleFrame staticAbortDefs venomInst venomState
  dftGasToListReachBoundary list

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

(* Complete missing predecessors in the actual static state when none is
   a static write. Otherwise the first pending target write supplies a
   straight abort prefix. A source abort-prefix alternative must also be
   transported; it cannot be treated as an ordinary range bound. *)
Theorem dft_ev_lowered_inv_static_abort:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ o1_ctx_shape C /\
  ctx_labels_bound C s.vs_labels /\ o1_initial_state_ok s /\
  s.vs_fmp = s.vs_initial_fmp /\ code_layout_valid s /\
  (!p d fn inst t. ev_reachable orc s C p d fn inst t ==>
     static_mem_ok_abort eom C fn inst t) ==>
  !p d fn inst t. ev_reachable orc s C' p d fn inst t ==>
    static_mem_ok_abort eom C' fn inst t
Proof
  strip_tac >> Cases_on `s.vs_call_ctx.cc_static`
  >- (rpt strip_tac >> rename1 `ev_reachable orc s C' p d fn' inst t` >>
      `active_inst fn' inst t` by
        (qpat_assum `ev_reachable orc s C' p d fn' inst t` mp_tac >>
         rewrite_tac[Once ev_reachable_cases] >> metis_tac[]) >>
      Cases_on `inv_memory_observation inst.inst_opcode`
      >- (Cases_on `inst.inst_opcode = DRET`
          >- suspend "dret" >>
          mp_tac (Q.INST [`initial` |-> `s`] inv_static_observation_source_completion) >>
          impl_tac
          >- (conj_tac >- metis_tac[inv_remaining_trace_prefix_no_static_writes] >>
              conj_tac >- metis_tac[inv_static_ftrace_no_writes] >>
              metis_tac[]) >>
          strip_tac >- suspend "source_observation" >>
          suspend "source_write") >>
      suspend "nonobservation") >>
  suspend "nonstatic"
QED

Resume dft_ev_lowered_inv_static_abort[nonstatic]:
  `!p d fn inst t. ev_reachable orc s C p d fn inst t ==>
     static_mem_ok eom C fn inst t` by
    (rpt strip_tac >>
     `~t.vs_call_ctx.cc_static` by metis_tac[inv_ev_reachable_nonstatic] >>
     metis_tac[static_mem_ok_abort_nonstatic]) >>
  mp_tac (Q.INST [`C:venom_context` |-> `C`, `C':venom_context` |-> `C'`,
                  `s:venom_state` |-> `s`, `orc` |-> `orc`, `eom` |-> `eom`]
                 dft_ev_lowered_inv_static) >>
  asm_rewrite_tac[] >> strip_tac >>
  rpt strip_tac >> simp[static_mem_ok_abort_def] >> metis_tac[]
QED

Resume dft_ev_lowered_inv_static_abort[nonobservation]:
  drule inv_paired_history_static >> disch_then (qspec_then `C` mp_tac) >>
  simp[] >> strip_tac >>
  `inst_shape_ok inst` by (irule inv_target_active_shape >> metis_tac[]) >>
  `inst_mem_ranges inst t = []` by
    metis_tac[inv_memory_observation_covers_ranges] >>
  simp[static_mem_ok_abort_def, static_mem_ok_def]
QED

Resume dft_ev_lowered_inv_static_abort[dret]:
  drule_all inv_reachable_dret_exact_static >> strip_tac >>
  `static_mem_ok_abort eom C fn inst t` by metis_tac[] >>
  `active_inst fn inst t` by
    (qpat_assum `ev_reachable orc s C p d fn inst t` mp_tac >>
     rewrite_tac[Once ev_reachable_cases] >> metis_tac[]) >>
  `~in_static_abort_prefix fn t` by
    (strip_tac >> fs[in_static_abort_prefix_def] >>
     `get_instruction bb t.vs_inst_idx = SOME inst` by
       (`ALL_DISTINCT (fn_labels fn)` by
          metis_tac[dft_fn_rel_def, venomWfTheory.wf_function_def] >>
        drule_all active_inst_lookup_distinct >> strip_tac >> gvs[]) >>
     gvs[static_abort_at_def, static_abort_pair_def] >>
     (Cases_on `t.vs_inst_idx = j`
      >- gvs[get_instruction_def] >>
      `t.vs_inst_idx < j` by decide_tac >>
      qpat_x_assum `!k i. _` (qspecl_then [`t.vs_inst_idx`, `inst`] mp_tac) >>
      simp[is_terminator_def])) >>
  `static_mem_ok eom C fn inst t` by gvs[static_mem_ok_abort_def] >>
  qpat_x_assum `static_mem_ok eom C fn inst t` mp_tac >>
  simp[static_mem_ok_def] >> strip_tac
  >- (simp[static_mem_ok_abort_def, static_mem_ok_def] >> disj2_tac >>
      disj1_tac >> irule inv_forward_active >> metis_tac[]) >>
  simp[static_mem_ok_abort_def, static_mem_ok_def]
QED

Resume dft_ev_lowered_inv_static_abort[source_observation]:
  `sS.vs_current_bb = s0.vs_current_bb` by
    (`inv_ev_ftrace orc p d C srcpre s0 sS` by
       (irule (iffRL dftGasInvFlexibleTraceTheory.inv_ev_ftrace_slice) >>
        qexistsl [`pseudos`, `inst::srcpost`, `bb`] >> simp[APPEND_ASSOC]) >>
     metis_tac[inv_ev_ftrace_current_bb]) >>
  `static_mem_ok_abort eom C fn inst sS` by metis_tac[] >>
  qpat_x_assum `static_mem_ok_abort eom C fn inst sS` mp_tac >>
  rewrite_tac[static_mem_ok_abort_def] >> strip_tac
  >- (fs[in_static_abort_prefix_def] >>
      `static_abort_at bb (LENGTH pseudos + LENGTH srcpre)` by gvs[] >>
      `static_abort_at bb' (LENGTH pseudos + LENGTH consumed)` by
        (irule inv_source_prefix_target_abort >> simp[] >>
         goal_assum (drule_at Any) >> simp[] >>
         goal_assum (drule_at Any) >> simp[APPEND_ASSOC] >> metis_tac[]) >>
      `t.vs_call_ctx.cc_static` by
        metis_tac[staticShadowEventReachableTheory.static_shadow_ev_reachable] >>
      simp[static_mem_ok_abort_def, in_static_abort_prefix_def,
           arithmeticTheory.ADD_COMM] >> gvs[]) >>
  `inst_mem_ranges inst sS = inst_mem_ranges inst t` by
    metis_tac[inv_non_dret_ranges_cong] >>
  qpat_x_assum `static_mem_ok eom C fn inst sS` mp_tac >>
  simp[static_mem_ok_def] >> strip_tac
  >- (simp[static_mem_ok_abort_def, static_mem_ok_def] >> disj2_tac >>
      disj1_tac >> irule inv_forward_active >> metis_tac[]) >>
  simp[static_mem_ok_abort_def, static_mem_ok_def]
QED

Resume dft_ev_lowered_inv_static_abort[source_write]:
  `static_abort_at bb' (LENGTH pseudos + LENGTH consumed)` by
    (irule inv_missing_write_target_abort >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[APPEND_ASSOC, MEM_FILTER] >>
     qexistsl [`fn`, `s0.vs_current_bb`] >>
     fs[] >> metis_tac[]) >>
  `t.vs_call_ctx.cc_static` by
    metis_tac[staticShadowEventReachableTheory.static_shadow_ev_reachable] >>
  simp[static_mem_ok_abort_def, in_static_abort_prefix_def] >> gvs[]
QED


Finalise dft_ev_lowered_inv_static_abort

Theorem dft_ev_static_mem_violation_source_write_available:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ o1_ctx_shape C /\
  ctx_labels_bound C s.vs_labels /\ o1_initial_state_ok s /\
  s.vs_fmp = s.vs_initial_fmp /\ code_layout_valid s /\
  (!p d fn inst t. ev_reachable orc s C p d fn inst t ==>
     static_mem_ok eom C fn inst t) /\
  ev_reachable orc s C' p d fn' inst t /\
  ~static_mem_ok eom C' fn' inst t ==>
  in_static_abort_prefix fn' t /\
  ?fn x0 s_x0. MEM fn C.ctx_functions /\ fn' = dft_fn fn /\
    dft_fn_rel fn fn' /\ ev_reachable orc s C p d fn x0 s_x0 /\
    active_inst fn x0 s_x0 /\
    MEM x0.inst_opcode [SSTORE; TSTORE; LOG] /\
    s_x0.vs_call_ctx.cc_static /\
    IS_SOME (eval_operands x0.inst_operands s_x0)
Proof
  strip_tac >> Cases_on `s.vs_call_ctx.cc_static`
  >- (`active_inst fn' inst t` by
        (qpat_assum `ev_reachable orc s C' p d fn' inst t` mp_tac >>
         rewrite_tac[Once ev_reachable_cases] >> metis_tac[]) >>
      Cases_on `inv_memory_observation inst.inst_opcode`
      >- (Cases_on `inst.inst_opcode = DRET`
          >- suspend "dret" >>
          mp_tac (Q.INST [`initial` |-> `s`] inv_static_observation_source_completion) >>
          impl_tac
          >- (conj_tac >- metis_tac[inv_remaining_trace_prefix_no_static_writes] >>
              conj_tac >- metis_tac[inv_static_ftrace_no_writes] >>
              metis_tac[]) >>
          strip_tac >- suspend "observation" >>
          suspend "write") >>
      suspend "nonobservation") >>
  suspend "nonstatic"
QED

Resume dft_ev_static_mem_violation_source_write_available[nonstatic]:
  mp_tac (Q.INST [`C:venom_context` |-> `C`, `C':venom_context` |-> `C'`,
                  `s:venom_state` |-> `s`, `orc` |-> `orc`, `eom` |-> `eom`]
                 dft_ev_lowered_inv_static) >>
  asm_rewrite_tac[] >> metis_tac[]
QED

Resume dft_ev_static_mem_violation_source_write_available[nonobservation]:
  drule inv_paired_history_static >> disch_then (qspec_then `C` mp_tac) >>
  simp[] >> strip_tac >>
  `inst_shape_ok inst` by (irule inv_target_active_shape >> metis_tac[]) >>
  `inst_mem_ranges inst t = []` by
    metis_tac[inv_memory_observation_covers_ranges] >>
  fs[static_mem_ok_def]
QED

Resume dft_ev_static_mem_violation_source_write_available[dret]:
  drule_all inv_reachable_dret_exact_static >> strip_tac >>
  `static_mem_ok eom C fn inst t` by metis_tac[] >>
  `active_inst fn inst t` by
    (qpat_assum `ev_reachable orc s C p d fn inst t` mp_tac >>
     rewrite_tac[Once ev_reachable_cases] >> metis_tac[]) >>
  qpat_x_assum `static_mem_ok eom C fn inst t` mp_tac >>
  simp[static_mem_ok_def] >> strip_tac
  >- (`in_revert_forward fn' t` by
        (fs[] >> irule inv_forward_active >> metis_tac[]) >>
      fs[static_mem_ok_def]) >>
  fs[static_mem_ok_def]
QED

Resume dft_ev_static_mem_violation_source_write_available[observation]:
  `sS.vs_current_bb = s0.vs_current_bb` by
    (`inv_ev_ftrace orc p d C srcpre s0 sS` by
       (irule (iffRL dftGasInvFlexibleTraceTheory.inv_ev_ftrace_slice) >>
        qexistsl [`pseudos`, `inst::srcpost`, `bb`] >> simp[APPEND_ASSOC]) >>
     metis_tac[inv_ev_ftrace_current_bb]) >>
  `static_mem_ok eom C fn inst sS` by metis_tac[] >>
  `inst_mem_ranges inst sS = inst_mem_ranges inst t` by
    metis_tac[inv_non_dret_ranges_cong] >>
  qpat_x_assum `static_mem_ok eom C fn inst sS` mp_tac >>
  simp[static_mem_ok_def] >> strip_tac
  >- (`in_revert_forward fn' t` by
        (fs[] >> irule inv_forward_active >> metis_tac[]) >>
      fs[static_mem_ok_def]) >>
  fs[static_mem_ok_def]
QED

Resume dft_ev_static_mem_violation_source_write_available[write]:
  `static_abort_at bb' (LENGTH pseudos + LENGTH consumed)` by
    (irule inv_missing_write_target_abort >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[APPEND_ASSOC, MEM_FILTER] >>
     qexistsl [`fn`, `s0.vs_current_bb`] >>
     fs[] >> metis_tac[]) >>
  `t.vs_call_ctx.cc_static` by
    metis_tac[staticShadowEventReachableTheory.static_shadow_ev_reachable] >>
  conj_tac
  >- (simp[in_static_abort_prefix_def] >> gvs[]) >>
  qexistsl [`fn`, `x0`, `sX`] >> simp[]
QED

Finalise dft_ev_static_mem_violation_source_write_available

Theorem dft_ev_static_mem_violation_source_write:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ o1_ctx_shape C /\
  ctx_labels_bound C s.vs_labels /\ o1_initial_state_ok s /\
  s.vs_fmp = s.vs_initial_fmp /\ code_layout_valid s /\
  (!p d fn inst t. ev_reachable orc s C p d fn inst t ==>
     static_mem_ok eom C fn inst t) /\
  ev_reachable orc s C' p d fn' inst t /\
  ~static_mem_ok eom C' fn' inst t ==>
  in_static_abort_prefix fn' t /\
  ?fn x0 s_x0. MEM fn C.ctx_functions /\ fn' = dft_fn fn /\
    dft_fn_rel fn fn' /\ ev_reachable orc s C p d fn x0 s_x0 /\
    active_inst fn x0 s_x0 /\
    MEM x0.inst_opcode [SSTORE; TSTORE; LOG] /\
    s_x0.vs_call_ctx.cc_static
Proof
  strip_tac >> drule_all dft_ev_static_mem_violation_source_write_available >>
  metis_tac[]
QED
