(* DFT memory observations on the raw-FMP wave, with actual static aborts. *)
Theory dftWaveStaticMemoryInv
Ancestors
  dftGasOracleInv dftGasInvMemoryRanges dftGasInvTerminalReach
  dftGasInvForwardActive dftGasInvCrossingProbe dftGasInvPairedHistory
  dftGasOracleDefs dftRunRel dftScheduleOrder dftDefs o1PassContract
  unitMemInv unitShapeDefs contextCodegenRel venomExecSemantics
  dftStaticAbortCompletion dftStaticAbortInterval dftStaticAbortExtension
  dftGasInvOracleFrame staticAbortDefs staticShadowEventReachable
  dftGasInvFlexibleTrace dftGasToListReachBoundary venomInst venomState list

Theorem inv_observation_range_transfer[local]:
  o1_ctx_shape C /\ MEM fn C.ctx_functions /\
  dft_fn_rel fn (dft_fn fn) /\
  active_inst fn inst sS /\ active_inst (dft_fn fn) inst t /\
  sS.vs_current_bb = t.vs_current_bb /\
  sS.vs_initial_fmp = t.vs_initial_fmp /\
  inst_mem_ranges inst sS = inst_mem_ranges inst t /\
  (in_revert_forward fn sS \/
   EVERY (\(off,len). P sS.vs_initial_fmp off len)
     (inst_mem_ranges inst sS)) ==>
  in_revert_forward (dft_fn fn) t \/
  EVERY (\(off,len). P t.vs_initial_fmp off len)
    (inst_mem_ranges inst t)
Proof
  strip_tac >- (disj1_tac >> irule inv_forward_active >> metis_tac[]) >>
  metis_tac[]
QED

(* One extraction serves preservation and the available-source-write API. *)
Theorem inv_wave_static_observation_classification[local]:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ o1_ctx_shape C /\
  ctx_labels_bound C s.vs_labels /\ o1_initial_state_ok s /\
  s.vs_fmp = s.vs_initial_fmp /\ code_layout_valid s /\
  s.vs_call_ctx.cc_static /\ ev_reachable orc s C' p d fn' inst t ==>
  lowered_mem_fact eom C' fn' inst t \/
  (?fn sS. MEM fn C.ctx_functions /\ fn' = dft_fn fn /\ dft_fn_rel fn fn' /\
    ev_reachable orc s C p d fn inst sS /\
    (in_static_abort_prefix fn sS ==> in_static_abort_prefix fn' t) /\
    (lowered_mem_fact eom C fn inst sS ==> lowered_mem_fact eom C' fn' inst t)) \/
  (in_static_abort_prefix fn' t /\
   ?fn x0 s_x0. MEM fn C.ctx_functions /\ fn' = dft_fn fn /\
     dft_fn_rel fn fn' /\ ev_reachable orc s C p d fn x0 s_x0 /\
     active_inst fn x0 s_x0 /\ MEM x0.inst_opcode [SSTORE; TSTORE; LOG] /\
     s_x0.vs_call_ctx.cc_static /\
     IS_SOME (eval_operands x0.inst_operands s_x0))
Proof
  strip_tac >>
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
      strip_tac >- suspend "observation" >> suspend "write") >>
  suspend "nonobservation"
QED

Resume inv_wave_static_observation_classification[nonobservation]:
  drule inv_paired_history_static >> disch_then (qspec_then `C` mp_tac) >>
  simp[] >> strip_tac >>
  `inst_shape_ok inst` by (irule inv_target_active_shape >> metis_tac[]) >>
  `inst_mem_ranges inst t = []` by
    metis_tac[inv_memory_observation_covers_ranges] >>
  disj1_tac >> simp[lowered_mem_fact_def, lowered_mem_ok_def]
QED

Resume inv_wave_static_observation_classification[dret]:
  drule_all inv_reachable_dret_exact_static >> strip_tac >>
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
  disj2_tac >> disj1_tac >> qexistsl [`fn`, `t`] >> simp[] >>
  rewrite_tac[lowered_mem_fact_def, lowered_mem_ok_def] >> strip_tac >>
  irule (BETA_RULE (Q.INST
    [`P` |-> `\fmp off len. len = 0 \/ off + len <= eom \/ w2n fmp <= off`]
    inv_observation_range_transfer)) >> metis_tac[]
QED

Resume inv_wave_static_observation_classification[observation]:
  `sS.vs_current_bb = s0.vs_current_bb` by
    (`inv_ev_ftrace orc p d C srcpre s0 sS` by
       (irule (iffRL inv_ev_ftrace_slice) >>
        qexistsl [`pseudos`, `inst::srcpost`, `bb`] >> simp[APPEND_ASSOC]) >>
     metis_tac[inv_ev_ftrace_current_bb]) >>
  `inst_mem_ranges inst sS = inst_mem_ranges inst t` by
    metis_tac[inv_non_dret_ranges_cong] >>
  disj2_tac >> disj1_tac >> qexistsl [`fn`, `sS`] >> simp[] >> conj_tac
  >- (strip_tac >> fs[in_static_abort_prefix_def] >>
      `static_abort_at bb (LENGTH pseudos + LENGTH srcpre)` by gvs[] >>
      `static_abort_at bb' (LENGTH pseudos + LENGTH consumed)` by
        (irule inv_source_prefix_target_abort >> simp[] >>
         goal_assum (drule_at Any) >> simp[] >>
         goal_assum (drule_at Any) >> simp[APPEND_ASSOC] >> metis_tac[]) >>
      `t.vs_call_ctx.cc_static` by metis_tac[static_shadow_ev_reachable] >>
      simp[in_static_abort_prefix_def, arithmeticTheory.ADD_COMM] >> gvs[]) >>
  rewrite_tac[lowered_mem_fact_def, lowered_mem_ok_def] >> strip_tac >>
  irule (BETA_RULE (Q.INST
    [`P` |-> `\fmp off len. len = 0 \/ off + len <= eom \/ w2n fmp <= off`]
    inv_observation_range_transfer)) >> metis_tac[]
QED

Resume inv_wave_static_observation_classification[write]:
  `static_abort_at bb' (LENGTH pseudos + LENGTH consumed)` by
    (irule inv_missing_write_target_abort >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[APPEND_ASSOC, MEM_FILTER] >>
     qexistsl [`fn`, `s0.vs_current_bb`] >> fs[] >> metis_tac[]) >>
  `t.vs_call_ctx.cc_static` by metis_tac[static_shadow_ev_reachable] >>
  disj2_tac >> disj2_tac >> conj_tac
  >- (simp[in_static_abort_prefix_def] >> gvs[]) >>
  qexistsl [`fn`, `x0`, `sX`] >> simp[]
QED

Finalise inv_wave_static_observation_classification[local]

Theorem dft_ev_lowered_inv_wave_static_abort:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ o1_ctx_shape C /\
  ctx_labels_bound C s.vs_labels /\ o1_initial_state_ok s /\
  s.vs_fmp = s.vs_initial_fmp /\ code_layout_valid s /\
  (!p d fn inst t. ev_reachable orc s C p d fn inst t ==>
     (in_static_abort_prefix fn t \/ lowered_mem_fact eom C fn inst t)) ==>
  !p d fn inst t. ev_reachable orc s C' p d fn inst t ==>
    (in_static_abort_prefix fn t \/ lowered_mem_fact eom C' fn inst t)
Proof
  strip_tac >> Cases_on `s.vs_call_ctx.cc_static`
  >- (rpt strip_tac >> drule_all inv_wave_static_observation_classification >>
      metis_tac[]) >>
  `!p d fn inst t. ev_reachable orc s C p d fn inst t ==>
     lowered_mem_fact eom C fn inst t` by
    (rpt strip_tac >>
     `~t.vs_call_ctx.cc_static` by metis_tac[inv_ev_reachable_nonstatic] >>
     metis_tac[in_static_abort_prefix_def]) >>
  mp_tac (Q.INST [`C:venom_context` |-> `C`, `C':venom_context` |-> `C'`,
                  `s:venom_state` |-> `s`, `orc` |-> `orc`, `eom` |-> `eom`]
                 dft_ev_lowered_inv) >>
  simp[o1_run_state_ok_def] >> metis_tac[]
QED

Theorem dft_ev_lowered_mem_violation_source_write_available:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ o1_ctx_shape C /\
  ctx_labels_bound C s.vs_labels /\ o1_initial_state_ok s /\
  s.vs_fmp = s.vs_initial_fmp /\ code_layout_valid s /\
  (!p d fn inst t. ev_reachable orc s C p d fn inst t ==>
     lowered_mem_fact eom C fn inst t) /\
  ev_reachable orc s C' p d fn' inst t /\
  ~lowered_mem_fact eom C' fn' inst t ==>
  in_static_abort_prefix fn' t /\
  ?fn x0 s_x0. MEM fn C.ctx_functions /\ fn' = dft_fn fn /\
    dft_fn_rel fn fn' /\ ev_reachable orc s C p d fn x0 s_x0 /\
    active_inst fn x0 s_x0 /\
    MEM x0.inst_opcode [SSTORE; TSTORE; LOG] /\
    s_x0.vs_call_ctx.cc_static /\
    IS_SOME (eval_operands x0.inst_operands s_x0)
Proof
  strip_tac >> Cases_on `s.vs_call_ctx.cc_static`
  >- (drule_all inv_wave_static_observation_classification >> metis_tac[]) >>
  mp_tac (Q.INST [`C:venom_context` |-> `C`, `C':venom_context` |-> `C'`,
                  `s:venom_state` |-> `s`, `orc` |-> `orc`, `eom` |-> `eom`]
                 dft_ev_lowered_inv) >>
  simp[o1_run_state_ok_def] >> metis_tac[]
QED
