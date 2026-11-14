Theory readonlyInvokeCopyFwdExecutionEmptyWrites
Ancestors
  readonlyInvokeCopyFwdExecution readonlyInvokeCopyFwdOpaque
  readonlyInvokeCopyFwdOpaqueReturn readonlyInvokeCopyFwdRel
  readonlyInvokeCopyFwdMemory readonlyInvokeCopyFwdOperationalSupport
  readonlyInvokeCopyFwdHistoryPhase readonlyInvokeCopyFwdHeterogeneousLedger
  internalReturnCopyFwdSim o1LowerDloadShared o1LowerDloadOccurrence regularCallEmitSim
  readonlyInvokeCopyFwdStepsMemory
  taintAgree ptrDiscipline contextCodegenRel venomExecSemantics venomState venomMemProps
  venomInst finite_map list pred_set

Theorem ricf_frame_empty_writes[local]:
  ricf_frame_agree D X sites PG G tn s t ==>
  ricf_frame_agree D X sites PG G tn
    (write_memory_with_expansion dst [] s)
    (write_memory_with_expansion target [] t)
Proof
  simp[ricf_frame_agree_def] >> strip_tac >> rpt conj_tac
  >- (mp_tac (Q.INST [`s` |-> `s`,
        `t` |-> `t with <|vs_vars := s.vs_vars; vs_params := s.vs_params|>`,
        `M` |-> `tn.t_mem`,
        `ms` |-> `(write_memory_with_expansion dst [] s).vs_memory`,
        `mt` |-> `(write_memory_with_expansion target [] t).vs_memory`]
        taint_agree_memory_update) >>
      impl_tac >- (simp[read_byte_write_memory_with_expansion] >>
        fs[taint_agree_def] >> metis_tac[]) >>
      simp[write_memory_with_expansion_def])
  >- simp[write_memory_with_expansion_def]
  >- (simp[write_memory_with_expansion_def] >> metis_tac[])
  >- simp[write_memory_with_expansion_def]
  >> fs[ircf_cross_def] >> simp[ircf_cross_def,
       read_byte_write_memory_with_expansion] >> metis_tac[]
QED

Theorem ricf_opaque_frame_empty_writes[local]:
  ricf_opaque_frame_agree fn D X sites PG G tn s t ==>
  ricf_opaque_frame_agree fn D X sites PG G tn
    (write_memory_with_expansion dst [] s)
    (write_memory_with_expansion target [] t)
Proof
  simp[ricf_opaque_frame_agree_def] >> strip_tac >>
  `ricf_opaque_view fn PG G (write_memory_with_expansion dst [] s) =
     write_memory_with_expansion dst [] (ricf_opaque_view fn PG G s) /\
   ricf_opaque_view fn PG G (write_memory_with_expansion target [] t) =
     write_memory_with_expansion target [] (ricf_opaque_view fn PG G t)` by
    simp[ricf_opaque_view_def, write_memory_with_expansion_def] >>
  simp[] >> irule ricf_frame_empty_writes >> simp[]
QED

Theorem ricf_execution_empty_write_next:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  active_inst fn inst s /\ ~is_terminator inst.inst_opcode /\
  inst.inst_opcode <> INVOKE /\
  u = write_memory_with_expansion dst [] s /\
  v = write_memory_with_expansion target [] t /\
  step_inst fuel C inst s = OK u /\ step_inst fuel Ct inst t = OK v /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) /\
  step_prov PG G inst u = G /\ step_taint inst s u tn = tn /\
  occurrence_sites_step a B inst u = B ==>
  ricf_execution_invariant vs C D stk PG G tn fn next
    (u with vs_inst_idx := SUC s.vs_inst_idx)
    (v with vs_inst_idx := SUC s.vs_inst_idx)
    n a U B HP (occurrence_step a HP H inst u) ledger E sites maps targets tn
Proof
  strip_tac >>
  qpat_x_assum `u = _` SUBST_ALL_TAC >> qpat_x_assum `v = _` SUBST_ALL_TAC >>
  `ricf_opaque_frame_agree fn D (ircf_dead (ricf_original_copy_ids C) s stk)
    sites (ricf_complete_params PG s.vs_params) G tn s t /\
   ricf_opaque_live_stack_agree D (ricf_original_copy_ids C) tn maps stk targets s t /\
   ircf_cross tn (ricf_phase_ranges 0 ledger) s t /\
   ricf_cert_crosses tn (ricf_phase_stack_ranges stk ledger) stk s t /\
   ricf_support_agree B E tn s t` by fs[ricf_execution_invariant_def] >>
  mp_tac (Q.INST [`rt` |-> `tn`,
    `u` |-> `write_memory_with_expansion dst [] s`,
    `v` |-> `write_memory_with_expansion target [] t`] ricf_execution_next) >>
  impl_tac >- (simp[] >> rpt conj_tac
  >- (`ircf_dead (ricf_original_copy_ids C) (write_memory_with_expansion dst [] s) stk =
       ircf_dead (ricf_original_copy_ids C) s stk /\
       (write_memory_with_expansion dst [] s).vs_params = s.vs_params` by
        simp[ircf_dead_def, write_memory_with_expansion_def] >>
      simp[] >> irule ricf_opaque_frame_empty_writes >> simp[])
  >- (fs[ricf_opaque_live_stack_agree_def] >>
      simp[ricf_opaque_live_stack_agree_def, ricf_write_memory_merge] >>
      rpt strip_tac >> irule ricf_opaque_frame_empty_writes >> simp[])
  >- (fs[ircf_cross_def] >> simp[ircf_cross_def,
        read_byte_write_memory_with_expansion] >> metis_tac[])
  >- (fs[ricf_cert_crosses_def, EVERY_MEM, ircf_cross_def] >>
      simp[ricf_cert_crosses_def, EVERY_MEM, ircf_cross_def,
        ricf_write_memory_merge, read_byte_write_memory_with_expansion] >> metis_tac[])
  >> fs[ricf_support_agree_def] >>
     simp[ricf_support_agree_def, read_byte_write_memory_with_expansion] >> metis_tac[]) >>
  simp[]
QED
