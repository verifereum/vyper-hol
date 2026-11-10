Theory concretizePtrFixedReadRecovery
Ancestors concretizePtrOwnerFloor concretizePtrFixedReadAudit concretizePtrFixedWriteReflection
  concretizePtrRevertHistory concretizePtrActualWrites
  concretizePtrActiveWriteOwner concretizePtrHistoryOrigin
  concretizePtrOwnedReadAudit concretizePtrActualByteFrame
  concretizePtrStructuralTrace concretizePtrStructuralTranscript
  concretizePtrPairedPrefix concretizePtrEventEmbedding
  concretizePtrHistoricalWriteExclusion concretizePtrChronologicalHistory
  concretizePtrOperationalOpcodes concretizePtrPairedFields
  concretizePtrSourceOwnership concretizePtrActivationBirths
  concretizePtrActivationChronology concretizePtrOwnerPath
  concretizePtrHistoryObservation frameExecutionHistory
  ptrDiscipline unitMemInv venomInst codegenRel
  list rich_list arithmetic pred_set finite_map

Theorem ptr_retained_ordinary_write_ledger[local]:
  ptr_paired_writes lo positions C Ct h ht done H ws /\
  q < LENGTH done /\ EL q done = w /\
  ~is_terminator (EL w h).po_inst.inst_opcode /\
  (EL w h).po_inst.inst_opcode <> INVOKE /\
  range_bytes (step_writes (EL w h).po_inst (EL w h).po_state
    (EL (SUC w) h).po_state) <> {} ==>
  ?rho. ptr_ledger_write_pair C Ct rho (EL w h) (EL (SUC w) h)
      (EL q ht) (EL (SUC q) ht) /\
    ptr_paired_write_owner lo positions rho
      (range_bytes (step_writes (EL w h).po_inst (EL w h).po_state
        (EL (SUC w) h).po_state)) (EL (SUC w) H)
Proof
  strip_tac >>
  `?rho. MEM (w,q,rho) ws` by
    (qpat_assum `ptr_paired_writes _ _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[ptr_paired_writes_def] >> strip_tac >>
     first_x_assum (qspec_then `q` mp_tac) >> simp[]) >>
  drule_all ptr_paired_write_event >> simp[ptr_paired_write_def] >>
  metis_tac[]
QED

Theorem ptr_paired_fixed_read_recovery:
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\
  x < lo /\ x NOTIN endpoint.po_taint.t_mem /\
  ~in_revert_forward endpoint.po_fn endpoint.po_state /\
  endpoint.po_inst.inst_opcode <> ASSIGN ==>
  read_byte x endpoint.po_state.vs_memory = read_byte x at.po_state.vs_memory
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_source >> strip_tac >>
  drule ptr_structural_trace_target >> strip_tac >>
  drule ptr_structural_trace_embedding >> strip_tac >>
  drule_all ptr_chrono_ordinary_non_revert >> strip_tac >>
  `!q. q < LENGTH done ==> SUC (EL q done) < LENGTH h /\
    ~in_revert_forward (EL (EL q done) h).po_fn
      (EL (EL q done) h).po_state` by
    (rpt strip_tac >>
     qpat_assum `ptr_event_embedding _ _ _` mp_tac >>
     pure_rewrite_tac[ptr_event_embedding_def] >> strip_tac >>
     `EL q done < LENGTH h - 1` by
       (first_x_assum (qspecl_then [`q`,`LENGTH done`] mp_tac) >>
        simp[EL_APPEND_EQN]) >>
     fs[EVERY_EL] >>
     `EL q done < LENGTH h` by decide_tac >> metis_tac[]) >>
  `!q. q < LENGTH done /\
    x NOTIN range_bytes (step_writes (EL (EL q done) h).po_inst
      (EL (EL q done) h).po_state (EL (SUC (EL q done)) h).po_state) ==>
    x NOTIN range_bytes (step_writes (EL q ht).po_inst
      (EL q ht).po_state (EL (SUC q) ht).po_state)` by
    (rpt strip_tac >> drule_all ptr_paired_fixed_actual_write_reflection >>
     metis_tac[]) >>
  drule_all ptr_chrono_last_actual_or_none >> strip_tac
  >- (`read_byte x endpoint.po_state.vs_memory = read_byte x vs.vs_memory` by
        (irule ptr_chrono_history_no_actual_write_byte >> simp[] >> metis_tac[]) >>
      `read_byte x at.po_state.vs_memory = read_byte x vs.vs_memory` by
        (irule ptr_chrono_history_no_actual_write_byte >>
         qexistsl [`C'`,`ht`] >> simp[] >>
         rpt strip_tac >> `k < LENGTH done` by decide_tac >> metis_tac[]) >>
      metis_tac[]) >>
  suspend "writer"
QED

Resume ptr_paired_fixed_read_recovery[writer]:
  drule ptr_structural_trace_actual_writer_retained >>
  disch_then (qspecl_then [`w`,`x`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `ptr_observation_reachable vs C (EL w h)` by
    (qpat_assum `ptr_chrono_history vs C h endpoint`
       (mp_tac o MATCH_MP ptr_chrono_history_reachable) >>
     simp[EVERY_EL] >> strip_tac >> first_x_assum irule >> decide_tac) >>
  `(EL w h).po_inst.inst_opcode <> DRET` by
    (irule ptr_stage_observation_no_dret >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `~is_terminator (EL w h).po_inst.inst_opcode /\
   (EL w h).po_inst.inst_opcode <> INVOKE` by
    (qpat_assum `(EL w h).po_inst.inst_opcode <> DRET` mp_tac >>
     Cases_on `(EL w h).po_inst.inst_opcode` >>
     simp[is_terminator_def] >>
     qpat_x_assum `x IN range_bytes _` mp_tac >>
     qpat_assum `(EL w h).po_inst.inst_opcode = _`
       (fn th => simp_tac (srw_ss())
         [th,step_writes_def,source_memory_write_ranges_def,range_bytes_def]) >>
     qpat_x_assum `DRET <> DRET` mp_tac >> simp[]) >>
  drule ptr_paired_prefix_writes >> strip_tac >>
  `range_bytes (step_writes (EL w h).po_inst (EL w h).po_state
    (EL (SUC w) h).po_state) <> {}` by metis_tac[NOT_IN_EMPTY] >>
  drule_all ptr_retained_ordinary_write_ledger >> strip_tac >>
  drule ptr_structural_transcript_ownership >>
  disch_then (qspec_then `SUC w` mp_tac) >> simp[] >>
  qabbrev_tac `snap = EL (SUC w) H` >> PairCases_on `snap` >>
  simp[ptr_snapshot_ownership_def] >> strip_tac >>
  drule ptr_source_ownership_caches >> strip_tac >>
  `EVERY (\f. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f)) C.ctx_functions` by
    (fs[ctx_has_dalloca_def, EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  drule_all ptr_source_birth_caches_slices >> strip_tac >>
  drule ptr_source_birth_caches_activations >> strip_tac >>
  drule ptr_source_activations_length >> strip_tac >>
  `!d. d <= LENGTH (EL (SUC w) h).po_stack ==>
    allocas_from lo (ptr_owner_view d (EL (SUC w) h)).cf_state` by
    (`ptr_observation_reachable vs C (EL (SUC w) h)` by
       (qpat_assum `ptr_chrono_history vs C h endpoint`
          (mp_tac o MATCH_MP ptr_chrono_history_reachable) >>
        simp[EVERY_EL] >> strip_tac >> first_x_assum irule >> simp[]) >>
     metis_tac[ptr_reachable_owner_allocas_from]) >>
  `rho' x = x` by
    (drule_all ptr_paired_write_owner_fixed >> simp[]) >>
  `read_byte x (EL (SUC w) h).po_state.vs_memory =
   read_byte x (EL (SUC q) ht).po_state.vs_memory` by
    (qpat_x_assum `ptr_ledger_write_pair _ _ _ _ _ _ _` mp_tac >>
     simp[concretizePtrPrefixLedgerTheory.ptr_ledger_write_pair_def,
          concretizePtrBytesTheory.ptr_bytes_agree_def] >>
     strip_tac >> first_x_assum (qspec_then `x` mp_tac) >> simp[]) >>
  suspend "frame"
QED

Resume ptr_paired_fixed_read_recovery[frame]:
  `!j. q < j /\ j < LENGTH done ==> w < EL j done` by
    (qpat_x_assum `ptr_event_embedding _ _ _` mp_tac >>
     pure_rewrite_tac[ptr_event_embedding_def] >> strip_tac >>
     rpt strip_tac >> first_x_assum (qspecl_then [`q`,`j`] mp_tac) >>
     simp[EL_APPEND_EQN]) >>
  `!j. SUC q <= j /\ j < LENGTH ht-1 ==>
    x NOTIN range_bytes (step_writes (EL j ht).po_inst
      (EL j ht).po_state (EL (SUC j) ht).po_state)` by
    (rpt gen_tac >> strip_tac >>
     `j < LENGTH done /\ w < EL j done` by
       (conj_tac >- decide_tac >> first_x_assum irule >> decide_tac) >>
     metis_tac[]) >>
  `EL (LENGTH h-1) h = endpoint /\ LENGTH h-1 < LENGTH h` by
    (qpat_assum `ptr_chrono_history vs C h endpoint`
       (mp_tac o MATCH_MP ptr_chrono_history_end) >>
     strip_tac >> Cases_on `h` >> gvs[LAST_EL]) >>
  `EL (LENGTH ht-1) ht = at /\ LENGTH ht-1 < LENGTH ht` by
    (qpat_assum `ptr_chrono_history vs C' ht at`
       (mp_tac o MATCH_MP ptr_chrono_history_end) >>
     strip_tac >> Cases_on `ht` >> gvs[LAST_EL]) >>
  `read_byte x endpoint.po_state.vs_memory =
    read_byte x (EL (SUC w) h).po_state.vs_memory` by
    (`read_byte x (EL (LENGTH h-1) h).po_state.vs_memory =
      read_byte x (EL (SUC w) h).po_state.vs_memory` suffices_by simp[] >>
     irule ptr_chrono_history_actual_interval_byte_frame >>
     conj_tac >- (rpt strip_tac >>
       qpat_x_assum `!n. w < n /\ SUC n < LENGTH h ==> _`
         (qspec_then `k` mp_tac) >> simp[] >> decide_tac) >>
     simp[] >> metis_tac[]) >>
  `read_byte x at.po_state.vs_memory =
    read_byte x (EL (SUC q) ht).po_state.vs_memory` by
    (`read_byte x (EL (LENGTH ht-1) ht).po_state.vs_memory =
      read_byte x (EL (SUC q) ht).po_state.vs_memory` suffices_by simp[] >>
     irule ptr_chrono_history_actual_interval_byte_frame >>
     conj_tac >- simp[] >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Finalise ptr_paired_fixed_read_recovery
