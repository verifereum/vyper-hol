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
    ptr_paired_write_owner (dyn_floor C (EL w h).po_state) lo positions rho
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
  EVERY ssa_form C.ctx_functions /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\ (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  (x < lo \/ dyn_floor C vs <= x) /\ x NOTIN endpoint.po_taint.t_mem /\
  ~in_revert_forward endpoint.po_fn endpoint.po_state /\
  endpoint.po_inst.inst_opcode <> ASSIGN ==>
  read_byte x endpoint.po_state.vs_memory = read_byte x at.po_state.vs_memory
Proof
  cheat
QED
