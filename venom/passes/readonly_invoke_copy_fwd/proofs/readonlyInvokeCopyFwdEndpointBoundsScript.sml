Theory readonlyInvokeCopyFwdEndpointBounds
Ancestors
  readonlyInvokeCopyFwdOperationalSupport readonlyInvokeCopyFwdHistoryOrigin
  readonlyInvokeCopyFwdProtectionOrigin readonlyInvokeCopyFwdHistory
  o1LowerDloadRawBridge o1LowerDloadStackFrontier o1LowerDloadOccurrence
  unitMemInv venomMemDefs ptrDiscipline contextCodegenRel
  venomInst venomState finite_map list words

Theorem ricf_history_origin_endpoint_bounds:
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  EVERY wf_function C.ctx_functions /\ mem_inv raw_mem_ok C vs /\
  ricf_history_origin vs C ctx0 log p stk PG G tn ==>
  p.rpe_db + p.rpe_size < dimword (:256) /\
  p.rpe_sb + p.rpe_size < dimword (:256)
Proof
  simp[ricf_history_origin_def, ricf_source_copy_payload_def] >>
  rpt strip_tac >>
  `frame_reachable vs C stk PG G tn p.rpe_fn
    (ricf_event_copy p.rpe_event p.rpe_block) p.rpe_before` by
    metis_tac[occ_frame_reachable_projection] >>
  `active_inst p.rpe_fn (ricf_event_copy p.rpe_event p.rpe_block) p.rpe_before` by
    (qpat_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
     gvs[Once frame_reachable_cases] >> metis_tac[]) >>
  `!name f. lookup_function name C.ctx_functions = SOME f ==> wf_function f` by
    (rpt strip_tac >> fs[EVERY_MEM] >> metis_tac[lookup_function_MEM]) >>
  `ld_raw_stack vs C stk p.rpe_fn p.rpe_before` by
    metis_tac[ld_frame_raw_stack] >>
  `raw_reachable vs C p.rpe_fn (ricf_event_copy p.rpe_event p.rpe_block)
    p.rpe_before` by metis_tac[ld_raw_stack_active] >>
  `p.rpe_before.vs_alloca_next < dimword (:256)` by
    (fs[mem_inv_raw_reachable, raw_mem_ok_def] >> metis_tac[]) >>
  `alloca_inv p.rpe_before` by
    metis_tac[ld_frame_reachable_current_alloca_inv] >>
  `occurrence_annotation_ok n p.rpe_owner U B HP H stk PG G p.rpe_before` by
    metis_tac[occ_frame_reachable_annotation] >>
  `FLOOKUP p.rpe_before.vs_allocas (SND p.rpe_dst) = SOME (p.rpe_db,p.rpe_size) /\
   FLOOKUP p.rpe_before.vs_allocas (SND p.rpe_src) = SOME (p.rpe_sb,p.rpe_size)` by
    (fs[occurrence_annotation_ok_def, occurrence_allocas_ok_def] >>
     metis_tac[pairTheory.PAIR]) >>
  fs[alloca_inv_def, alloca_next_valid_def] >>
  metis_tac[arithmeticTheory.LESS_EQ_LESS_TRANS]
QED

Theorem ricf_translation_origin_endpoint_bounds:
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  EVERY wf_function C.ctx_functions /\ mem_inv raw_mem_ok C vs /\
  ricf_translation_origin vs C ctx0 log stk PG G tn fn inst s U B
    (db,sz) (db,sb,sz) ==>
  db + sz < dimword (:256) /\ sb + sz < dimword (:256)
Proof
  simp[ricf_translation_origin_def, ricf_history_cursor_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[ricf_history_origin_endpoint_bounds]
QED
