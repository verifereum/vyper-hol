Theory readonlyInvokeCopyFwdExecutionWriteGuards
Ancestors
  readonlyInvokeCopyFwdExecutionWriteClassification readonlyInvokeCopyFwdAnalyzedOrigins
  readonlyInvokeCopyFwdExecutionHistory readonlyInvokeCopyFwdExecution
  readonlyInvokeCopyFwdHeterogeneousLedger readonlyInvokeCopyFwdAlignedOrigins
  readonlyInvokeCopyFwdHistoryPhase invokeCopyFwdCommonDefs
  o1LowerDloadOccurrence occurrenceGeometry ptrDiscipline
  list rich_list pred_set arithmetic

Theorem ricf_saved_phase_range_origin[local]:
  MEM gam (ricf_phase_stack_ranges stk certificates) /\
  (db,sb,sz) IN gam ==>
  ?p frames. MEM (p,frames) certificates /\ frames <> [] /\
    db = p.rpe_db /\ sb = p.rpe_sb /\ sz = p.rpe_size
Proof
  simp[ricf_phase_stack_ranges_def, MEM_GENLIST, ricf_phase_ranges_def] >>
  rpt strip_tac >> gvs[] >> qexistsl_tac [`p`,`pre`] >>
  simp[] >> Cases_on `pre` >> fs[]
QED

Theorem ricf_execution_saved_phase_write_ranges:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H certificates E sites maps targets tn /\
  ricf_certificate_readonly vs C log_of stk PG G tn fn inst s U B certificates /\
  o1_ctx_shape C /\ ALL_DISTINCT (MAP (\f. f.fn_name) C.ctx_functions) /\
  EVERY wf_ssa C.ctx_functions /\ EVERY ricf_param_order_ok C.ctx_functions /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ptr_discipline lo C vs /\ ~in_revert_forward fn s /\
  MEM (off,len) (source_memory_write_ranges inst s) /\
  MEM gam (ricf_phase_stack_ranges stk certificates) /\
  (db,sb,sz) IN gam /\ k < sz ==>
  ~(off <= db+k /\ db+k < off+len) /\
  ~(off <= sb+k /\ sb+k < off+len)
Proof
  strip_tac >> drule_all ricf_saved_phase_range_origin >>
  disch_then (qx_choosel_then [`p`,`frames`] strip_assume_tac) >>
  `occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H` by
    fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
  `occurrence_natural_geometry lo a U B stk s /\
   occurrence_env_ok B (a::MAP (\u. u.of_owner) U) H G /\ access_ok lo G fn inst s` by
    (drule occ_frame_reachable_annotation >>
     simp[occurrence_annotation_ok_def] >> strip_tac >>
     metis_tac[occ_frame_reachable_geometry, ptr_discipline_def,
       occ_frame_reachable_projection]) >>
  `ricf_aligned_translation_origin vs C
     (icf_build_ctx (icf_fn_meta_of C) C.ctx_functions
       (readonly_mem_analyze C) p.rpe_fn) (log_of p.rpe_fn)
     stk PG G tn fn inst s U B (db,sz) (db,sb,sz)` by
    (fs[ricf_certificate_readonly_def] >>
     first_x_assum (qspecl_then [`p`,`frames`] mp_tac) >> simp[] >>
     strip_tac >> simp[ricf_aligned_translation_origin_def] >>
     metis_tac[]) >>
  `(icf_build_ctx (icf_fn_meta_of C) C.ctx_functions
      (readonly_mem_analyze C) p.rpe_fn).icf_rma = readonly_mem_analyze C` by
    simp[icf_build_ctx_def] >>
  metis_tac[ricf_analyzed_translation_origin_write_ranges]
QED

Theorem ricf_execution_write_ranges:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H certificates E sites maps targets tn /\
  ricf_analyzed_origins vs C stk PG G tn fn inst s a U B certificates sites maps /\
  ricf_certificate_readonly vs C log_of stk PG G tn fn inst s U B certificates /\
  o1_ctx_shape C /\ ALL_DISTINCT (MAP (\f. f.fn_name) C.ctx_functions) /\
  EVERY wf_ssa C.ctx_functions /\ EVERY ricf_param_order_ok C.ctx_functions /\
  EVERY wf_function C.ctx_functions /\ EVERY fn_inst_wf C.ctx_functions /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ptr_discipline lo C vs /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  MEM (off,len) (source_memory_write_ranges inst s) /\
  (gam = ricf_phase_ranges 0 certificates \/
    MEM gam (ricf_phase_stack_ranges stk certificates) \/
    gam = ricf_site_triples sites \/
    ?j. j < LENGTH stk /\ gam = ricf_site_triples (EL j maps)) /\
  (db,sb,sz) IN gam /\ k < sz ==>
  ~(off <= db+k /\ db+k < off+len) /\
  ~(off <= sb+k /\ sb+k < off+len)
Proof
  strip_tac >>
  `ricf_analyzed_map_origins vs C stk PG G tn fn inst s U B sites /\
   ricf_analyzed_saved_map_origins vs C stk PG G tn fn inst s U B maps` by
    fs[ricf_analyzed_origins_def] >>
  metis_tac[ricf_execution_current_phase_write_ranges,
    ricf_execution_saved_phase_write_ranges, ricf_execution_map_write_ranges]
QED
