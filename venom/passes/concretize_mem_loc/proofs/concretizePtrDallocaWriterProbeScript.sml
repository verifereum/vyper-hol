Theory concretizePtrDallocaWriterProbe
Ancestors
  concretizePtrHistoricalWriteExclusion concretizePtrDemandWriteExclusion
  concretizePtrDallocaWriterTaint concretizePtrLifetime
  concretizePtrChronologicalHistory concretizePtrStructuralTranscript
  concretizePtrStructuralTrace
  list rich_list arithmetic

(* Retention is occurrence-preserving. The recursive copy read will be at
   source index w, strictly before the demanded endpoint LENGTH h - 1. *)
Theorem ptr_dalloca_demand_writer_index:
  ptr_demand_interval R vs C C' h endpoint ht at done tokens registry births
    PT TG saved entries H lo P d aid b sz k v token fn bp mems observed
    rpolicy s out names w ==>
  ?q. q < LENGTH done /\ EL q done = w /\ w < LENGTH h - 1
Proof
  strip_tac >>
  `ptr_structural_transcript R vs C C' h endpoint ht at done tokens registry
     births PT TG saved entries H /\
   SUC w < LENGTH h /\
   b+k IN range_bytes (step_writes (EL w h).po_inst (EL w h).po_state
     (EL (SUC w) h).po_state)` by fs[ptr_demand_interval_def] >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_actual_writer_retained >>
  disch_then (qspecl_then [`w`, `b+k`] mp_tac) >> simp[] >> strip_tac >>
  qexists `q` >> simp[] >> decide_tac
QED

Theorem ptr_dalloca_demand_writer_source_edge:
  ptr_demand_interval R vs C C' h endpoint ht at done tokens registry births
    PT TG saved entries H lo P d aid b sz k v token fn bp mems observed
    rpolicy s out names w ==>
  ptr_chrono_step C (EL w h) (EL (SUC w) h) /\
  b+k NOTIN (EL (SUC w) h).po_taint.t_mem
Proof
  strip_tac >>
  `ptr_structural_transcript R vs C C' h endpoint ht at done tokens registry
     births PT TG saved entries H /\ SUC w < LENGTH h /\
   b+k NOTIN (EL (SUC w) h).po_taint.t_mem` by fs[ptr_demand_interval_def] >>
  simp[] >> drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_source >>
  disch_then (mp_tac o MATCH_MP ptr_chrono_history_adjacent) >>
  disch_then (qspec_then `w` mp_tac) >> simp[]
QED

(* UNPROVED production obligation (diagnostic only, not a theorem):
   ptr_dalloca_writer_geometry_probe:
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  ptr_demand_interval R vs C C' h endpoint ht at done tokens registry births
    PT TG saved entries H lo P d aid b sz k v token fn bp mems observed
    rpolicy s out names w /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\ (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\
  q < LENGTH done /\ EL q done = w ==>
  pa+k IN range_bytes (step_writes (EL q ht).po_inst (EL q ht).po_state
    (EL (SUC q) ht).po_state)

   The probe reaches precisely this coverage conclusion after applying
   ptr_paired_historical_event. That event supplies source access_ok and
   taint_ok, mixed variables, content agreement, and instruction rewriting;
   none of these alone is a forward write-coverage theorem.

   ptr_ordinary_write_operand_transport cannot discharge it: its final
   premise already assumes target write coverage. The historical exclusion
   API only applies at j>w, not at the initializing writer j=w.

   Further obligations for WriterTaint's store/copy interfaces, using
     inst=(EL w h).po_inst, instT=(EL q ht).po_inst,
     src=(EL w h).po_state, tgt=(EL q ht).po_state,
     tn=(EL w h).po_taint, un=(EL q ht).po_taint:
   - For stores with operands [a;value] and [aT;valueT], produce evaluations
     a/src=SOME dst and aT/tgt=SOME dstT and a common offset off<32 with
       b+k = w2n dst+off /\ pa+k = w2n dstT+off.
     The incoming ghost induction must supply
       op_taint un valueT SUBSET op_taint tn value.
   - For MCOPY, produce destination/source/size evaluations dst,r,len and
     dstT,rT,lenT and an offset off with
       off<w2n len /\ off<w2n lenT /\
       b+k=w2n dst+off /\ pa+k=w2n dstT+off.
     The earlier-read induction obligation is exactly
       w2n rT+off IN (EL q ht).po_taint.t_mem ==>
       w2n r+off IN (EL w h).po_taint.t_mem.
     It must be justified as an input read demand at observation w; it
     cannot be obtained from state-content equality. The checked index
     lemma above gives EL q done=w and w<LENGTH h-1, the strict decrease
     needed by a source-history induction. A production theorem must also
     classify this read byte as fixed, dynamic or an owned relocated byte.
   - WriterTaint takes actual step_taint post states. A successful ordinary
     step and the corresponding chronological taint-update equation must
     be exposed before applying it to the next observation; no identity
     between actual post and next-observation states is assumed here.

   This theory checks writer retention and the source edge only. It does
   not assert target coverage, equal offsets, or ghost-taint inclusion.
*)
