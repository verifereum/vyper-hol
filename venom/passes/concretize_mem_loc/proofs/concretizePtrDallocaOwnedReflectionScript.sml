Theory concretizePtrDallocaOwnedReflection
Ancestors
  concretizePtrDallocaMemoryProbe concretizePtrStagePlacements
  concretizePtrSourceOwnership concretizePtrOwnerFloor concretizePtrImportOrigins
  concretizePtrHistoricalWriteExclusion concretizeLayoutAccessGeometry
  concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrPairedPrefix concretizePtrOwnerPath
  concretizePtrChronologicalHistory ptrDiscipline rich_list unitTransformDefs
  o1PassContract unitShapeDefs venomWf finite_map list pred_set arithmetic
  frameAllocationOwnership o1ScheduleDecompHelpers concretizePtrDemandWriteExclusion

Theorem ptr_dalloca_owned_demand:
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  FLOOKUP TG v = SOME (token,aid) /\
  FLOOKUP endpoint.po_prov v = SOME (b,sz) /\
  FLOOKUP births (token,aid) = SOME (b,sz) /\
  FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\ k < sz /\
  b+k NOTIN endpoint.po_taint.t_mem /\
  ~in_revert_forward endpoint.po_fn endpoint.po_state /\
  endpoint.po_inst.inst_opcode <> ASSIGN /\
  MEM (Var v) endpoint.po_inst.inst_operands /\
  (inst_read_op endpoint.po_inst = SOME (Var v) \/ endpoint.po_inst.inst_opcode = INVOKE) ==>
  (?P d fn bp mems observed s out w.
    ptr_demand_interval R vs C C' h endpoint ht at done tokens registry births
      PT TG saved entries H lo P d aid b sz k v token fn bp mems observed
      rpolicy s out names w) \/ dyn_floor C vs <= b+k
Proof
  strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_paired_prefix_placements >> strip_tac >>
  drule ptr_structural_transcript_endpoint >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_source >> strip_tac >>
  `ptr_source_ownership vs C h endpoint tokens registry births PT TG saved` by
    metis_tac[ptr_structural_trace_ownership] >>
  drule_all ptr_stage_placements_live_owner >> strip_tac >>
  `ptr_observation_reachable vs C endpoint` by
    metis_tac[ptr_chrono_history_reachable, ptr_chrono_history_end, MEM_LAST] >>
  `lo <= b+k` by
    (drule_all ptr_reachable_owner_allocas_from >>
     simp[allocas_from_def] >> strip_tac >> first_x_assum drule >> decide_tac) >>
  drule_all ptr_stage_lookup_origin >> strip_tac >>
  `EVERY wf_function C.ctx_functions /\ EVERY fn_inst_wf C.ctx_functions` by
    gvs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (simp[Once EVERY_MEM] >> gen_tac >> strip_tac >>
     irule ptr_fn_inst_wf_flat >> fs[EVERY_MEM]) >>
  `vs.vs_allocas = FEMPTY` by fs[o1_run_state_ok_def, o1_initial_state_ok_def] >>
  qpat_assum `ptr_discipline lo C vs` mp_tac >>
  pure_rewrite_tac[ptr_discipline_def] >> strip_tac >>
  `EVERY (fn_ptr_ok P) C.ctx_functions` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `!obs. MEM obs h ==> access_ok lo obs.po_prov obs.po_fn obs.po_inst obs.po_state` by
    (rpt strip_tac >>
     drule ptr_chrono_history_reachable >> simp[EVERY_MEM] >>
     disch_then drule >> simp[ptr_observation_reachable_def] >> metis_tac[]) >>
  `MEM owner C.ctx_functions` by
    (fs[ptr_observation_reachable_def] >>
     drule frame_reachable_functions_member >> strip_tac >>
     Cases_on `d = LENGTH endpoint.po_stack`
     >- gvs[ptr_owner_view_def] >>
     `MEM (ptr_owner_view d endpoint) endpoint.po_stack` by
       (simp[ptr_owner_view_def] >> irule EL_MEM >> decide_tac) >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  `lookup_function owner.fn_name C.ctx_functions = SOME owner` by
    (irule (iffRL lookup_function_member_iff) >>
     gvs[o1_ctx_shape_def, ctx_wf_def, ctx_distinct_fn_names_def, venomInstTheory.ctx_fn_names_def]) >>
  `fn = owner` by metis_tac[optionTheory.SOME_11] >>
  gvs[] >>
  qabbrev_tac `bp = bp_analyze_fuel
    (concretize_memloc_fuel (ptr_owner_view d endpoint).cf_fn)
    (cfg_analyze (ptr_owner_view d endpoint).cf_fn) (ptr_owner_view d endpoint).cf_fn` >>
  qabbrev_tac `mems = (\nm. incr_ssort alloc_to
    (MAP FST (callee_mems_used observed.cu_context nm)))` >>
  drule ptr_demand_interval_exists >>
  simp[Abbr `bp`, Abbr `mems`] >> metis_tac[]
QED

(* The writer contract is conditional: the history join discharges it using
   the simultaneous earlier-index reflection clauses. It is not a stage
   precondition. Quantifying all analysis witnesses avoids exposing choices
   made by the demand producer to that join. *)
Theorem ptr_dalloca_owned_demand_reflection:
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  FLOOKUP TG v = SOME (token,aid) /\
  FLOOKUP endpoint.po_prov v = SOME (b,sz) /\
  FLOOKUP births (token,aid) = SOME (b,sz) /\
  FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\ k < sz /\
  ~in_revert_forward endpoint.po_fn endpoint.po_state /\
  endpoint.po_inst.inst_opcode <> ASSIGN /\
  MEM (Var v) endpoint.po_inst.inst_operands /\
  (inst_read_op endpoint.po_inst = SOME (Var v) \/ endpoint.po_inst.inst_opcode = INVOKE) /\
  (!P d fn bp mems observed s out w.
    ptr_demand_interval R vs C C' h endpoint ht at done tokens registry births
      PT TG saved entries H lo P d aid b sz k v token fn bp mems observed
      rpolicy s out names w ==> pa+k NOTIN at.po_taint.t_mem) ==>
  pa+k IN at.po_taint.t_mem ==> b+k IN endpoint.po_taint.t_mem
Proof
  strip_tac >> strip_tac >> spose_not_then assume_tac >>
  `dyn_floor C vs <= b+k` by
    (drule ptr_dalloca_owned_demand >> simp[] >> metis_tac[]) >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_paired_prefix_placements >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  `ptr_source_ownership vs C h endpoint tokens registry births PT TG saved` by
    metis_tac[ptr_structural_trace_ownership] >>
  drule_all ptr_stage_placements_live_owner >> strip_tac >>
  `ptr_observation_reachable vs C endpoint` by
    (drule ptr_structural_trace_source >> strip_tac >>
     metis_tac[ptr_chrono_history_reachable, ptr_chrono_history_end, MEM_LAST]) >>
  `EVERY wf_function C.ctx_functions /\ vs.vs_allocas = FEMPTY` by
    gvs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM,
      o1_run_state_ok_def, o1_initial_state_ok_def] >>
  drule_all ptr_reachable_owner_below_dyn_floor >> decide_tac
QED
