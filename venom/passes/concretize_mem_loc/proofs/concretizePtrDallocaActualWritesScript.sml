Theory concretizePtrDallocaActualWrites
Ancestors
  concretizePtrDallocaWriterGeometry concretizePtrHistoricalWriteClassification
  concretizePtrExactWriteTransport concretizePtrStageReserved concretizePtrStageBounds
  concretizePtrOwnerFloor concretizePtrSourceOwnership concretizePtrMloadEndpoint
  concretizePtrPlacementBounds concretizePtrWriteClassification venomInst
  concretizePtrHistoricalWriteExclusion concretizePtrStructuralTranscript
  concretizePtrStructuralTrace concretizePtrTaggedSupport concretizePtrPairedPrefix
  concretizeStepStructure concretizeMemLocDefs codegenRel passSharedDefs
  ptrDiscipline o1PassContract venomWf memLocDefs venomState
  list finite_map words arithmetic pred_set

(* Both the original live static allocation and its placement are strictly
   between the fixed and dynamic identity bands. *)
Theorem ptr_dalloca_live_owner_bands:
  ptr_source_ownership vs C h a tokens registry births PT TG saved /\
  ptr_observation_reachable vs C a /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\ o1_ctx_shape C /\
  callee_first names C.ctx_functions /\ ptr_discipline lo C vs /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ vs.vs_allocas = FEMPTY /\
  ptr_stage_placements C' positions /\ max_live_eom C' = SOME eom /\
  (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  FLOOKUP TG v = SOME (token,aid) /\ FLOOKUP a.po_prov v = SOME (b,sz) /\
  FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\ sz <> 0 ==>
  lo <= b /\ b+sz <= dyn_floor C vs /\ lo <= pa /\ pa+sz <= dyn_floor C vs
Proof
  strip_tac >>
  `EVERY wf_function C.ctx_functions /\
   EVERY (\fn. EVERY inst_wf (fn_insts fn)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_inst_wf_def,
        fn_insts_def, fn_insts_blocks_MEM, EVERY_MEM] >> metis_tac[]) >>
  drule_all ptr_source_ownership_live_cache >> strip_tac >>
  `allocas_from lo (ptr_owner_view d a).cf_state` by
    (drule_all ptr_reachable_owner_allocas_from >> simp[]) >>
  `lo <= b` by (fs[allocas_from_def] >> metis_tac[]) >>
  `b+sz <= dyn_floor C vs` by
    (drule_all ptr_reachable_owner_below_dyn_floor >> simp[]) >>
  `lo <= pa+0` by
    (irule ptr_stage_placements_reserved_prefix >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `pa+sz <= eom /\ pa+sz < dimword(:256)` by
    metis_tac[ptr_stage_placements_endpoint_bound, ptr_stage_placements_strict_bound] >>
  simp[] >> simp[dyn_floor_def] >> IF_CASES_TAC >> gvs[] >> decide_tac
QED

(* This arithmetic boundary uses the common actual write lengths, including
   the MIN with the returned-data length for external calls. *)
Theorem ptr_dalloca_write_band_geometry:
  mem_write_ops inst = SOME ops /\ ops.iao_max_size = SOME sizeop /\
  eval_operand ops.iao_ofst s = SOME x /\ eval_operand ops.iao_ofst t = SOME y /\
  eval_operand sizeop s = SOME z /\ eval_operand sizeop t = SOME z /\
  (!op. IS_SOME (eval_operand op s) = IS_SOME (eval_operand op t)) /\
  (MEM inst.inst_opcode [CALL;STATICCALL;DELEGATECALL] ==>
    LENGTH posts.vs_returndata = LENGTH postt.vs_returndata) /\
  (x = y \/ (lo <= w2n x /\ w2n x+w2n z <= dyn /\
             lo <= w2n y /\ w2n y+w2n z <= dyn)) /\
  (i < lo \/ dyn <= i) ==>
  (i IN range_bytes (step_writes inst s posts) <=>
   i IN range_bytes (step_writes inst t postt)) /\
  (i IN range_bytes (step_writes inst t postt) ==> x = y)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> Cases_on `x = y`
  >- (gvs[] >> drule_all (SRULE [MEM] ptr_paired_write_intervals) >> strip_tac >> metis_tac[]) >>
  `!q. q IN range_bytes (step_writes inst s posts) ==> w2n x <= q /\ q < w2n x+w2n z` by
    (metis_tac[ptr_step_write_max_containment]) >>
  `!q. q IN range_bytes (step_writes inst t postt) ==> w2n y <= q /\ q < w2n y+w2n z` by
    (metis_tac[ptr_step_write_max_containment]) >>
  first_x_assum (qspec_then `i` assume_tac) >>
  first_x_assum (qspec_then `i` assume_tac) >> gvs[] >> decide_tac
QED

Theorem ptr_dalloca_actual_event_context:
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom C' = SOME eom /\
  q < LENGTH done /\ a = EL (EL q done) h /\ t = EL q ht /\
  ~in_revert_forward a.po_fn a.po_state ==>
  ?P tsj rj bj PTj TGj sj ej.
    EL (EL q done) H = (tsj,rj,bj,PTj,TGj,sj,ej) /\
    ptr_source_ownership vs C (TAKE (SUC (EL q done)) h) a tsj rj bj PTj TGj sj /\
    ptr_observation_reachable vs C a /\
    ptr_mixed_vars bj positions TGj a.po_taint a.po_fn t.po_fn a.po_state t.po_state /\
    a.po_state.vs_labels = t.po_state.vs_labels /\
    fn_ptr_ok P a.po_fn /\ opaque_use_ok a.po_fn /\ MEM a.po_inst (fn_insts a.po_fn) /\
    taint_ok a.po_fn a.po_taint a.po_inst a.po_state /\
    access_ok lo a.po_prov a.po_fn a.po_inst a.po_state /\
    label_positions_ok a.po_inst /\ a.po_inst.inst_opcode <> DRET /\
    (!u. u IN FDOM TGj ==> u IN fn_pv P a.po_fn) /\
    t.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
    (EL (SUC (EL q done)) h).po_state.vs_returndata =
      (EL (SUC q) ht).po_state.vs_returndata
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~in_revert_forward (EL (EL q done) h).po_fn (EL (EL q done) h).po_state` by metis_tac[] >>
  drule_all ptr_paired_historical_event >> strip_tac >>
  `ptr_source_ownership vs C (TAKE (SUC (EL q done)) h)
    (EL (EL q done) h) tsj rj bj PTj TGj sj` by
    (drule ptr_structural_transcript_ownership >>
     disch_then (qspec_then `EL q done` mp_tac) >>
     simp[ptr_snapshot_ownership_def]) >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    (fs[ptr_discipline_def, EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_inst_wf_def,
        fn_insts_def, fn_insts_blocks_MEM, EVERY_MEM] >> metis_tac[]) >>
  drule_all ptr_dalloca_writer_instruction_facts >> strip_tac >>
  `(EL (EL q done) h).po_state.vs_labels = (EL q ht).po_state.vs_labels` by
    metis_tac[concretizePtrRequestHistoryTheory.ptr_history_content_labels] >>
  `!u. u IN FDOM TGj ==> u IN fn_pv P (EL (EL q done) h).po_fn` by
    (rpt strip_tac >>
     `?tag. FLOOKUP TGj u = SOME tag` by metis_tac[FLOOKUP_DEF] >>
     drule_all ptr_source_tagged_var_support >> simp[]) >>
  `(EL (SUC (EL q done)) h).po_state.vs_returndata =
    (EL (SUC q) ht).po_state.vs_returndata` by
    (drule ptr_paired_prefix_samples >> strip_tac >>
     drule ptr_structural_transcript_erasure >> strip_tac >>
     drule_all ptr_paired_samples_post_returndata >> simp[]) >>
  rpt (goal_assum (drule_at Any)) >> gvs[] >> metis_tac[]
QED

Theorem ptr_dalloca_written_instruction:
  instT = concretize_inst_with_positions positions inst /\
  (i IN range_bytes (step_writes inst s posts) \/
   i IN range_bytes (step_writes instT t postt)) ==>
  inst.inst_opcode <> ALLOCA /\ instT = inst
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> Cases_on `inst.inst_opcode = ALLOCA`
  >- (Cases_on `inst.inst_outputs` >>
      gvs[concretize_inst_with_positions_def, AllCaseEqs()] >>
      gvs[AllCaseEqs(), mk_assign_inst_def, mk_nop_inst_def,
          ptr_step_write_range, source_memory_write_ranges_def]) >>
  simp[concretize_positions_unchanged]
QED

(* Source and target extraction share a single descriptor.  The taint of
   the value being stored is deliberately not constrained here. *)
Theorem ptr_dalloca_two_sided_write_operands:
  ptr_mixed_vars births positions TG tn fn ft src tgt /\
  src.vs_labels = tgt.vs_labels /\
  fn_ptr_ok P fn /\ opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  taint_ok fn tn inst src /\ label_positions_ok inst /\ inst.inst_opcode <> DRET /\
  (!u. u IN FDOM TG ==> u IN fn_pv P fn) /\
  (q IN range_bytes (step_writes inst src posts) \/
   q IN range_bytes (step_writes inst tgt postt)) ==>
  ?ops sizeop x z xt.
    mem_write_ops inst = SOME ops /\ ops.iao_max_size = SOME sizeop /\
    eval_operand ops.iao_ofst src = SOME x /\ eval_operand sizeop src = SOME z /\
    MEM (w2n x,w2n z) (source_memory_write_ranges inst src) /\
    eval_operand ops.iao_ofst tgt = SOME xt /\ eval_operand sizeop tgt = SOME z /\
    ptr_lookup_transport births positions (op_prov TG ops.iao_ofst)
      (op_taint tn ops.iao_ofst) (eval_operand ops.iao_ofst src)
      (eval_operand ops.iao_ofst tgt) /\ w2n z <> 0 /\
    (!op. IS_SOME (eval_operand op src) = IS_SOME (eval_operand op tgt))
Proof
  strip_tac
  >- (drule_all ptr_dalloca_forward_write_operands >> metis_tac[]) >>
  drule_all ptr_ordinary_write_operand_transport >> metis_tac[]
QED

Theorem ptr_dalloca_owned_destination_band:
  ptr_source_ownership vs C h a tokens registry births PT TG saved /\
  ptr_observation_reachable vs C a /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\ o1_ctx_shape C /\
  callee_first names C.ctx_functions /\ ptr_discipline lo C vs /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ vs.vs_allocas = FEMPTY /\
  ptr_stage_placements C' positions /\ max_live_eom C' = SOME eom /\
  (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  FLOOKUP TG v = SOME (token,aid) /\ FLOOKUP a.po_prov v = SOME (b,sz) /\
  FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\
  b <= w2n x /\ w2n x+w2n z <= b+sz /\ w2n z <> 0 /\
  ptr_lookup_transport births positions (SOME (token,aid)) mask (SOME x) (SOME y) ==>
  lo <= w2n x /\ w2n x+w2n z <= dyn_floor C vs /\
  lo <= w2n y /\ w2n y+w2n z <= dyn_floor C vs
Proof
  strip_tac >>
  `sz <> 0` by decide_tac >>
  drule_all ptr_dalloca_live_owner_bands >> strip_tac >>
  `EVERY (\fn. EVERY inst_wf (fn_insts fn)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_inst_wf_def,
        fn_insts_def, fn_insts_blocks_MEM, EVERY_MEM] >> metis_tac[]) >>
  `FLOOKUP births (token,aid) = SOME (b,sz)` by
    (drule_all ptr_source_ownership_prov_erases >>
     simp[concretizePtrPrefixLedgerTheory.ptr_ledger_erases_def] >>
     strip_tac >>
     qpat_x_assum `!v. ptr_owner_erases _ _ _ _` (qspec_then `v` mp_tac) >>
     simp[concretizePtrPrefixLedgerTheory.ptr_owner_erases_def]) >>
  `pa+sz < dimword(:256)` by metis_tac[ptr_stage_placements_strict_bound] >>
  `y = x - n2w b + n2w pa` by
    gvs[concretizePtrValueTransportTheory.ptr_lookup_transport_some,
        concretizePtrValueTransportTheory.ptr_value_transport_def] >>
  `w2n y = pa + (w2n x-b)` by
    (asm_rewrite_tac[] >> irule concretizePtrComparisonTransportTheory.ptr_closed_relocation_value >>
     simp[] >> qexists `sz` >> simp[] >> decide_tac) >>
  decide_tac
QED

Theorem ptr_dalloca_actual_write_descriptor:
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom C' = SOME eom /\
  (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  q < LENGTH done /\ a = EL (EL q done) h /\ t = EL q ht /\
  posts = (EL (SUC (EL q done)) h).po_state /\
  postt = (EL (SUC q) ht).po_state /\
  ~in_revert_forward a.po_fn a.po_state /\
  (i < lo \/ dyn_floor C vs <= i) /\
  (i IN range_bytes (step_writes a.po_inst a.po_state posts) \/
   i IN range_bytes (step_writes t.po_inst t.po_state postt)) ==>
  t.po_inst = a.po_inst /\
  ?ops sizeop x z.
    mem_write_ops a.po_inst = SOME ops /\ ops.iao_max_size = SOME sizeop /\
    eval_operand ops.iao_ofst a.po_state = SOME x /\
    eval_operand ops.iao_ofst t.po_state = SOME x /\
    eval_operand sizeop a.po_state = SOME z /\
    eval_operand sizeop t.po_state = SOME z /\
    (!op. IS_SOME (eval_operand op a.po_state) = IS_SOME (eval_operand op t.po_state)) /\
    (MEM a.po_inst.inst_opcode [CALL;STATICCALL;DELEGATECALL] ==>
      LENGTH posts.vs_returndata = LENGTH postt.vs_returndata)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ptr_dalloca_actual_event_context >> strip_tac >>
  `t.po_inst = a.po_inst` by
    (drule_all ptr_dalloca_written_instruction >> simp[]) >>
  qpat_x_assum `_ IN range_bytes _ \/ _ IN range_bytes _` mp_tac >>
  pure_once_rewrite_tac[] >> disch_tac >> gns[] >>
  drule_all ptr_dalloca_two_sided_write_operands >> strip_tac >>
  drule_all ptr_paired_historical_event >> strip_tac >>
  `EL q done < LENGTH h /\ vs.vs_allocas = FEMPTY` by
    (gns[o1_run_state_ok_def, unitTransformDefsTheory.o1_initial_state_ok_def] >> decide_tac) >>
  Q.SUBGOAL_THEN `op_prov TGj ops.iao_ofst = NONE /\ op_taint a.po_taint ops.iao_ofst = {} \/
   (?v token aid b sz pa. ops.iao_ofst = Var v /\
     FLOOKUP TGj v = SOME (token,aid) /\ FLOOKUP a.po_prov v = SOME (b,sz) /\
     FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\
     b <= w2n x /\ w2n x+w2n z <= b+sz)` assume_tac
  >- (drule_all ptr_historical_write_classification >> gvs[] >> metis_tac[]) >>
  Q.SUBGOAL_THEN `x = xt \/ (lo <= w2n x /\ w2n x+w2n z <= dyn_floor C vs /\
              lo <= w2n xt /\ w2n xt+w2n z <= dyn_floor C vs)` assume_tac
  >-
    (pop_assum strip_assume_tac
     >- gvs[concretizePtrValueTransportTheory.ptr_lookup_transport_some,
            concretizePtrValueTransportTheory.ptr_value_transport_scalar_empty] >>
     disj2_tac >>
     `ptr_lookup_transport bj positions (SOME (token,aid))
       (op_taint a.po_taint ops.iao_ofst) (SOME x) (SOME xt)` by
       (gvs[op_prov_def]) >>
     gns[] >> drule_all (SRULE [] ptr_dalloca_owned_destination_band) >> simp[]) >>
  `x = xt` by
    (Cases_on `x = xt` >- simp[] >>
     `!j. j IN range_bytes (step_writes a.po_inst a.po_state posts) ==>
       w2n x <= j /\ j < w2n x+w2n z` by
       (gns[] >> metis_tac[ptr_step_write_max_containment]) >>
     `!j. j IN range_bytes (step_writes a.po_inst t.po_state postt) ==>
       w2n xt <= j /\ j < w2n xt+w2n z` by
       (gns[] >> metis_tac[ptr_step_write_max_containment]) >>
     ntac 2 (first_x_assum (qspec_then `i` assume_tac)) >> gvs[] >> decide_tac) >>
  simp[]
QED
