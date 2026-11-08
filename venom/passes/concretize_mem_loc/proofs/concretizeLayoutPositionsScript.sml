Theory concretizeLayoutPositions
Ancestors
  concretizeAnalysisRuntimeItems concretizeLayoutNumericSchedule
  concretizeLayoutMetadataSchedule concretizeAnalysisMetadataSchedule
  concretizeAnalysisMetadataOwnership concretizeLayoutMetadata
  concretizeAnalysisCollection staticLayoutAllocatorProofs
  ctxLookupAgreeHelpers contextCodegenRel o1PassContract o1ScheduleDecomp o1ScheduleDecompHelpers
  venomWf venomInst ptrDiscipline staticLayoutDefs frameJointTrace list pair finite_map words

Definition concretize_positions_def:
  concretize_positions C' owner aid =
    case lookup_function owner.fn_name C'.ctx_functions of
      NONE => 0
    | SOME out =>
        case FIND (\(a,p,sz). a = Allocation aid) out.fn_mems_used of
          NONE => 0
        | SOME (a,p,sz) => p
End

Theorem concretize_positions_lookup:
  lookup_function owner.fn_name C'.ctx_functions = SOME out /\
  FIND (\(a,p,sz). a = Allocation aid) out.fn_mems_used =
    SOME (Allocation aid,p,sz) ==>
  concretize_positions C' owner aid = p
Proof
  simp[concretize_positions_def]
QED

Theorem concretize_positions_static_item:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ MEM owner C.ctx_functions /\
  static_alloca_items owner = SOME items /\ MEM (Allocation aid,sz) items ==>
  canonical_metadata C C' (Allocation aid) (concretize_positions C' owner aid) sz
Proof
  strip_tac >>
  `lookup_function owner.fn_name C.ctx_functions = SOME owner` by
    (gvs[o1_ctx_shape_def, ctx_wf_def, ctx_distinct_fn_names_def, ctx_fn_names_def,
         lookup_function_member_iff]) >>
  drule_all concretize_stage_lookup >> strip_tac >>
  `owner.fn_eom = NONE` by gvs[EVERY_MEM] >>
  drule_all concretize_context_rebuilds_metadata >> strip_tac >> gvs[] >>
  `ALL_DISTINCT (MAP FST items)` by metis_tac[static_alloca_items_ALL_DISTINCT] >>
  drule_all context_layout_own_find >> strip_tac >>
  `concretize_positions C' owner aid = THE (FLOOKUP layout.cl_positions (Allocation aid))` by
    metis_tac[concretize_positions_lookup] >>
  simp[canonical_metadata_def] >>
  qexistsl_tac [`owner`, `items`, `apply_context_concretize_layout observed.cu_context layout owner`] >>
  simp[]
QED

Theorem concretize_positions_activation_cache:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  joint_config_reachable vs0 C q /\ activation_cache q d owner aid (b,sz) ==>
  canonical_metadata C C' (Allocation aid) (concretize_positions C' owner aid) sz
Proof
  strip_tac >>
  `MEM owner C.ctx_functions` by metis_tac[activation_cache_source_owner] >>
  drule_all activation_cache_source_static_item >> strip_tac >>
  metis_tac[concretize_positions_static_item]
QED

Theorem concretize_positions_activation_numeric:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  joint_config_reachable vs0 C q /\ activation_cache q d owner aid (b,sz) ==>
  concretize_positions C' owner aid + sz < dimword (:256) /\
  (0 < sz ==> EVERY (reserved_intervals_disjoint
    (concretize_positions C' owner aid,sz)) C.ctx_global_reserved)
Proof
  strip_tac >> drule_all concretize_positions_activation_cache >> strip_tac >>
  metis_tac[concretize_canonical_numeric]
QED

Theorem reserved_positive_position_lower_bound:
  fixed_region_reserved lo C /\ 0 < sz /\
  EVERY (reserved_intervals_disjoint (p,sz)) C.ctx_global_reserved ==>
  lo <= p
Proof
  simp[fixed_region_reserved_def, EVERY_MEM, FORALL_PROD,
       reserved_intervals_disjoint_def] >>
  rpt strip_tac >> Cases_on `p < lo` >> simp[] >>
  first_x_assum drule >> strip_tac >>
  first_x_assum drule >> decide_tac
QED

Theorem concretize_positions_activation_lower_bound:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\ fixed_region_reserved lo C /\
  joint_config_reachable vs0 C q /\ activation_cache q d owner aid (b,sz) /\
  0 < sz ==> lo <= concretize_positions C' owner aid
Proof
  strip_tac >> drule_all concretize_positions_activation_numeric >> strip_tac >>
  irule reserved_positive_position_lower_bound >> metis_tac[]
QED

Theorem concretize_positions_trace_cache:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\ fixed_region_reserved lo C /\
  joint_trace vs0 C q0 es qs q /\ k <= LENGTH es /\
  activation_cache (EL k (q0::qs)) d owner aid (b,sz) ==>
  canonical_metadata C C' (Allocation aid) (concretize_positions C' owner aid) sz /\
  (0 < sz ==> lo <= concretize_positions C' owner aid)
Proof
  strip_tac >>
  `LENGTH es = LENGTH qs` by metis_tac[joint_trace_def, joint_chain_length] >>
  `k < LENGTH (q0::qs)` by simp[] >>
  `joint_config_reachable vs0 C (EL k (q0::qs))` by
    (drule joint_trace_prefix_reachable >> strip_tac >>
     Cases_on `k` >> fs[EVERY_EL]) >>
  metis_tac[concretize_positions_activation_cache,
            concretize_positions_activation_lower_bound]
QED
