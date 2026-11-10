(* Actual target reachability and full borrowed extents. *)
Theory tuplePlaceReachable
Ancestors
  tuplePlaceGeometry tuplePlaceBorrow bodySimAugPlaceLoad
  exprSimPopNestedLocalSource vyperTargetPlaceWrite bodyExprPreFacts
  vyperTypeCallStackSoundness vyperTypeCallGraph exprSimHypsDefs supportedTargets
  vyperPlaceWriteSoundness exprLoweringProps compileEnv loweringPosts exprSimProps pair

Theorem tuple_place_local_path_extent:
  expr_sim_inv cenv cx env ee /\
  stmt_state_rel ctx func cenv cx ee s /\
  local_region cenv ee.scopes s n b sz /\
  local_path_at cenv cx n k tv ==>
  k + type_memory_size tv <= sz
Proof
  rpt strip_tac >>
  gvs[local_region_def, local_path_at_def] >>
  `evaluate_type (get_tenv cx) t0 = SOME entry.type` by
    (drule aug_place_entry_type_agrees >> metis_tac[]) >>
  gvs[] >> drule mem_path_offset_sound >> strip_tac >>
  gvs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
  res_tac >> gvs[]
QED

Theorem tuple_place_mutable_path_barrier:
  !path tv k out.
    mutable_place_path tv path /\
    mem_path_offset tv path = SOME (k,out) ==>
    tuple_place_no_tuple_step tv path
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  gvs[mem_path_offset_def, AllCaseEqs(), EXISTS_PROD] >>
  drule tuple_place_no_tuple_step_cons >> disch_then (rewrite_tac o single) >>
  Cases_on `h` >> Cases_on `tv` >>
  gvs[mutable_place_path_def, mem_step_offset_def, AllCaseEqs()] >>
  imp_res_tac mem_field_offset_sound >> gvs[] >>
  Cases_on `v` >> gvs[mutable_place_path_def, mem_step_offset_def] >>
  Cases_on `b` >> gvs[mem_step_offset_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem tuple_place_base_target_adapter:
  eval_base_place cx bt ee = (INL (PlaceR p),ee) ==>
  eval_target_place cx bt ee = (INL p,ee)
Proof
  simp[Once vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.get_place_def, vyperStateTheory.return_def]
QED

Theorem tuple_place_reachable_memory_barrier:
  expr_sim_inv cenv cx env ee /\ well_typed_target env bt ty /\
  call_evaluation_safe cx (int_calls_target bt) /\
  eval_base_place cx bt ee = (INL (PlaceR (MemoryPlace id path)),ee) /\
  cenv.ce_var_type id = SOME root_ty /\
  evaluate_type (get_tenv cx) root_ty = SOME root_tv /\
  mem_path_offset root_tv path = SOME (k,tv) ==>
  tuple_place_no_tuple_step root_tv path
Proof
  rpt strip_tac >>
  drule tuple_place_base_target_adapter >> strip_tac >>
  `writable_place_result cx ee (PlaceR (MemoryPlace id path))` by
    (gvs[exprSimHypsDefsTheory.expr_sim_inv_def] >>
     drule_all eval_target_place_writable >> simp[]) >>
  `?entry. lookup_scopes id ee.scopes = SOME entry /\
           mutable_place_path entry.type path` by
    gvs[vyperTargetPlaceWriteTheory.writable_place_result_def,
        runtime_place_writable_def] >>
  `evaluate_type (get_tenv cx) root_ty = SOME entry.type` by
    (drule aug_place_entry_type_agrees >> metis_tac[]) >>
  gvs[] >> irule tuple_place_mutable_path_barrier >> metis_tac[]
QED

Theorem tuple_place_rhs_empty_call_safe:
  expr_body_pre cenv cx env e es ==> call_evaluation_safe cx []
Proof
  simp[exprSimHypsDefsTheory.expr_body_pre_def] >> rpt strip_tac >>
  irule vyperTypeCallStackSoundnessTheory.call_evaluation_safe_mono >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem tuple_place_pure_target_no_calls:
  !bt tops. supported_target_pure tops bt ==> int_calls_target bt = []
Proof
  measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt` >>
  simp[supportedTargetsTheory.supported_target_pure_def,
       vyperTypeCallGraphTheory.int_calls_expr_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `b` mp_tac) >>
  simp[vyperASTTheory.expr_size_def] >>
  metis_tac[bodyExprPreFactsTheory.supported_pure_int_calls]
QED

Theorem tuple_place_rhs_target_call_safe:
  expr_body_pre cenv cx env e es /\ supported_target_pure tops bt ==>
  call_evaluation_safe cx (int_calls_target bt)
Proof
  metis_tac[tuple_place_rhs_empty_call_safe, tuple_place_pure_target_no_calls]
QED

(* Coordinate interface for live memory places; no write is needed. *)
Theorem tuple_place_memory_coordinates:
  expr_sim_inv cenv cx env ee /\ stmt_state_rel ctx func cenv cx ee s /\
  lookup_scopes id ee.scopes = SOME entry /\
  place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) dw
    (SOME LocMemory) (Type ty) ==>
  ?base sz root_tv off tv.
    local_region cenv ee.scopes s id base sz /\
    local_path_at cenv cx id off tv /\
    mem_path_offset root_tv path = SOME (off,tv) /\
    root_tv = entry.type /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    w2n dw = base + off /\ off + type_memory_size tv <= sz
Proof
  rpt strip_tac >> gvs[place_ptr_rel_def] >>
  `evaluate_type (get_tenv cx) t0 = SOME entry.type` by
    (drule aug_place_entry_type_agrees >> metis_tac[]) >> gvs[] >>
  `local_ptrs_rel func cenv ee.scopes s` by
    metis_tac[stmt_state_rel_def, state_rel_def] >>
  `w2n b + sz <= s.vs_alloca_next /\ type_memory_size entry.type <= sz` by
    (gvs[local_ptrs_rel_def] >>
     first_x_assum (drule_all_then strip_assume_tac) >> gvs[]) >>
  `s.vs_alloca_next < dimword (:256)` by
    metis_tac[exprLoweringPropsTheory.alloca_room_next_lt, stmt_state_rel_def] >>
  drule mem_path_offset_sound >> strip_tac >>
  `k < dimword (:256) /\ w2n b + k < dimword (:256)` by decide_tac >>
  `w2n (b + n2w k) = w2n b + k` by
    (`w2n (b + n2w k) = w2n b + w2n ((n2w k):bytes32)` suffices_by simp[] >>
     irule wordsTheory.w2n_add_2 >> simp[] >> decide_tac) >>
  qexistsl [`w2n b`, `sz`] >>
  simp[local_region_def, local_path_at_def] >> metis_tac[]
QED

Theorem tuple_place_borrow_destination_apart:
  expr_sim_inv cenv cx env ee /\ stmt_state_rel ctx func cenv cx ee s /\
  local_region cenv ee.scopes s n b sz /\
  local_path_at cenv cx n k (TupleTV tvs) /\
  k + type_memory_size (TupleTV tvs) <= sz /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  i < LENGTH tys /\ well_typed_target env bt (EL i tys) /\
  supported_target_pure tops bt /\ call_evaluation_safe cx [] /\
  eval_base_place cx bt ee = (INL (PlaceR p),ee) /\
  place_ptr_rel cenv cx s (PlaceR p) dw (SOME LocMemory) (Type (EL i tys)) ==>
  b + k + type_memory_size (TupleTV tvs) <= w2n dw \/
  w2n dw + type_memory_size (EL i tvs) <= b + k
Proof
  rpt strip_tac >>
  `call_evaluation_safe cx (int_calls_target bt)` by
    metis_tac[tuple_place_pure_target_no_calls] >>
  `writable_place_result cx ee (PlaceR p)` by
    (drule tuple_place_base_target_adapter >> strip_tac >>
     gvs[expr_sim_inv_def] >> drule_all eval_target_place_writable >> simp[]) >>
  Cases_on `p` >>
  gvs[place_ptr_rel_def, slot_loc_def, AllCaseEqs(),
      vyperTargetPlaceWriteTheory.writable_place_result_def,
      runtime_place_writable_def] >>
  `place_ptr_rel cenv cx s (PlaceR (MemoryPlace s' l)) (b' + n2w k')
     (SOME LocMemory) (Type (EL i tys))` by
    (simp[place_ptr_rel_def] >> metis_tac[]) >>
  drule_all tuple_place_memory_coordinates >> strip_tac >>
  `evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs) /\ i < LENGTH tvs` by
    (gvs[vyperValueTheory.evaluate_type_def,
         vyperValueTheory.evaluate_types_OPT_MMAP, AllCaseEqs()] >>
     drule exprSimAttributeFieldsTheory.opt_mmap_el >>
     disch_then (qspec_then `i` mp_tac) >> simp[]) >>
  gvs[] >> reverse (Cases_on `s' = n`)
  >- (`regions_disjoint b sz base' sz''` by
        (gvs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
         metis_tac[]) >>
      gvs[compileEnvTheory.regions_disjoint_def] >> decide_tac) >>
  gvs[local_region_def, local_path_at_def] >>
  `evaluate_type (get_tenv cx) t0 = SOME entry.type` by
    (drule aug_place_entry_type_agrees >> metis_tac[]) >> gvs[] >>
  `tuple_place_no_tuple_step entry.type l` by
    (irule tuple_place_mutable_path_barrier >> metis_tac[]) >>
  irule tuple_place_tuple_barrier_apart >>
  conj_tac >- metis_tac[listTheory.EL_MEM] >>
  qexistsl [`path`, `l`, `entry.type`] >> simp[]
QED
