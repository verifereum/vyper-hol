(* Actual target reachability and full borrowed extents. *)
Theory tuplePlaceReachable
Ancestors
  vyperLocalAccessFrame vyperTypeEnv vyperPlaceResultTyping vyperTypeInvariants vyperValue
  vyperTypeSystem vyperValueOperation targetPlaceSim targetPlaceSimCasesBase
  vyperInterpreter vyperState
  tuplePlaceGeometry tuplePlaceBorrow bodySimAugPlaceLoad
  exprSimPopNestedLocalSource vyperTargetPlaceWrite bodyExprPreFacts
  vyperTypeCallStackSoundness vyperTypeCallGraph exprSimHypsDefs supportedTargets
  vyperPlaceWriteSoundness exprLoweringProps compileEnv loweringStateRelDefs loweringPosts exprSimProps pair

Theorem tuple_place_local_path_extent:
  expr_sim_inv cenv cx env ee /\
  stmt_state_rel H ctx func cenv cx ee s /\
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

(* Coordinate interface for live memory places; no write is needed. *)
Theorem tuple_place_memory_coordinates:
  expr_sim_inv cenv cx env ee /\ stmt_state_rel H ctx func cenv cx ee s /\
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

Theorem tuple_place_target_step[local]:
  evaluate_type env.type_defs ty = SOME base_tv /\
  mem_path_offset base_tv [sb] = SOME (off,tv) /\
  ((?ix ix_ty. sb = ValueSubscript ix /\
          subscript_vtype (Type ty) ix_ty = SOME vt) \/
   (?field field_ty. sb = AttrSubscript field /\ vt = Type field_ty /\
          attribute_type env.type_defs ty field = SOME field_ty)) ==>
  mutable_place_path base_tv [sb] /\
  ?out. vt = Type out /\ evaluate_type env.type_defs out = SOME tv
Proof
  disch_then strip_assume_tac >> gvs[]
  >- (Cases_on `ty` >> gvs[subscript_vtype_def, AllCaseEqs()] >>
      gvs[evaluate_type_def, AllCaseEqs()] >>
      Cases_on `ix` >> Cases_on `b` >>
      gvs[mem_path_offset_def, mem_step_offset_def, AllCaseEqs(),
          mutable_place_path_def]) >>
  drule_all attribute_type_runtime_step >> strip_tac >>
  drule mem_path_offset_sound >> simp[subscripts_type_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  Cases_on `base_tv` >> gvs[subscript_type_def, mutable_place_path_def]
QED

(* A successful memory target follows the checked path from its local root.
   The offset supplies the shape of the index value even when the index
   expression calls an internal function. *)
Theorem tuple_place_target_memory_path[local]:
  !bt cx env ee final id path vt root_tv off tv.
    type_place_target env bt = SOME vt /\
    eval_base_place cx bt ee = (INL (PlaceR (MemoryPlace id path)),final) /\
    (!ty. FLOOKUP env.var_types id = SOME ty ==>
          evaluate_type env.type_defs ty = SOME root_tv) /\
    mem_path_offset root_tv path = SOME (off,tv) ==>
    IS_SOME (lookup_scopes id ee.scopes) /\ mutable_place_path root_tv path /\
    ?ty. vt = Type ty /\ evaluate_type env.type_defs ty = SOME tv
Proof
  recInduct base_assignment_target_induct >> rpt conj_tac
  >- (rpt gen_tac >>
      simp[type_place_target_NameTarget, Once evaluate_def, bind_def,
           get_scopes_def, type_check_def, assert_def, ignore_bind_def,
           return_def, raise_def, mem_path_offset_def, mutable_place_path_def,
           AllCaseEqs()] >>
      rpt strip_tac >> gvs[mem_path_offset_def] >> metis_tac[])
  >- (rpt gen_tac >> PairCases_on `nsid` >>
      simp[Once evaluate_def, lookup_global_not_memory])
  >> rpt gen_tac >> strip_tac >> rpt gen_tac >> disch_then strip_assume_tac >>
  qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >>
  strip_tac >>
  drule extend_place_memory_origin >> strip_tac >> gvs[] >>
  drule aug_place_extend_name_memory >> strip_tac >> gvs[] >>
  drule mem_path_offset_append_decompose >> strip_tac >>
  gvs[Once well_typed_expr_def, AllCaseEqs()] >>
  first_x_assum (drule_all_then strip_assume_tac) >> gvs[] >>
  simp[] >>
  drule_at (Pat `mem_path_offset _ [_] = _`) tuple_place_target_step >>
  disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
  disch_then (fn step => FIRST
    [qpat_assum `subscript_vtype _ _ = SOME vt`
       (fn _ => mp_tac (Q.SPEC `vt` step)),
     mp_tac (Q.SPEC `Type ty` step)]) >>
  (impl_tac >- metis_tac[]) >> strip_tac >> gvs[] >>
  imp_res_tac mem_path_offset_sound >>
  metis_tac[mutable_place_path_append]
QED

Theorem tuple_place_borrow_destination_apart:
  expr_sim_inv cenv cx env ee /\ stmt_state_rel H ctx func cenv cx ee s /\
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
  `?id dest. p = MemoryPlace id dest` by
    (Cases_on `p` >> gvs[place_ptr_rel_def, slot_loc_def, AllCaseEqs()]) >>
  gvs[] >>
  qpat_assum `place_ptr_rel _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [place_ptr_rel_def]) >>
  rename1 `cenv.ce_var_type id = SOME root_ty` >>
  rename1 `evaluate_type (get_tenv cx) root_ty = SOME root_tv` >>
  rename1 `mem_path_offset root_tv dest = SOME (off,dest_tv)` >>
  `(!ty. FLOOKUP env.var_types id = SOME ty ==>
           evaluate_type env.type_defs ty = SOME root_tv)` by
    (fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
     gen_tac >> strip_tac >>
     `cenv.ce_var_type id = SOME ty` by
       (qpat_assum `!name t. FLOOKUP env.var_types name = SOME t ==>
                              cenv.ce_var_type name = SOME t` irule >>
        first_assum ACCEPT_TAC) >>
     fs[]) >>
  `IS_SOME (lookup_scopes id ee.scopes) /\
   mutable_place_path root_tv dest` by
    (mp_tac (Q.SPECL [`bt`, `cx`, `env`, `ee`, `ee`, `id`, `dest`,
        `Type (EL i tys)`, `root_tv`, `off`, `dest_tv`]
        tuple_place_target_memory_path) >>
     fs[well_typed_target_def]) >>
  Cases_on `lookup_scopes id ee.scopes` >> gvs[] >>
  rename1 `lookup_scopes id ee.scopes = SOME entry` >>
  `tuple_place_no_tuple_step root_tv dest` by
    (irule tuple_place_mutable_path_barrier >> metis_tac[]) >>
  drule_all tuple_place_memory_coordinates >> strip_tac >>
  `evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs) /\ i < LENGTH tvs` by
    (gvs[vyperValueTheory.evaluate_type_def,
         vyperValueTheory.evaluate_types_OPT_MMAP, AllCaseEqs()] >>
     drule exprSimAttributeFieldsTheory.opt_mmap_el >>
     disch_then (qspec_then `i` mp_tac) >> simp[]) >>
  gvs[] >> reverse (Cases_on `id = n`)
  >- (`regions_disjoint b sz base' sz''` by
        (gvs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
         metis_tac[]) >>
      gvs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  gvs[local_region_def, local_path_at_def] >>
  `root_tv = entry.type` by
    (drule aug_place_entry_type_agrees >>
     disch_then (qspecl_then [`root_ty`, `ee`, `id`, `entry`] mp_tac) >>
     simp[]) >>
  gvs[] >>
  `k + type_memory_size (TupleTV tvs) <= off \/
   off + type_memory_size (EL i tvs) <= k` by
    (irule tuple_place_tuple_barrier_apart >>
     conj_tac >- metis_tac[listTheory.EL_MEM] >>
     qexistsl_tac [`path`, `dest`, `entry.type`] >> simp[]) >>
  decide_tac
QED
