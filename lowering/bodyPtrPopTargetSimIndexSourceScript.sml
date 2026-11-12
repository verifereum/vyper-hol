Theory bodyPtrPopTargetSimIndexSource
Ancestors
  bodyPtrPopTargetDefs bodyPtrPopTargetSimCurrentLocal
  exprSimSubscriptArrayOrigin stmtSimAugAssignPlace stmtSimForArrayFrame
  vyperInterpreter vyperState targetPlaceSim targetPlaceSimDefs exprSimHypsDefs
  vyperTypeSystem vyperTyping vyperAST list finite_map loweringPosts
  exprSimProps vyperTypeEnv vyperTypeInvariants vyperPlaceStatePreservation
  stmtSimAugAssign targetPlaceLive exprSimPopNestedBase vyperPureExpr
  vyperStorageBackend

Theorem target_base_memory_root_ptr:
  !bt cx s id path st.
    eval_base_place cx bt s = (INL (PlaceR (MemoryPlace id path)),st) ==>
    target_root bt = NameTarget id
Proof
  `(!e:expr. T) /\ (!bt. !cx s id path st.
    eval_base_place cx bt s = (INL (PlaceR (MemoryPlace id path)),st) ==>
    target_root bt = NameTarget id)` suffices_by simp[] >>
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >>
  simp[] >> rpt conj_tac >> rpt gen_tac
  >- simp[Once evaluate_def, bind_def, get_scopes_def, ignore_bind_def,
          type_check_def, assert_def, return_def, raise_def, AllCaseEqs(), target_root_def]
  >- (PairCases_on `p` >> simp[Once evaluate_def] >> metis_tac[lookup_global_not_memory]) >>
  rpt strip_tac >> qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >> drule extend_place_memory_origin >> strip_tac >> gvs[] >>
  simp[target_root_def] >> metis_tac[]
QED

Theorem target_current_local_resolution_ptr:
  (!id. target_root (SubscriptTarget bt e) = NameTarget id ==>
    local_target_live cx id (SubscriptTarget bt e)) /\
  eval_base_place cx bt es = (INL (PlaceR (MemoryPlace id path)),em) /\
  bind (eval_expr cx e) (read_result cx) em = (INL v,ef) /\
  lookup_scopes id ef.scopes = SOME entry ==>
  ISL (evaluate_subscripts entry.type entry.value path)
Proof
  strip_tac >> drule target_base_memory_root_ptr >> strip_tac >>
  fs[target_root_def, local_target_live_def] >> metis_tac[]
QED

Theorem target_readable_local_type_ptr:
  expr_sim_inv cenv cx env es /\ place_readable cx es (PlaceR (MemoryPlace id path)) ==>
  ?ty entry. FLOOKUP env.var_types id = SOME ty /\
    lookup_scopes id es.scopes = SOME entry /\
    evaluate_type (get_tenv cx) ty = SOME entry.type
Proof
  strip_tac >>
  `?entry. lookup_scopes id es.scopes = SOME entry` by
    (qpat_x_assum `place_readable _ _ _` mp_tac >>
     simp[place_readable_def, read_place_def, get_scopes_def, bind_def,
       lift_option_type_def, return_def, raise_def] >>
     Cases_on `lookup_scopes id es.scopes` >> simp[raise_def]) >>
  fs[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
     vyperTypeInvariantsTheory.env_scopes_consistent_def] >>
  qpat_x_assum `!id entry. lookup_scopes id es.scopes = SOME entry ==> _`
    (qspecl_then [`id`, `entry`] mp_tac) >> simp[] >>
  Cases_on `FLOOKUP env.var_types id` >> simp[] >> metis_tac[]
QED

Theorem target_index_local_source_ptr:
  expr_sim_inv cenv cx env em /\
  place_readable cx em (PlaceR (MemoryPlace id path)) /\
  expr_sim_inv cenv cx env ef /\
  (!id. target_root (SubscriptTarget bt e) = NameTarget id ==>
    local_target_live cx id (SubscriptTarget bt e)) /\
  eval_base_place cx bt es = (INL (PlaceR (MemoryPlace id path)),em) /\
  bind (eval_expr cx e) (read_result cx) em = (INL v,ef) /\
  place_ptr_rel cenv cx u (PlaceR (MemoryPlace id path)) a loc (Type aty) ==>
  ?entry tv. lookup_scopes id ef.scopes = SOME entry /\
    evaluate_type (get_tenv cx) aty = SOME tv /\
    subscripts_type entry.type path = SOME tv /\
    ?cv. evaluate_subscripts entry.type entry.value path = INL cv /\
         value_has_type tv cv
Proof
  strip_tac >> drule_all target_readable_local_type_ptr >> strip_tac >>
  drule_all stmtSimAugAssignTheory.expr_sim_inv_local >> strip_tac >>
  `cenv.ce_var_type id = SOME ty` by (fs[expr_sim_inv_def] >> metis_tac[]) >>
  `ISL (evaluate_subscripts entry'.type entry'.value path)` by
    (irule target_current_local_resolution_ptr >> metis_tac[]) >>
  fs[place_ptr_rel_def] >> gvs[] >>
  drule mem_path_offset_sound >> strip_tac >>
  `value_has_type entry'.type entry'.value /\ well_formed_type_value entry'.type` by
    (fs[expr_sim_inv_def, state_well_typed_def] >>
     metis_tac[scope_well_typed_lookup_scopes]) >>
  Cases_on `evaluate_subscripts entry'.type entry'.value path` >> gvs[] >>
  metis_tac[evaluate_subscripts_type]
QED

Theorem target_index_pure_storage_source_ptr:
  contract_storage_well_formed cx es /\
  EVERY pure_expr (target_indices bt) /\ pure_expr e /\
  eval_base_place cx bt es = (INL (PlaceR (StoragePlace tr slot tv)),em) /\
  bind (eval_expr cx e) (read_result cx) em = (INL v,ef) ==>
  ef = es /\
  slots_in_range (get_storage cx ef tr) (w2n slot) tv /\
  storage_read_live cx tr (get_storage cx ef tr) slot tv
Proof
  strip_tac >>
  `em = es` by metis_tac[nested_pop_eval_base_pure_state] >>
  qpat_x_assum `em = es` SUBST_ALL_TAC >>
  `ef = es` by
    (qpat_x_assum `bind _ _ _ = _` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> strip_tac >>
     drule_all eval_expr_preserves_state >> strip_tac >> gvs[] >>
     metis_tac[read_result_state]) >> gvs[] >>
  drule_all nested_pop_eval_base_slots >>
  drule_all nested_pop_eval_base_live >>
  simp[nested_pop_result_slots_def, nested_pop_result_live_def,
       get_storage_backend_eq]
QED
