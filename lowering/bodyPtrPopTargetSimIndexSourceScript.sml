Theory bodyPtrPopTargetSimIndexSource
Ancestors
  bodyPtrPopTargetDefs bodyPtrPopTargetSimCurrentLocal
  exprSimSubscriptArrayOrigin stmtSimAugAssignPlace
  vyperInterpreter vyperState targetPlaceSim targetPlaceSimDefs exprSimHypsDefs
  vyperTypeSystem vyperTyping vyperAST list finite_map loweringPosts

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
