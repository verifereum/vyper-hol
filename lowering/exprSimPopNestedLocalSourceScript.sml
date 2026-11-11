Theory exprSimPopNestedLocalSource
Ancestors
  vyperTypeEvalSoundness vyperTypeAssignContext exprSimHypsDefs
  vyperTargetPlaceWrite vyperPlaceWriteSoundness vyperTypeInvariants vyperTypeEnv
  vyperTypeSystem vyperTypeCallGraph vyperPlaceResultTyping vyperPlaceTyping
  vyperValue vyperTyping vyperPlaceStatePreservation exprSimPopNestedLocalProps

Theorem eval_target_place_runtime_facts:
  !cx bt env ty s p t.
    well_typed_target env bt ty /\ env_consistent env cx s /\
    state_well_typed s /\ context_well_typed cx /\
    accounts_well_typed s.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_target bt) /\
    eval_target_place cx bt s = (INL p,t) ==>
    state_well_typed t /\ env_consistent env cx t /\
    accounts_well_typed t.accounts /\
    eval_result_typed (env,cx,t) (PlaceR p) (Type ty)
Proof
  rpt strip_tac >>
  drule_all (cj 1 (cj 8 eval_scc_type_sound_results_mutual)) >> simp[]
QED

Theorem eval_target_place_writable:
  !cx bt env ty s p t.
    well_typed_target env bt ty /\ env_consistent env cx s /\
    state_well_typed s /\ context_well_typed cx /\
    accounts_well_typed s.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_target bt) /\
    eval_target_place cx bt s = (INL p,t) ==>
    writable_place_result cx t (PlaceR p)
Proof
  rpt strip_tac >>
  drule_all (cj 4 (cj 8 eval_scc_type_sound_results_mutual)) >> simp[]
QED

Theorem writable_memory_entry_typed:
  !cx s id path.
    state_well_typed s /\
    writable_place_result cx s (PlaceR (MemoryPlace id path)) ==>
    ?entry. lookup_scopes id s.scopes = SOME entry /\ entry.assignable /\
      mutable_place_path entry.type path /\
      value_has_type entry.type entry.value /\ well_formed_type_value entry.type
Proof
  simp[writable_place_result_def, runtime_place_writable_def] >>
  rpt strip_tac >> qexists `entry` >> simp[] >>
  irule scope_well_typed_lookup_scopes >>
  gvs[state_well_typed_def] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem pop_target_source_facts:
  expr_body_pre cenv cx env (Pop ann bt) s /\
  eval_target_place cx bt s = (INL p,t) ==>
  ?n. state_well_typed t /\ env_consistent env cx t /\
    writable_place_result cx t (PlaceR p) /\
    eval_result_typed (env,cx,t) (PlaceR p) (Type (ArrayT ann (Dynamic n)))
Proof
  strip_tac >>
  `?n. well_typed_target env bt (ArrayT ann (Dynamic n)) /\
       call_evaluation_safe cx (int_calls_target bt)` by
    (fs[expr_body_pre_def, well_typed_expr_def, well_typed_target_def,
        int_calls_expr_def] >> metis_tac[]) >>
  `env_consistent env cx s /\ state_well_typed s /\
   accounts_well_typed s.accounts /\ context_well_typed cx /\
   functions_well_typed cx` by fs[expr_body_pre_def, expr_sim_inv_def] >>
  qpat_x_assum `expr_body_pre _ _ _ _ _` kall_tac >>
  drule_all eval_target_place_runtime_facts >> strip_tac >>
  drule_all eval_target_place_writable >> strip_tac >>
  qexists_tac `n` >> simp[]
QED

Theorem pop_target_live_array:
  expr_body_pre cenv cx env (Pop ann bt) s /\
  eval_target_place cx bt s = (INL (MemoryPlace id path),t) /\
  place_readable cx t (PlaceR (MemoryPlace id path)) /\
  (!entry err. lookup_scopes id t.scopes = SOME entry /\
    evaluate_subscripts entry.type entry.value path = INR err ==>
    read_popped entry.type path entry.popped = NONE) ==>
  ?entry etv n vs.
    lookup_scopes id t.scopes = SOME entry /\ entry.assignable /\
    mutable_place_path entry.type path /\
    value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
    evaluate_type env.type_defs ann = SOME etv /\
    subscripts_type entry.type path = SOME (ArrayTV etv (Dynamic n)) /\
    evaluate_subscripts entry.type entry.value path = INL (ArrayV (DynArrayV vs))
Proof
  strip_tac >> drule_all pop_target_source_facts >> strip_tac >>
  drule_all writable_memory_entry_typed >> strip_tac >>
  drule_all place_readable_memory_live >> strip_tac >> gvs[] >>
  gvs[evaluate_type_def, runtime_place_typed_memory, AllCaseEqs()] >>
  drule_all evaluate_subscripts_type >> strip_tac >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `value_has_type _ (ArrayV av)` >>
  Cases_on `av` >> gvs[value_has_type_def]
QED
