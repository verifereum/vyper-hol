Theory exprSimPopNestedLocalSource
Ancestors
  vyperTypeEvalSoundness vyperTypeAssignContext exprSimHypsDefs
  vyperTargetPlaceWrite vyperPlaceWriteSoundness vyperTypeInvariants vyperTypeEnv

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
