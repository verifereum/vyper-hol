(* Typing and writability at the place actually reached by a linked Pop. *)
Theory bodyPopSourceMods
Ancestors
  exprSimPopNestedLocalSource exprBodyPreTypingProps exprBodyPreCallSafetyProps
  vyperTypeAssignContext vyperTypeExprSoundness vyperTypeInvariants
  vyperTypeSystem vyperTypeCallGraph vyperPlaceTyping vyperPlaceStatePreservation
  vyperInterpreter vyperState vyperTyping vyperValue vyperAST

Theorem pop_target_source_facts_mods:
  expr_body_pre_mods mods cenv cx env (Pop ann bt) s /\
  eval_target_place cx bt s = (INL p,t) ==>
  ?n. well_typed_target env bt (ArrayT ann (Dynamic n)) /\
      state_well_typed t /\ env_consistent env cx t /\
      accounts_well_typed t.accounts /\
      writable_place_result cx t (PlaceR p) /\
      eval_result_typed (env,cx,t) (PlaceR p) (Type (ArrayT ann (Dynamic n)))
Proof
  strip_tac >>
  drule expr_body_pre_mods_runtime_typing >> simp[runtime_consistent_def] >>
  strip_tac >>
  drule_then strip_assume_tac well_typed_expr_Pop_dynamic_target >>
  drule expr_body_pre_mods_call_evaluation_safe >> simp[int_calls_expr_def] >>
  strip_tac >>
  `well_typed_target env bt (ArrayT ann (Dynamic n))` by simp[well_typed_target_def] >>
  drule_all_then strip_assume_tac eval_target_place_runtime_facts >>
  drule_all_then assume_tac eval_target_place_writable >>
  qexists `n` >>
  fs[eval_result_typed_def]
QED

Theorem pop_memory_live_array_mods:
  expr_body_pre_mods mods cenv cx env (Pop ann bt) s /\
  eval_target_place cx bt s = (INL (MemoryPlace id path),t) /\
  (?entry v. lookup_scopes id t.scopes = SOME entry /\
             evaluate_subscripts entry.type entry.value path = INL v) ==>
  ?entry etv n vs.
    lookup_scopes id t.scopes = SOME entry /\ entry.assignable /\
    mutable_place_path entry.type path /\
    value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
    evaluate_type env.type_defs ann = SOME etv /\
    subscripts_type entry.type path = SOME (ArrayTV etv (Dynamic n)) /\
    evaluate_subscripts entry.type entry.value path = INL (ArrayV (DynArrayV vs))
Proof
  strip_tac >> drule_all_then strip_assume_tac pop_target_source_facts_mods >>
  drule_all_then strip_assume_tac writable_memory_entry_typed >>
  gvs[evaluate_type_def, runtime_place_typed_memory, AllCaseEqs()] >>
  drule_all_then assume_tac evaluate_subscripts_type >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `value_has_type _ (ArrayV av)` >>
  Cases_on `av` >> gvs[value_has_type_def]
QED
