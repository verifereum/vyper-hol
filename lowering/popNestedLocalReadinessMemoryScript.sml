(* Successful local target paths and their actual index continuations. *)
Theory popNestedLocalReadinessMemory
Ancestors
  popNestedLocalPathMemory popNestedFixedPathMemory popNestedLocalAccessMemory
  logArgumentSourceTypes targetSubscriptMemory exprSimPopNestedLocalHandoff
  targetPlaceSim targetPlaceSimCasesBase exprSimSource vyperTypeCallGraph
  stmtSimAugAssignPlace popTargetPre gasSummary
  vyperTypeInvariants vyperPlaceFrames vyperInterpreter vyperValue
  vyperTyping vyperState exprSimHypsDefs vyperTypeEnv allocLimits
  vyperTypeSystem vyperTypeCallStackSoundness vyperPlaceTyping
  vyperPlaceResultTyping vyperTypeEvalSoundness option list

Theorem pop_nested_local_index_ready:
  target_root bt = NameTarget id /\
  target_pre cenv cx env bt st /\
  type_place_target env bt = SOME (Type ty) /\
  call_evaluation_safe cx (int_calls_target bt) /\
  eval_base_place cx bt st = (INL (PlaceR (MemoryPlace id path)),mid) /\
  lookup_scopes id mid.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value path = INL v /\
  ~target_subscript_overlap cenv bt e /\
  expr_body_pre cenv cx env e mid /\
  bind (eval_expr cx e) (read_result cx) mid = (res,fin) ==>
  ?other w. lookup_scopes id fin.scopes = SOME other /\
    evaluate_subscripts other.type other.value path = INL w
Proof
  strip_tac >> Cases_on `target_through_dynarray cenv bt`
  >- (drule_all pop_nested_local_index_entry_frame >> simp[] >> metis_tac[]) >>
  drule_all pop_nested_local_path_typed >> strip_tac >> gvs[] >>
  drule pop_nested_local_path_fixed >> simp[] >> disch_tac >>
  `expr_sim_inv cenv cx env mid` by metis_tac[eval_base_place_sim_inv] >>
  qpat_x_assum `bind _ _ mid = _` mp_tac >>
  simp[bind_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  imp_res_tac read_result_state >> gvs[] >>
  `expr_sim_inv cenv cx env fin` by metis_tac[expr_body_pre_eval_result] >>
  `env_scopes_consistent env cx mid /\ env_scopes_consistent env cx fin /\
   state_well_typed fin` by fs[expr_sim_inv_def, env_consistent_def] >>
  drule_all consistent_scopes_lookup_type >> strip_tac >>
  `value_has_type old.type old.value /\ well_formed_type_value old.type` by
    (irule scope_well_typed_lookup_scopes >>
     gvs[state_well_typed_def] >> goal_assum (drule_at Any) >> simp[]) >>
  qexists_tac `old` >> simp[] >>
  irule pop_nested_fixed_path_ready >> metis_tac[]
QED

Theorem pop_nested_local_base_ready:
  !bt cenv cx env st ty id pv fin.
    target_root bt = NameTarget id /\
    target_pre cenv cx env bt st /\
    type_place_target env bt = SOME (Type ty) /\
    call_evaluation_safe cx (int_calls_target bt) /\
    eval_base_place cx bt st = (INL pv,fin) ==>
    ?path entry v. pv = PlaceR (MemoryPlace id path) /\
      lookup_scopes id fin.scopes = SOME entry /\
      evaluate_subscripts entry.type entry.value path = INL v
Proof
  recInduct base_assignment_target_induct >> rpt conj_tac >> rpt gen_tac
  >- (simp[Once evaluate_def, bind_def, get_scopes_def, type_check_def,
           assert_def, ignore_bind_def, return_def, raise_def, target_root_def] >>
      rpt strip_tac >> gvs[AllCaseEqs(), IS_SOME_EXISTS] >>
      simp[evaluate_subscripts_def])
  >- simp[target_root_def]
  >- suspend "subscript"
  >> suspend "attribute"
QED

Resume pop_nested_local_base_ready[subscript]:
  strip_tac >> rpt gen_tac >> strip_tac >>
  imp_res_tac (cj 2 target_pre_sub) >>
  gvs[target_root_def, type_place_target_SubscriptTarget] >>
  qpat_x_assum `eval_base_place cx (SubscriptTarget bt e) st = _` mp_tac >>
  simp[Once evaluate_def, bind_def] >>
  Cases_on `eval_base_place cx bt st` >> rename1 `(r1,s1)` >>
  Cases_on `r1` >> simp[] >>
  Cases_on `eval_expr cx e s1` >> rename1 `(r2,s2)` >>
  Cases_on `r2` >> simp[] >>
  rename1 `eval_expr cx e s1 = (INL rv,s2)` >>
  Cases_on `read_result cx rv s2` >> rename1 `(r3,s3)` >>
  Cases_on `r3` >> simp[] >> strip_tac >> gvs[] >>
  `call_evaluation_safe cx (int_calls_target bt)` by
    (fs[int_calls_expr_def] >> metis_tac[call_evaluation_safe_append_left]) >>
  `env_consistent env cx st /\ state_well_typed st /\
   context_well_typed cx /\ accounts_well_typed st.accounts /\
   functions_well_typed cx` by fs[target_pre_def, expr_sim_inv_def] >>
  drule_all aug_place_name_root_base >> strip_tac >> gvs[] >>
  drule_all (cj 1 (cj 7 eval_scc_type_sound_results_mutual)) >>
  Cases_on `vt'` >> simp[eval_result_typed_place, runtime_place_typed_memory] >>
  strip_tac >>
  first_x_assum drule_all >> strip_tac >> gvs[] >>
  `expr_sim_inv cenv cx env s1` by metis_tac[eval_base_place_sim_inv] >>
  `expr_body_pre cenv cx env e s1 /\ ~target_subscript_overlap cenv bt e` by
    fs[target_pre_def, target_indices_pre_def] >>
  `bind (eval_expr cx e) (read_result cx) s1 = (INL x',s3)` by simp[bind_def] >>
  drule_all pop_nested_local_index_ready >> strip_tac >>
  drule_all extend_place_memory_live >> strip_tac >> gvs[] >> metis_tac[]
QED

Resume pop_nested_local_base_ready[attribute]:
  strip_tac >> rpt gen_tac >> strip_tac >>
  imp_res_tac (cj 1 target_pre_sub) >>
  gvs[target_root_def, type_place_target_AttributeTarget, int_calls_expr_def] >>
  qpat_x_assum `eval_base_place cx (AttributeTarget bt s) st = _` mp_tac >>
  simp[Once evaluate_def, bind_def] >>
  Cases_on `eval_base_place cx bt st` >> rename1 `(r1,s1)` >>
  Cases_on `r1` >> simp[] >> strip_tac >> gvs[] >>
  first_x_assum drule_all >> strip_tac >> gvs[] >>
  drule_all extend_place_memory_live >> strip_tac >> gvs[] >> metis_tac[]
QED

Finalise pop_nested_local_base_ready

Theorem pop_nested_local_target_ready:
  expr_body_pre cenv cx env (Pop ann bt) st /\
  target_root bt = NameTarget id /\
  eval_target_place cx bt st = (INL p,fin) ==>
  ?path entry v. p = MemoryPlace id path /\
    lookup_scopes id fin.scopes = SOME entry /\
    evaluate_subscripts entry.type entry.value path = INL v
Proof
  strip_tac >>
  `~immutable_root cx bt` by fs[immutable_root_def] >>
  `target_pre cenv cx env bt st` by metis_tac[target_pre_of_pop] >>
  `?n. type_place_target env bt = SOME (Type (ArrayT ann (Dynamic n))) /\
       call_evaluation_safe cx (int_calls_target bt)` by
    (fs[expr_body_pre_def, well_typed_expr_def, well_typed_target_def,
        int_calls_expr_def] >> metis_tac[]) >>
  qpat_x_assum `eval_target_place cx bt st = _` mp_tac >>
  simp[Once evaluate_def, bind_def] >>
  Cases_on `eval_base_place cx bt st` >> rename1 `(out,mid)` >>
  Cases_on `out` >> simp[] >>
  drule_all pop_nested_local_base_ready >> strip_tac >> gvs[] >>
  simp[get_place_def, return_def] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

(* The antecedent describing a popped-history fallback is unreachable.  This
   is exactly the no-popped premise of pop_counted_source_handoff, at the same
   marked execution witnesses; no new execution is chosen. *)
Theorem pop_nested_local_no_popped:
  expr_body_pre cenv cx env (Pop ann bt) es /\
  target_root bt = NameTarget id /\
  gas_marked_exec memory (ctx,func) (eval_target_place cx bt)
    (es,s0) marks (INL p) tend r ==>
  !path entry err.
    p = MemoryPlace id path /\
    lookup_scopes id tend.scopes = SOME entry /\
    evaluate_subscripts entry.type entry.value path = INR err ==>
    read_popped entry.type path entry.popped = NONE
Proof
  strip_tac >>
  `eval_target_place cx bt
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL p,tend with gas_obs := [])` by
    (fs[gas_marked_exec_def] >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_body_pre cenv cx env (Pop ann bt)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  drule_all pop_nested_local_target_ready >> simp[] >> rpt strip_tac >> gvs[]
QED
