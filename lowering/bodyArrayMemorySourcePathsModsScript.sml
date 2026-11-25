(* Source path certificates at the marked no-copy array cuts. *)
Theory bodyArrayMemorySourcePathsMods
Ancestors
  bodyFullSubscriptReturnedLocal bodyFullSubscriptPopTraceRead
  exprSimSubscriptArraySource exprSimSource exprSimHypsDefs exprBodyPreProps
  exprBodyPreTypingProps exprBodyPreCallSafetyProps
  vyperTypeEvalSoundness vyperTypeEvalProofs vyperTypeEvalStoragePreservation
  vyperTypeStatePreservation vyperTypeExprSoundness vyperPlaceResultTyping
  vyperImmutableMetadataFrame vyperStatePreservation vyperState
  vyperPlaceTyping vyperValueOperation vyperTypeInvariants finite_map list

Theorem marked_eval_paths[local]:
  runtime_consistent env cx es /\ functions_well_typed cx /\
  well_typed_expr env e /\ call_evaluation_safe cx (int_calls_expr e) /\
  eval_expr cx e (es with gas_obs := marks) = (INL raw,ee) ==>
  typed_scope_transition es ee /\ state_well_typed ee /\
  eval_result_typed (env,cx,ee) raw (Type (expr_type e)) /\
  live_memory_result ee raw /\ immutable_metadata_frame es ee
Proof
  strip_tac >>
  `runtime_consistent env cx (es with gas_obs := marks)` by
    fs[runtime_consistent_def] >>
  drule_all_then strip_assume_tac eval_expr_success_storage_facts >>
  `typed_scope_transition (es with gas_obs := marks) ee` by
    (irule (cj 2 (cj 5 eval_scc_type_sound_mutual)) >>
     fs[runtime_consistent_def] >> qexistsl_tac [`cx`,`e`,`env`,`INL raw`] >> simp[]) >>
  `typed_scope_transition es (es with gas_obs := marks)` by simp[typed_scope_transition_scopes] >>
  drule_all_then assume_tac typed_scope_transition_trans >>
  fs[runtime_consistent_def] >>
  irule immutable_metadata_frame_trans >>
  qexists_tac `es with gas_obs := marks` >> simp[immutable_metadata_frame_eq] >>
  drule eval_expr_immutable_metadata_frame >> simp[]
QED

Theorem marked_initial_local_path[local]:
  runtime_consistent env cx es /\ functions_well_typed cx /\
  popped_keys_indexed es.scopes /\ well_typed_expr env e /\
  call_evaluation_safe cx (int_calls_expr e) /\
  eval_expr cx e (es with gas_obs := marks) = (INL (PlaceR (MemoryPlace id path)),mid) ==>
  ?initial v. lookup_scopes id es.scopes = SOME initial /\
              evaluate_subscripts initial.type initial.value path = INL v
Proof
  strip_tac >>
  `runtime_consistent env cx (es with gas_obs := marks)` by fs[runtime_consistent_def] >>
  `typed_scope_transition es (es with gas_obs := marks)` by simp[typed_scope_transition_scopes] >>
  qspec_then `es` mp_tac subscript_returned_local_live_from_extension >>
  (impl_tac >- (fs[runtime_consistent_def] >> metis_tac[subscript_pop_read_extension_live])) >>
  disch_then (irule o cj 5) >>
  goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  qexists_tac `env` >> fs[runtime_consistent_def]
QED

Theorem marked_local_type[local]:
  expr_sim_inv_mods mods ce cx env es /\ lookup_scopes id es.scopes = SOME entry ==>
  ?rt. ce.ce_var_type id = SOME rt /\ evaluate_type (get_tenv cx) rt = SOME entry.type
Proof
  simp[expr_sim_inv_mods_def, env_consistent_def, env_scopes_consistent_def] >>
  strip_tac >>
  `IS_SOME (FLOOKUP env.var_types id)` by metis_tac[] >>
  Cases_on `FLOOKUP env.var_types id` >> gvs[] >> metis_tac[]
QED

Theorem marked_memory_dynamic_extension[local]:
  state_well_typed es /\ popped_keys_indexed es.scopes /\ state_well_typed fin /\
  lookup_scopes id es.scopes = SOME initial /\
  evaluate_subscripts initial.type initial.value path = INL v0 /\
  lookup_scopes id fin.scopes = SOME entry /\
  entry_pop_trace initial events entry /\ entry_pop_trace_valid events /\
  typed_scope_transition mid fin /\ immutable_metadata_frame mid fin /\
  eval_result_typed (env,cx,mid) (PlaceR (MemoryPlace id path)) (Type (ArrayT et (Dynamic cap))) /\
  live_memory_result mid (PlaceR (MemoryPlace id path)) /\
  subscripts_type entry.type path = SOME (ArrayTV etv (Dynamic cap)) /\
  read_result cx (PlaceR (MemoryPlace id path)) fin = (INL (ArrayV (DynArrayV vs)),fin) /\
  0 <= i /\ Num i < LENGTH vs ==>
  (?v. evaluate_subscripts initial.type initial.value (path ++ [ValueSubscript (IntV i)]) = INL v) /\
  live_memory_result fin (PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV i)])))
Proof
  strip_tac >>
  `read_memory_path entry path = INL (ArrayV (DynArrayV vs))` by
    (qpat_x_assum `read_result _ _ _ = _` mp_tac >>
     simp[read_result_def, read_place_def, get_scopes_def, bind_def,
          lift_option_type_def, lift_sum_def] >>
     Cases_on `read_memory_path entry path` >> simp[return_def, raise_def]) >>
  `evaluate_subscripts (ArrayTV etv (Dynamic cap)) (ArrayV (DynArrayV vs))
     [ValueSubscript (IntV i)] = INL (EL (Num i) vs)` by
    simp[evaluate_subscripts_def, array_index_def, oEL_THM] >>
  conj_tac
  >- (irule subscript_pop_read_extension_live >>
      `value_has_type initial.type initial.value` by
        metis_tac[lookup_scopes_state_well_typed_value_has_type] >>
      `EVERY (\k. ?err. evaluate_subscripts initial.type initial.value k = INR err)
         (MAP FST initial.popped)` by metis_tac[popped_keys_indexed_lookup_dead] >>
      simp[] >> qexistsl_tac [`entry`,`events`,`ArrayTV etv (Dynamic cap)`,
                                `ArrayV (DynArrayV vs)`,`EL (Num i) vs`] >> simp[]) >>
  `select_result cx (ArrayT et (Dynamic cap)) (PlaceR (MemoryPlace id path))
     (ValueSubscript (IntV i)) fin =
     (INL (PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV i)]))),fin)` by
    (drule_all select_memory_result >> simp[bind_def, lift_sum_def, return_def]) >>
  irule transported_typed_result_extend_live >>
  goal_assum (drule_at (Pat `select_result _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `eval_result_typed _ _ _`)) >> simp[]
QED

Theorem array_memory_source_paths_mods:
  expr_sim_inv_mods mods ce cx env es /\ well_typed_expr env obj /\
  call_evaluation_safe cx (int_calls_expr obj) /\
  expr_body_pre_mods mods ce cx env idx mid /\ expr_type obj = ArrayT et bd /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  eval_expr cx obj (es with gas_obs := gs1) = (INL (PlaceR (MemoryPlace id path)),mid) /\
  bind (eval_expr cx idx) (read_result cx) (mid with gas_obs := gs2) = (INL key,fin) ==>
  typed_scope_transition es fin /\ state_well_typed fin /\ state_well_typed es /\
  popped_keys_indexed es.scopes /\ popped_keys_indexed fin.scopes /\
  live_memory_result fin (PlaceR (MemoryPlace id path)) /\
  runtime_place_typed cx fin (MemoryPlace id path) (ArrayTV etv bd) /\
  ?initial em entry v0 events rt.
    lookup_scopes id es.scopes = SOME initial /\
    lookup_scopes id mid.scopes = SOME em /\
    lookup_scopes id fin.scopes = SOME entry /\
    em.type = initial.type /\ entry.type = initial.type /\
    ce.ce_var_type id = SOME rt /\ evaluate_type (get_tenv cx) rt = SOME initial.type /\
    entry_pop_trace initial events entry /\ entry_pop_trace_valid events /\
    subscripts_type entry.type path = SOME (ArrayTV etv bd) /\
    evaluate_subscripts initial.type initial.value path = INL v0 /\
    !cap vs i. bd = Dynamic cap /\ key = IntV i /\ 0 <= i /\ Num i < LENGTH vs /\
      read_result cx (PlaceR (MemoryPlace id path)) fin = (INL (ArrayV (DynArrayV vs)),fin) ==>
      (?v1. evaluate_subscripts initial.type initial.value (path ++ [ValueSubscript (IntV i)]) = INL v1) /\
      live_memory_result fin (PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV i)])))
Proof
  strip_tac >>
  `runtime_consistent env cx es /\ functions_well_typed cx /\
   state_well_typed es /\ popped_keys_indexed es.scopes` by
    fs[expr_sim_inv_mods_def, runtime_consistent_def] >>
  drule_all_then strip_assume_tac marked_initial_local_path >>
  drule_all_then strip_assume_tac marked_eval_paths >>
  drule_then strip_assume_tac expr_body_pre_mods_runtime_typing >>
  drule_then assume_tac expr_body_pre_mods_call_evaluation_safe >>
  dxrule vyperStatePreservationTheory.bind_split >>
  disch_then (strip_assume_tac o SRULE [sumTheory.sum_distinct]) >>
  drule read_result_state >> disch_then (SUBST_ALL_TAC o SYM) >>
  drule_all_then strip_assume_tac marked_eval_paths >>
  `typed_scope_transition es fin` by metis_tac[typed_scope_transition_trans] >>
  `live_memory_result fin (PlaceR (MemoryPlace id path))` by
    metis_tac[live_memory_result_transport] >>
  `popped_keys_indexed fin.scopes` by
    (irule eval_expr_popped_keys_indexed >>
     goal_assum (drule_at (Pat `eval_expr cx idx _ = _`)) >>
     fs[expr_body_pre_mods_def, expr_sim_inv_mods_def]) >>
  drule_all_then strip_assume_tac marked_local_type >>
  qpat_assum `typed_scope_transition es mid`
    (strip_assume_tac o REWRITE_RULE [typed_scope_transition_def]) >>
  qpat_assum `typed_scope_transition es fin`
    (strip_assume_tac o REWRITE_RULE [typed_scope_transition_def]) >>
  `?em. lookup_scopes id mid.scopes = SOME em /\ em.type = initial.type` by
    (qpat_assum `scope_pop_trace es.scopes _ mid.scopes`
       (mp_then Any mp_tac scope_pop_trace_lookup) >>
     disch_then (drule_then strip_assume_tac) >>
     drule_then strip_assume_tac entry_pop_trace_metadata >> simp[] >> metis_tac[]) >>
  `?entry events. lookup_scopes id fin.scopes = SOME entry /\ entry.type = initial.type /\
     entry_pop_trace initial events entry /\ entry_pop_trace_valid events` by
    (qpat_assum `scope_pop_trace es.scopes _ fin.scopes`
       (mp_then Any mp_tac scope_pop_trace_lookup) >>
     disch_then (drule_then strip_assume_tac) >>
     drule_then strip_assume_tac entry_pop_trace_metadata >>
     goal_assum (drule_at (Pat `entry_pop_trace _ _ _`)) >> simp[entry_events_valid]) >>
  `subscripts_type entry.type path = SOME (ArrayTV etv bd)` by
    (qpat_x_assum `eval_result_typed (_,_,mid) (PlaceR _) _` mp_tac >>
     `env.type_defs = get_tenv cx` by fs[runtime_consistent_def, env_consistent_def, env_context_consistent_def] >>
     simp[eval_result_typed_def, runtime_place_typed_memory] >> strip_tac >> gvs[]) >>
  `runtime_place_typed cx fin (MemoryPlace id path) (ArrayTV etv bd)` by
    (simp[runtime_place_typed_memory] >>
     metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value]) >>
  rename1 `entry_pop_trace initial evs entry` >>
  simp[] >> qexists_tac `evs` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `bd = Dynamic cap` SUBST_ALL_TAC >>
  `eval_result_typed (env,cx,mid) (PlaceR (MemoryPlace id path))
     (Type (ArrayT et (Dynamic cap)))` by
    (qpat_x_assum `eval_result_typed (_,_,mid) (PlaceR _) _` mp_tac >> asm_rewrite_tac[]) >>
  drule_all_then ACCEPT_TAC marked_memory_dynamic_extension
QED
