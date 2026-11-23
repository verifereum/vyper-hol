(* Source certificates at the two gas-marked cuts of a no-copy subscript. *)
Theory bodyFullSubscriptLocalCutOrigin
Ancestors
  bodyFullSubscriptReturnedLocal bodyFullSubscriptPopTraceRead
  exprSimSubscriptArraySource exprSimSource exprSimHypsDefs
  vyperTypeEvalSoundness vyperTypeEvalProofs vyperTypeEvalStoragePreservation
  vyperTypeStatePreservation vyperTypeExprSoundness vyperPlaceResultTyping
  vyperImmutableMetadataFrame vyperStatePreservation vyperState
  vyperPlaceTyping vyperValueOperation list

Theorem marked_local_eval_facts[local]:
  expr_body_pre cenv cx env e st /\ eval_expr cx e st = (INL pv,st') ==>
  typed_scope_transition st st' /\ state_well_typed st' /\
  eval_result_typed (env,cx,st') pv (Type (expr_type e)) /\
  live_memory_result st' pv
Proof
  strip_tac >>
  `runtime_consistent env cx st' /\
   eval_result_typed (env,cx,st') pv (Type (expr_type e)) /\
   live_memory_result st' pv` by
    (irule eval_expr_success_storage_facts >>
     gvs[expr_body_pre_def, expr_sim_inv_def, runtime_consistent_def] >>
     qexists `st` >> simp[]) >>
  fs[runtime_consistent_def] >>
  irule (cj 2 (cj 5 eval_scc_type_sound_mutual)) >>
  gvs[expr_body_pre_def, expr_sim_inv_def] >>
  qexistsl [`cx`, `e`, `env`, `INL pv`] >> simp[]
QED

Theorem marked_base_initial_local[local]:
  expr_body_pre cenv cx env e es /\
  eval_expr cx e (es with gas_obs := gs) = (INL (PlaceR (MemoryPlace id p)),mid) ==>
  ?initial v. lookup_scopes id es.scopes = SOME initial /\
              evaluate_subscripts initial.type initial.value p = INL v
Proof
  strip_tac >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
  `typed_scope_transition es (es with gas_obs := gs)` by
    simp[typed_scope_transition_scopes] >>
  qspec_then `es` mp_tac subscript_returned_local_live_from_extension >>
  (impl_tac >- (fs[expr_body_pre_def, expr_sim_inv_def] >>
                metis_tac[subscript_pop_read_extension_live])) >>
  disch_then (mp_tac o cj 5) >>
  disch_then irule >>
  goal_assum (drule_at Any) >>
  qexistsl [`cx`, `e`, `env`, `mid`] >>
  gvs[expr_body_pre_def, expr_sim_inv_def]
QED

Theorem local_cut_initial_extension[local]:
  state_well_typed es /\ popped_keys_indexed es.scopes /\
  lookup_scopes id es.scopes = SOME initial /\
  evaluate_subscripts initial.type initial.value path = INL old /\
  typed_scope_transition es fin /\ lookup_scopes id fin.scopes = SOME entry /\
  subscripts_type entry.type path = SOME tv /\ read_memory_path entry path = INL v /\
  evaluate_subscripts tv v [sb] = INL w ==>
  ?v1. evaluate_subscripts initial.type initial.value (path ++ [sb]) = INL v1
Proof
  strip_tac >> fs[typed_scope_transition_def] >>
  drule_all scope_pop_trace_lookup >> strip_tac >> gvs[] >>
  irule subscript_pop_read_extension_live >>
  qpat_assum `entry_pop_trace initial _ entry` (irule_at Any) >>
  qpat_assum `evaluate_subscripts tv v [sb] = INL w` (irule_at Any) >>
  qexists `old` >> simp[] >> rpt conj_tac
  >- metis_tac[popped_keys_indexed_lookup_dead]
  >- metis_tac[lookup_scopes_state_well_typed_value_has_type]
  >> irule entry_events_valid >> simp[]
QED

Theorem subscript_local_cut_returned_paths:
  expr_body_pre cenv cx env (Subscript ann obj idx) es /\
  expr_type obj = ArrayT et bd /\
  eval_expr cx obj (es with gas_obs := gs1) = (INL (PlaceR (MemoryPlace id path)),mid) /\
  bind (eval_expr cx idx) (read_result cx) (mid with gas_obs := gs2) = (INL key,fin) ==>
  typed_scope_transition es fin /\ state_well_typed fin /\
  state_well_typed es /\ popped_keys_indexed es.scopes /\
  live_memory_result fin (PlaceR (MemoryPlace id path)) /\
  ?initial v0. lookup_scopes id es.scopes = SOME initial /\
    evaluate_subscripts initial.type initial.value path = INL v0 /\
    !cap etv vs i.
      bd = Dynamic cap /\ key = IntV i /\ 0 <= i /\ Num i < LENGTH vs /\
      runtime_place_typed cx fin (MemoryPlace id path) (ArrayTV etv (Dynamic cap)) /\
      read_result cx (PlaceR (MemoryPlace id path)) fin = (INL (ArrayV (DynArrayV vs)),fin) ==>
      (?v1. evaluate_subscripts initial.type initial.value
               (path ++ [ValueSubscript (IntV i)]) = INL v1) /\
      live_memory_result fin (PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV i)])))
Proof
  strip_tac >>
  `expr_body_pre cenv cx env obj es` by
    (qpat_assum `expr_body_pre _ _ _ (Subscript _ _ _) _`
       (mp_then Any irule exprSimSubscriptArraySourceTheory.expr_body_pre_array_subscript_base_eval) >>
     qpat_assum `eval_expr cx obj _ = (INL _,_)` (irule_at Any) >> simp[]) >>
  drule_all marked_base_initial_local >> strip_tac >>
  `expr_body_pre cenv cx env (Subscript ann obj idx) (es with gas_obs := gs1)` by simp[] >>
  `expr_body_pre cenv cx env idx (mid with gas_obs := gs2)` by
    (drule_all expr_body_pre_array_subscript_index_after_base >> simp[]) >>
  `expr_body_pre cenv cx env obj (es with gas_obs := gs1)` by simp[] >>
  dxrule_all marked_local_eval_facts >> strip_tac >>
  dxrule vyperStatePreservationTheory.bind_split >>
  disch_then (strip_assume_tac o SRULE [sumTheory.sum_distinct]) >>
  drule read_result_state >> disch_then (SUBST_ALL_TAC o SYM) >>
  drule_all marked_local_eval_facts >> strip_tac >>
  `typed_scope_transition es (es with gas_obs := gs1) /\
   typed_scope_transition mid (mid with gas_obs := gs2)` by
    simp[typed_scope_transition_scopes] >>
  `typed_scope_transition mid fin /\ typed_scope_transition es fin` by
    metis_tac[typed_scope_transition_trans] >>
  `immutable_metadata_frame mid fin` by
    (irule immutable_metadata_frame_trans >>
     qexists `mid with gas_obs := gs2` >>
     simp[immutable_metadata_frame_eq] >>
     drule eval_expr_immutable_metadata_frame >> simp[]) >>
  `live_memory_result fin (PlaceR (MemoryPlace id path))` by
    metis_tac[live_memory_result_transport] >>
  `state_well_typed es /\ popped_keys_indexed es.scopes` by
    (qpat_assum `expr_body_pre _ _ _ (Subscript _ _ _) es` mp_tac >>
     simp[NoAsms, expr_body_pre_def, expr_sim_inv_def]) >>
  simp[] >> rpt gen_tac >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `runtime_place_typed _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [runtime_place_typed_memory]) >>
  `read_memory_path entry path = INL (ArrayV (DynArrayV vs))` by
    (qpat_x_assum `read_result cx (PlaceR (MemoryPlace id path)) fin = _` mp_tac >>
     simp[read_result_def, read_place_def, get_scopes_def, bind_def,
          lift_option_type_def, lift_sum_def] >>
     Cases_on `read_memory_path entry path` >> simp[return_def, raise_def]) >>
  `evaluate_subscripts (ArrayTV etv (Dynamic cap)) (ArrayV (DynArrayV vs))
      [ValueSubscript (IntV i)] = INL (EL (Num i) vs)` by
    simp[evaluate_subscripts_def, array_index_def, listTheory.oEL_THM] >>
  conj_tac >- (drule_all local_cut_initial_extension >> simp[]) >>
  `select_result cx (ArrayT et (Dynamic cap)) (PlaceR (MemoryPlace id path))
     (ValueSubscript (IntV i)) fin =
     (INL (PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV i)]))),fin)` by
    (drule_all select_memory_result >> simp[bind_def, lift_sum_def, return_def]) >>
  irule transported_typed_result_extend_live >>
  qpat_assum `eval_result_typed (_,cx,mid) _ _` (irule_at Any) >>
  goal_assum (drule_at Any) >> simp[]
QED
