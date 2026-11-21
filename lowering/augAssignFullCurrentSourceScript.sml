(* Source-only writeback readiness at the actual post-RHS state.
   The saved current value is not identified with a refreshed immutable value. *)
Theory augAssignFullCurrentSource
Ancestors
  targetLocalLive stmtSimForArrayFrame targetPlaceSim exprSimHypsDefs
  stmtSimAugAssignPlaceMemory bodyImmutableAugAssignFacts bodySimStmtFacts
  bodySimAugPlaceLoad bodySimAugPlaceLive bodySimAugPlaceScopes
  vyperStorageTrace vyperStoragePlaceRegion exprSimSource
  supportedStmts vyperState list

Theorem augassign_memory_current_source_ready:
  target_pre cenv cx env bt es /\ type_place_target env bt = SOME (Type ty) /\
  ~aug_assign_overlap cenv bt e /\ expr_body_pre cenv cx env e st /\
  eval_target_place cx bt es = (INL (MemoryPlace id path),st) /\
  place_type_value cx (MemoryPlace id path) st = (INL ptv,st) /\
  bind (eval_expr cx e) (read_result cx) st = (INL rhs,ee) ==>
  expr_sim_inv cenv cx env ee /\
  ?entry old. lookup_scopes id ee.scopes = SOME entry /\
    evaluate_subscripts entry.type entry.value path = INL old /\
    subscripts_type entry.type path = SOME ptv /\
    (!t0. cenv.ce_var_type id = SOME t0 ==>
      evaluate_type (get_tenv cx) t0 = SOME entry.type)
Proof
  strip_tac >>
  `expr_sim_inv cenv cx env ee` by metis_tac[expr_body_pre_eval] >>
  `expr_sim_inv cenv cx env st` by fs[expr_body_pre_def] >>
  `?entry. lookup_scopes id st.scopes = SOME entry /\
           subscripts_type entry.type path = SOME ptv` by
    (qpat_x_assum `place_type_value _ _ _ = _` mp_tac >>
     Cases_on `lookup_scopes id st.scopes` >>
     simp[place_type_value_def, get_scopes_def, bind_def, lift_option_type_def,
          return_def, raise_def] >>
     rename1 `lookup_scopes id st.scopes = SOME entry` >>
     Cases_on `subscripts_type entry.type path` >>
     simp[bind_def, return_def, raise_def]) >>
  `target_root bt = NameTarget id` by
    metis_tac[eval_target_place_memory_root, place_access_root] >>
  drule_all local_target_live >> strip_tac >>
  drule_all aug_place_rhs_memory_live >> strip_tac >>
  simp[] >> metis_tac[aug_place_store_entry_types]
QED

Theorem augassign_immutable_current_source_ready:
  expr_body_pre cenv cx env e st /\
  bind (eval_expr cx e) (read_result cx) st = (INL rhs,ee) /\
  FLOOKUP env.bare_globals (src,id) = SOME ty /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  expr_sim_inv cenv cx env ee /\
  ?imms v. ALOOKUP ee.immutables cx.txn.target = SOME imms /\
    FLOOKUP (get_source_immutables src imms) id = SOME (tv,v) /\
    value_has_type tv v
Proof
  strip_tac >>
  `expr_sim_inv cenv cx env ee` by
    metis_tac[bodySimStmtFactsTheory.expr_body_pre_eval] >>
  drule_all immutable_augassign_entry >> strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem augassign_storage_current_root:
  eval_target_place cx bt es = (INL (StoragePlace tr slot tv),st) /\
  MEM (StorageRoot tr root rtv) st.storage_trace /\
  storage_subregion rtv path delta tv /\
  slot = n2w root + n2w delta /\
  bind (eval_expr cx e) (read_result cx) st = (INL rhs,ee) ==>
  MEM (StorageRoot tr root rtv) ee.storage_trace /\
  storage_subregion rtv path delta tv /\
  slot = n2w root + n2w delta /\
  ?target_events rhs_events.
    st.storage_trace = es.storage_trace ++ target_events /\
    ee.storage_trace = st.storage_trace ++ rhs_events
Proof
  strip_tac >>
  `storage_trace_frame (eval_target_place cx bt)` by
    metis_tac[cj 8 evaluate_storage_trace_frame] >>
  `storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
    (irule storage_trace_frame_bind_all >>
     simp[cj 5 evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
  `?target_events. st.storage_trace = es.storage_trace ++ target_events` by
    metis_tac[storage_trace_frame_prefix] >>
  `?rhs_events. ee.storage_trace = st.storage_trace ++ rhs_events` by
    metis_tac[storage_trace_frame_prefix] >>
  gvs[MEM_APPEND] >> metis_tac[]
QED
