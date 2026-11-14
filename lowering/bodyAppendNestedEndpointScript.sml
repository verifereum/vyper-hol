(* Storage endpoint for aggregate Append below a declared root. *)
Theory bodyAppendNestedEndpoint
Ancestors
  tuplePlaceSourceHead stmtSimAugAssignPlaceStorage exprSimPopNestedBase
  appendNestedAggregateRel accountsRelProps exprSimHypsDefs targetPlaceSim
  bodySim supportedTargets vyperTypeInvariants vyperTypeSystem
  vyperStorageLayoutSafety vyperStoragePlaceRegion vyperState vyperValue
  vyperInterpreter targetPlaceSimDefs targetPlaceSimCases
  stmtSimDefs stmtSimStoreCopyState loweringStateRelDefs
  valueEncodingProps words targetSubscriptSplit bodyAppendResolvedPre
  exprSimSource exprSimHyps bodyAppendStorageAdapter vyperTypeInvariants
  vyperTyping valueEncodingTyping vyperTypeExprResult
  vyperTypeExprSoundness exprSimProps

Theorem body_append_nested_storage_endpoint:
  body_inv tops ctx cenv cx /\ target_pre cenv cx env bt es /\
  supported_target_info tops bindings bt = SOME pt /\
  (?id. target_root bt = TopLevelNameTarget id) /\
  well_typed_target env bt (ArrayT elem (Dynamic cap)) /\
  call_evaluation_safe cx (int_calls_target bt) /\
  evaluate_type (get_tenv cx) elem = SOME tv /\ 0 < type_slot_size tv /\
  eval_target_place cx bt (es with gas_obs := gs) = (INL p,et) ==>
  ?tr slot. p = StoragePlace tr slot (ArrayTV tv (Dynamic cap)) /\
    w2n slot + type_slot_size (ArrayTV tv (Dynamic cap)) <= dimword (:256) /\
    (!raw. storage_read_live cx tr raw slot (ArrayTV tv (Dynamic cap))) /\
    (!es0 s0 u cut (b:bytes32) len v0 writes ks res es1.
      stmt_state_rel ctx func cenv cx es0 s0 /\ local_ptrs_reserved cenv cut /\
      value_has_type tv v0 /\ val_in_memory tv v0 (w2n b) s0.vs_memory /\
      encode_value tv v0 = SOME writes /\
      (!i. MEM i ks <=> MEM i (MAP FST writes)) /\
      w2n b + 32 * type_slot_size tv <= dimword (:256) /\
      len = w2n (lookup_storage slot (get_storage cx es0 tr)) /\ len < cap /\
      store_copy_normalize s0 u =
        (if tr then tstore else sstore) slot (n2w (len+1))
          (FOLDL (\t i. (if tr then tstore else sstore)
            (slot+n2w (1+len*type_slot_size tv)+n2w i)
            (mem_word_at (w2n b+32*i) s0.vs_memory) t) s0 ks) /\
      (!x. not_fresh_at cut x ==> lookup_var x u = lookup_var x s0) /\
      append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v0 es0 = (res,es1) ==>
      res = INL () /\ stmt_state_rel ctx func cenv cx es1 u)
Proof
  strip_tac >>
  `target_pre cenv cx env bt (es with gas_obs := gs)` by
    gvs[target_pre_def] >>
  `well_formed_vtype (get_tenv cx) (Type (ArrayT elem (Dynamic cap)))` by
    (irule target_subscript_pre_result_well_formed >>
     goal_assum (drule_at Any) >> fs[well_typed_target_def]) >>
  `evaluate_type (get_tenv cx) (ArrayT elem (Dynamic cap)) =
    SOME (ArrayTV tv (Dynamic cap))` by
    (gvs[well_formed_vtype_def, well_formed_type_def, evaluate_type_def,
         AllCaseEqs()]) >>
  drule_all tuple_place_source_target_endpoint >> strip_tac >>
  `?tr slot leaf. p = StoragePlace tr slot leaf` by
    (irule aug_place_supported_storage_kind >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[targetPlaceSimTheory.target_root_def]) >>
  gvs[runtime_place_typed_def, place_type_value_def, return_def] >>
  `storage_layout_safe cx` by fs[expr_sim_inv_def] >>
  drule_all nested_pop_storage_natural_region >> strip_tac >>
  conj_tac >- decide_tac >>
  conj_tac
  >- (gen_tac >> irule storage_place_region_read_live >> simp[type_slot_size_def]) >>
  `well_formed_type_value tv` by
    metis_tac[cj 1 vyperTypingTheory.evaluate_type_well_formed] >>
  `!mid' name' subs' k' tv'.
    declared_storage_region cx mid' name' subs' = SOME (tr,k',tv') /\
    (k',tv') <> (root,root_tv) ==>
    ranges_disjoint (w2n root) (type_slot_size root_tv)
                    (w2n k') (type_slot_size tv')` by
    (rpt strip_tac >>
     irule storage_layout_safe_region_separation >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[optionTheory.SOME_11, pairTheory.PAIR_EQ]) >>
  rpt gen_tac >> strip_tac >>
  irule (INST_TYPE [alpha |-> ``:256``] append_nested_aggregate_copy_success_post) >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at (Pat `val_in_memory _ _ _ _`)) >>
  goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
  goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
  qpat_x_assum `slot = root + n2w delta` kall_tac >>
  simp[]
QED

Theorem body_append_nested_rhs_endpoint:
  (!s p t. eval_target_place cx bt s = (INL p,t) ==> body_expr_ok cx e) /\
  body_inv tops ctx cenv cx /\ target_pre cenv cx env bt es /\
  expr_body_pre cenv cx env e es /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  type_memory_bytes cenv (expr_type e) = 32 * type_slot_size tv /\
  eval_target_place cx bt (es with gas_obs := gs) = (INL p,et) ==>
  expr_sim ctx func cenv cx (expr_type e) e et /\
  (!hs v ee.
    bind (eval_expr cx e) (read_result cx) (et with gas_obs := hs) = (INL v,ee) ==>
    value_has_type tv v /\ val_wf tv v /\
    val_footprint tv v <= type_memory_bytes cenv (expr_type e))
Proof
  strip_tac >>
  `target_pre cenv cx env bt (es with gas_obs := gs)` by simp[target_pre_def] >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
  `expr_body_pre cenv cx env e et` by
    metis_tac[append_resolved_rhs_body_pre] >>
  `body_expr_ok cx e` by metis_tac[] >>
  conj_tac >- metis_tac[body_expr_ok_def] >>
  rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env e (et with gas_obs := hs)` by simp[] >>
  qpat_x_assum `expr_body_pre _ _ _ _ es` kall_tac >>
  qpat_x_assum `expr_body_pre _ _ _ _ (es with gas_obs := gs)` kall_tac >>
  qpat_x_assum `expr_body_pre _ _ _ _ et` kall_tac >>
  drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_eval) >> strip_tac >>
  `expr_sim_inv cenv cx env et` by fs[expr_body_pre_def] >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `value_has_type tv v` by
    gvs[expr_result_typed_def, expr_runtime_typed_def,
        value_result_typed_def, value_runtime_typed_def] >>
  `val_wf tv v` by metis_tac[cj 1 value_has_type_val_wf] >>
  `type_memory_size tv = 32 * type_slot_size tv` by
    metis_tac[expr_sim_inv_memory_size] >>
  metis_tac[val_footprint_le]
QED
