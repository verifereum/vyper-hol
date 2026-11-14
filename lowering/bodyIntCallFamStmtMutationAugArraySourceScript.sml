(* Source preparation for an effectful counted array index. *)
Theory bodyIntCallFamStmtMutationAugArraySource
Ancestors
  bodyIntCallFamStmtMutationAugIndexFrame bodyIntCallFamStmtMutationAugIndexLive
  bodyIntCallJointContract bodyIntCallJointAggCore
  targetSubscriptSplit targetSubscriptStorage targetSubscriptMemory targetLocalLive targetPlaceSimCasesBase
  targetPlaceSim targetPlaceSimDefs exprSimIfExp exprSimHypsDefs exprSimDefs loweringPosts
  exprBopSimProps vyperTypeSystem vyperTyping vyperInterpreter vyperState
  vyperValue vyperTypeEnv vyperTypeInvariants loweringStateRelDefs
  stmtSimForArrayFrame gasSummary gasContext compileEnv
  exprSimBinopFrag valueEncoding exprSimPopNestedLocalHandoff

Theorem intcall_target_array_index_ready:
  target_pre ce fp.jc_cx env (SubscriptTarget bt e) es /\
  type_place_target env bt = SOME (Type (ArrayT ety bd)) /\
  subscript_vtype (Type (ArrayT ety bd)) (expr_type e) = SOME vt /\
  gas_marked_exec F (fp.jc_ctx,fp.jc_func) (eval_base_place fp.jc_cx bt)
    (es,s0) left (INL pv) mid (OK t) /\
  gas_marked_exec F (fp.jc_ctx,fp.jc_func)
    (bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx))
    (mid with gas_obs := [],t) right (INL key) ee (OK u) /\
  target_post fp.jc_ctx fp.jc_func ce fp.jc_cx es sa sm s0
    (mid with gas_obs := []) pv (Type (ArrayT ety bd)) rb t /\
  intcall_expr_cont fp ce env es sa s0 (mid with gas_obs := []) sm t /\
  intcall_expr_cont fp ce env (mid with gas_obs := []) sm t
    (ee with gas_obs := []) sn u /\
  expr_val_rel fp.jc_cx (post_value_type ce e) key ix u /\
  stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s0 /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sn.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\ (!l. FST rb <> Label l) ==>
  ?i itv. key = IntV i /\
    evaluate_type (get_tenv fp.jc_cx) (expr_type e) = SOME itv /\
    value_has_type itv (IntV i) /\ eval_operand ix u = SOME (i2w i) /\
    target_post fp.jc_ctx fp.jc_func ce fp.jc_cx es sa sn s0
      (ee with gas_obs := []) pv (Type (ArrayT ety bd)) rb u /\
    MAP FDOM es.scopes = MAP FDOM (ee with gas_obs := []).scopes /\
    (!id path. pv = PlaceR (MemoryPlace id path) ==>
      ?entry av. lookup_scopes id (ee with gas_obs := []).scopes = SOME entry /\
        evaluate_subscripts entry.type entry.value path = INL (ArrayV av)) /\
    (!tr slot tv. pv = PlaceR (StoragePlace tr slot tv) ==>
      storage_read_live fp.jc_cx tr (get_storage fp.jc_cx (ee with gas_obs := []) tr) slot tv /\
      w2n slot + type_slot_size tv <= dimword(:256) /\
      (!etv cnt. tv = ArrayTV etv (Dynamic cnt) ==>
        w2n (lookup_storage slot (get_storage fp.jc_cx (ee with gas_obs := []) tr)) <= cnt))
Proof
  strip_tac >>
  qabbrev_tac `fin = ee with gas_obs := []` >>
  qabbrev_tac `gs = gas_explicit right t.vs_gas_readings` >>
  `eval_base_place fp.jc_cx bt
    (es with gas_obs := gas_explicit left s0.vs_gas_readings ++ gs) =
    (INL pv,mid with gas_obs := gs)` by
    (drule target_subscript_marked_base_source >> simp[]) >>
  `bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)
     (mid with gas_obs := gs) = (INL key,fin)` by
    (qpat_x_assum `gas_marked_exec _ _ (bind _ _) _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >>
     simp[Abbr `fin`, Abbr `gs`]) >>
  `expr_body_pre ce fp.jc_cx env e (mid with gas_obs := gs)` by
    (fs[target_pre_def, target_indices_pre_def] >>
     first_x_assum irule >>
     fs[intcall_expr_cont_def, intcall_expr_res_def]) >>
  `?itv. evaluate_type (get_tenv fp.jc_cx) (expr_type e) = SOME itv /\
     value_has_type itv key` by
    (drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) ifexp_body_pre_read_typed) >> simp[]) >>
  `is_int_type (expr_type e)` by
    (Cases_on `bd` >> fs[subscript_vtype_def, AllCaseEqs()]) >>
  `?i. key = IntV i /\ eval_operand ix u = SOME (i2w i)` by suspend "key" >>
  gvs[] >>
  suspend "ready"
QED

Resume intcall_target_array_index_ready[key]:
  drule_all int_type_value >> strip_tac >>
  `post_value_type ce e = expr_type e` by
    (irule post_value_type_word >>
     Cases_on `expr_type e` >> gvs[is_int_type_def] >>
     rename1 `BaseT bty` >> Cases_on `bty` >>
     gvs[is_int_type_def, is_word_type_def]) >>
  gvs[] >> Cases_on `expr_type e` >> gvs[is_int_type_def] >>
  rename1 `expr_type e = BaseT bty` >> Cases_on `bty` >>
  gvs[is_int_type_def, evaluate_type_def, expr_val_rel_def,
      is_word_type_def, typed_val_to_w256_def, val_to_w256_def]
QED

Resume intcall_target_array_index_ready[ready]:
  `MAP FDOM es.scopes = MAP FDOM (mid with gas_obs := []).scopes` by
    (drule target_subscript_marked_base_domains >> simp[]) >>
  `MAP FDOM (mid with gas_obs := []).scopes = MAP FDOM fin.scopes` by
    (drule (CONV_RULE (DEPTH_CONV ETA_CONV) bop_marked_scopes_dom) >>
     simp[Abbr `fin`]) >>
  `expr_sim_inv ce fp.jc_cx env fin` by
    fs[intcall_expr_cont_def, intcall_expr_res_def] >>
  `(!id path. pv = PlaceR (MemoryPlace id path) ==>
      ?entry av. lookup_scopes id fin.scopes = SOME entry /\
        evaluate_subscripts entry.type entry.value path = INL (ArrayV av)) /\
   (!tr slot tv. pv = PlaceR (StoragePlace tr slot tv) ==>
      storage_read_live fp.jc_cx tr (get_storage fp.jc_cx fin tr) slot tv /\
      w2n slot + type_slot_size tv <= dimword(:256) /\
      (!etv cnt. tv = ArrayTV etv (Dynamic cnt) ==>
        w2n (lookup_storage slot (get_storage fp.jc_cx fin tr)) <= cnt)) /\
   place_readable fp.jc_cx fin pv` by suspend "live" >>
  `target_post fp.jc_ctx fp.jc_func ce fp.jc_cx es sa sn s0 fin pv
     (Type (ArrayT ety bd)) rb u` by
    (irule intcall_target_index_frame >>
     simp[] >> qexistsl_tac [`env`, `mid with gas_obs := []`, `sm`, `t`] >> simp[]) >>
  simp[] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Resume intcall_target_array_index_ready[live]:
  `(?id. target_root bt = NameTarget id) \/
   (?src id. target_root bt = TopLevelNameTarget (src,id))` by
    (qid_spec_tac `bt` >> recInduct base_assignment_target_induct >>
     simp[target_root_def] >> Cases_on `nsid` >> simp[])
  >- suspend "local" >>
  suspend "storage"
QED

Resume intcall_target_array_index_ready[local]:
  `target_pre ce fp.jc_cx env (SubscriptTarget bt e)
     (es with gas_obs := gas_explicit left s0.vs_gas_readings ++ gs)` by simp[] >>
  drule_at (Pat `eval_base_place _ _ _ = _`) local_subscript_index_live >>
  simp[] >> disch_then drule_all >> strip_tac >> gvs[] >>
  `place_readable fp.jc_cx fin (PlaceR (MemoryPlace id path))` by
    (irule place_readable_memory_live >> metis_tac[]) >>
  `target_post fp.jc_ctx fp.jc_func ce fp.jc_cx es sa sn s0 fin
     (PlaceR (MemoryPlace id path)) (Type (ArrayT ety bd)) rb u` by
    (irule intcall_target_index_frame >> simp[] >>
     qexistsl_tac [`env`, `mid with gas_obs := []`, `sm`, `t`] >> simp[]) >>
  drule_all target_subscript_memory_array_ready >> strip_tac >> gvs[]
QED

Resume intcall_target_array_index_ready[storage]:
  `(!id path. pv <> PlaceR (MemoryPlace id path))` by
    (rpt strip_tac >> gvs[] >>
     drule eval_base_place_memory_root >> simp[place_access_target_root]) >>
  `place_readable fp.jc_cx fin pv` by suspend "storage_readable" >>
  simp[] >> rpt gen_tac >> strip_tac >> gvs[] >>
  drule_at (Pat `eval_base_place _ _ _ = _`) eval_base_place_storage_ready >>
  disch_then (qspec_then `fin` mp_tac) >>
  fs[expr_sim_inv_def] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Resume intcall_target_array_index_ready[storage_readable]:
  drule_all target_subscript_storage_index_readable >> simp[]
QED

Finalise intcall_target_array_index_ready
