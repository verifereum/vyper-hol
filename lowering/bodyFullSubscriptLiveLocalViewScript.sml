(* A captured local path need not remain in the current value after the index.
   The row theorem uses the original path and the actual final source read. *)
Theory bodyFullSubscriptLiveLocalView
Ancestors
  bodyFullSubscriptLocalCutOrigin bodyFullSubscriptCoveredRow
  abiEncodeArgsSim stateRelProj nameLoweringProps exprBopSimProps
  exprSimSubscriptArraySource exprSimProps exprSimSource exprSimHypsDefs
  bodyPtrDefs bodyPtrBopHashFootprint bodyPtrBopInMemoryContents
  exprPtrUnwrapFacts typedMemoryCopy valueEncodingTyping valueEncodingProps
  loweringPosts loweringStateRelDefs ptrDiscipline vyperPlaceTyping vyperTypeStatePreservation
  vyperPlaceResultTyping vyperTypeEvalProofs vyperTypeValues vyperState
  vyperTyping vyperValue context venomState words finite_map arithmetic

Theorem subscript_live_local_index_view:
  expr_body_pre ce cx env (Subscript ann obj idx) es /\
  expr_type obj = ArrayT et bd /\ ~base_from_pop obj /\
  post_value_type ce obj = expr_type obj /\
  eval_expr cx obj (es with gas_obs := gs1) = (INL (PlaceR (MemoryPlace id path)),mid) /\
  bind (eval_expr cx idx) (read_result cx) (mid with gas_obs := gs2) = (INL key,fin) /\
  stmt_state_rel H ctx fn ce cx es s0 /\
  vv_post H ctx fn ce cx obj es sa sm s0 mid (PlaceR (MemoryPlace id path))
    (LocatedValue t p) s /\
  expr_post H ctx fn ce cx idx mid sm sn s fin key iop u /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\ (!l. p.ptr_operand <> Label l) /\
  ptr_vv_ok cx (post_value_type ce obj) (PlaceR (MemoryPlace id path))
    (LocatedValue t p) mid Gm tnm s /\
  ghost_inv_at D lo d ce cx es G0 tn0 s0 /\
  ghost_inv_at D lo d ce cx fin Gi tni u /\
  ghost_kept_at lo ce es sa G0 tn0 s0 Gm tnm /\
  ghost_kept_at lo ce mid sm Gm tnm s Gi tni ==>
  p.ptr_location = LocMemory /\
  vv_place_ptr ce cx fin u (PlaceR (MemoryPlace id path)) (LocatedValue t p) /\
  ptr_vv_ok cx (expr_type obj) (PlaceR (MemoryPlace id path)) (LocatedValue t p) fin Gi tni u /\
  popped_keys_indexed fin.scopes /\
  op_taint tni p.ptr_operand = {} /\ op_prov Gi p.ptr_operand = op_prov Gm p.ptr_operand /\
  ?etv a v q B sz k.
    evaluate_type (get_tenv cx) et = SOME etv /\
    evaluate_type (get_tenv cx) (expr_type obj) = SOME (ArrayTV etv bd) /\
    runtime_place_typed cx fin (MemoryPlace id path) (ArrayTV etv bd) /\
    read_result cx (PlaceR (MemoryPlace id path)) fin = (INL v,fin) /\
    value_has_type (ArrayTV etv bd) v /\ val_wf (ArrayTV etv bd) v /\
    well_formed_type_value (ArrayTV etv bd) /\
    eval_operand p.ptr_operand s = SOME a /\ eval_operand p.ptr_operand u = SOME a /\
    place_ptr_rel ce cx u (PlaceR (MemoryPlace id path)) a (SOME LocMemory)
      (Type (expr_type obj)) /\
    FLOOKUP ce.ce_vars id = SOME (PtrVar (Var q) sz) /\ lookup_var q u = SOME B /\
    w2n a = w2n B + k /\ k + type_memory_size (ArrayTV etv bd) <= sz /\
    w2n a + type_memory_size (ArrayTV etv bd) < dimword (:256) /\
    (!mem. mem_agree_outside tni.t_mem u.vs_memory mem ==>
      val_in_memory (ArrayTV etv bd) v (w2n a) mem) /\
    (!cap. bd = Dynamic cap ==>
      ?vs x b n. v = ArrayV (DynArrayV vs) /\ LENGTH vs <= cap /\
        mload (w2n a) u = n2w (LENGTH vs) /\ mem_word_taint tni.t_mem (w2n a) = {} /\
        p.ptr_operand = Var x /\ FLOOKUP Gi x = SOME (b,n) /\ b <= w2n a /\
        w2n a + 32 + cap * type_memory_size etv <= b + n /\ ptr_covers Gi tni x u 32)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac subscript_local_cut_returned_paths >>
  `expr_body_pre ce cx env obj (es with gas_obs := gs1)` by
    (`expr_body_pre ce cx env obj es` suffices_by simp[] >>
     (qpat_assum `expr_body_pre _ _ _ (Subscript _ _ _) _`
        (mp_then Any irule exprSimSubscriptArraySourceTheory.expr_body_pre_array_subscript_base_eval) >>
      qpat_assum `eval_expr cx obj _ = (INL _,_)` (irule_at Any) >> simp[])) >>
  drule_all_then strip_assume_tac expr_body_pre_place_metadata >>
  `expr_body_pre ce cx env (Subscript ann obj idx) (es with gas_obs := gs1)` by simp[] >>
  `expr_body_pre ce cx env idx (mid with gas_obs := gs2)` by
    (drule_all expr_body_pre_array_subscript_index_after_base >> simp[]) >>
  `popped_keys_indexed fin.scopes` by
    (qpat_assum `bind _ _ _ = _` (mp_then Any mp_tac vyperStatePreservationTheory.bind_split) >>
     simp[sumTheory.sum_distinct] >> strip_tac >>
     drule read_result_state >> disch_then (SUBST_ALL_TAC o SYM) >>
     metis_tac[expr_body_pre_popped_keys_indexed]) >>
  `expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
  drule_all_then strip_assume_tac abi_args_local_type_coherent >>
  qpat_x_assum `typed_scope_transition es fin` (strip_assume_tac o REWRITE_RULE [typed_scope_transition_def]) >>
  drule_all_then strip_assume_tac scope_pop_trace_lookup >>
  drule_then strip_assume_tac entry_pop_trace_metadata >>
  drule_all_then assume_tac entry_events_valid >>
  qpat_x_assum `runtime_place_typed cx mid _ _`
    (strip_assume_tac o REWRITE_RULE [runtime_place_typed_memory]) >>
  rename1 `lookup_scopes id mid.scopes = SOME em` >>
  `em.type = initial.type` by
    (`expr_body_pre ce cx env idx mid` by metis_tac[expr_body_pre_gas_obs] >>
     `expr_sim_inv ce cx env mid` by fs[expr_body_pre_def] >>
     `?ty'. ce.ce_var_type id = SOME ty' /\ evaluate_type (get_tenv cx) ty' = SOME em.type` by
       (irule abi_args_local_type_coherent >> metis_tac[]) >> gvs[]) >>
  qhdtm_assum `vv_post`
    (strip_assume_tac o REWRITE_RULE [vv_post_def]) >>
  qhdtm_assum `expr_post`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  qpat_assum `vv_place_ptr _ _ mid _ _ _`
    (strip_assume_tac o SRULE [vv_place_ptr_def]) >>
  rename1 `FLOOKUP ce.ce_vars id = SOME (PtrVar (Var q) sz)` >>
  rename1 `lookup_var q s = SOME B` >>
  `mem_path_offset initial.type path = SOME (k,tvk)` by metis_tac[optionTheory.SOME_11] >>
  drule_then strip_assume_tac mem_path_offset_sound >>
  `tvk = tv` by metis_tac[optionTheory.SOME_11] >>
  `local_ptrs_rel fn ce es.scopes s0` by metis_tac[stmt_state_rel_local_ptrs_alloca] >>
  drule_all_then strip_assume_tac local_ptrs_rel_value >>
  `not_fresh_at sa q /\ not_fresh_at sm q` by metis_tac[local_ptrs_reserved_def] >>
  `lookup_var q s0 = SOME B /\ lookup_var q u = SOME B` by
    (fs[eval_operand_def] >> metis_tac[optionTheory.SOME_11]) >>
  `local_region ce mid.scopes s id (w2n B) sz` by simp[local_region_def] >>
  `w2n B + sz < dimword (:256)` by metis_tac[stmt_state_rel_region_lt] >>
  qabbrev_tac `a = B + n2w k` >>
  `eval_operand p.ptr_operand u = SOME a` by
    (irule eval_operand_frame >> simp[] >> qexistsl [`sm`,`s`] >> simp[]) >>
  `w2n a = w2n B + k` by
    (`k < dimword (:256) /\ w2n B + k < dimword (:256)` by decide_tac >>
     simp[Abbr `a`, w2n_add_2, w2n_n2w]) >>
  `popped_kept ce es fin s0 u` by
    (`locals_kept ce es fin s0 u` by (irule locals_kept_trans >> metis_tac[]) >>
     fs[locals_kept_def]) >>
  `value_has_type initial.type initial.value` by
    metis_tac[lookup_scopes_state_well_typed_value_has_type] >>
  `value_has_type entry'.type entry'.value` by
    metis_tac[lookup_scopes_state_well_typed_value_has_type] >>
  `well_formed_type_value initial.type` by metis_tac[evaluate_type_well_formed_type_value] >>
  `?v. read_result cx (PlaceR (MemoryPlace id path)) fin = (INL v,fin) /\
       value_has_type tv v /\ well_formed_type_value tv /\ k + type_memory_size tv <= sz /\
       !mem. mem_agree_outside tni.t_mem u.vs_memory mem ==>
             val_in_memory tv v (w2n a) mem` by
    (irule subscript_covered_row_read_robust >>
     qpat_assum `entry_pop_trace initial _ entry'` (irule_at Any) >>
     qpat_assum `local_region ce mid.scopes s id _ sz` (irule_at Any) >>
     qpat_assum `ghost_inv_at D lo d ce cx es G0 tn0 s0` (irule_at Any) >>
     qpat_assum `ghost_inv_at D lo d ce cx fin Gi tni u` (irule_at Any) >>
     qpat_assum `evaluate_subscripts initial.type initial.value path = INL v0` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo ce es sa G0 tn0 s0 Gm tnm` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo ce mid sm Gm tnm s Gi tni` (irule_at Any) >>
     fs[]) >>
  `?etv. evaluate_type (get_tenv cx) et = SOME etv /\ tv = ArrayTV etv bd` by
    (qpat_assum `evaluate_type (get_tenv cx) (expr_type obj) = SOME tv` mp_tac >>
     simp[] >> metis_tac[evaluate_type_ArrayT_cases]) >>
  `runtime_place_typed cx fin (MemoryPlace id path) tv` by
    (simp[runtime_place_typed_memory] >> qexists `entry'` >> fs[]) >>
  `vv_place_ptr ce cx fin u (PlaceR (MemoryPlace id path)) (LocatedValue t p)` by
    (simp[vv_place_ptr_def, Abbr `a`] >> metis_tac[]) >>
  `place_ptr_rel ce cx u (PlaceR (MemoryPlace id path)) a (SOME LocMemory)
     (Type (expr_type obj))` by
    (simp[place_ptr_rel_def, Abbr `a`] >> metis_tac[]) >>
  `w2n a + type_memory_size tv < dimword (:256)` by decide_tac >>
  `val_wf tv v` by metis_tac[value_has_type_val_wf] >>
  `op_taint tnm p.ptr_operand = {} /\
   ?vm. ptr_mem_ok cx (expr_type obj) vm p.ptr_operand Gm tnm s` by
    (qpat_assum `ptr_vv_ok _ _ _ _ mid _ _ _` (mp_tac o REWRITE_RULE [ptr_vv_ok_def]) >>
     simp[] >> strip_tac >> goal_assum (drule_at Any)) >>
  `op_taint tni p.ptr_operand = {} /\
   op_prov Gi p.ptr_operand = op_prov Gm p.ptr_operand` by
    (qpat_assum `ghost_kept_at lo ce mid sm Gm tnm s Gi tni` mp_tac >>
     Cases_on `p.ptr_operand` >> fs[ghost_kept_at_def, op_prov_def, op_taint_def]) >>
  `!z. val_footprint tv z = type_memory_size tv /\
       val_store_size tv z = type_memory_size tv` by
    (gen_tac >> Cases_on `z` >> simp[val_footprint_def, val_store_size_def]) >>
  `type_memory_size tv <> 0 ==>
     ?x b n. p.ptr_operand = Var x /\ FLOOKUP Gi x = SOME (b,n) /\
             b <= w2n a /\ w2n a + type_memory_size tv <= b + n` by
    (strip_tac >>
     `val_footprint tv vm <> 0` by gvs[] >>
     drule_all_then strip_assume_tac ptr_mem_ok_bounds >>
     gvs[op_prov_def] >> goal_assum (drule_at Any) >> simp[]) >>
  `ptr_mem_ok cx (expr_type obj) v p.ptr_operand Gi tni u` by
    gvs[ptr_mem_ok_def] >>
  `ptr_vv_ok cx (expr_type obj) (PlaceR (MemoryPlace id path)) (LocatedValue t p)
      fin Gi tni u` by gvs[ptr_vv_ok_def] >>
  rpt (conj_tac >- simp[]) >>
  qexistsl [`etv`,`a`,`v`,`q`,`B`,`sz`,`k`] >>
  rpt (conj_tac >- gvs[]) >>
  gen_tac >> disch_then SUBST_ALL_TAC >>
  qpat_x_assum `tv = ArrayTV _ _` SUBST_ALL_TAC >>
  drule_then strip_assume_tac typed_copy_dynarray_typed_value >>
  `!mem. mem_agree_outside tni.t_mem u.vs_memory mem ==>
         val_in_memory (ArrayTV etv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n a) mem` by
    gvs[] >>
  `mload (w2n a) u = n2w (LENGTH vs)` by
    (drule typedCopyLayoutPtrTheory.dynarray_in_memory_robust_length >>
     disch_then (qspec_then `u.vs_memory` mp_tac) >>
     simp[mem_agree_outside_def, mem_word_at_eq_mload]) >>
  `mem_word_taint tni.t_mem (w2n a) = {}` by
    (drule dynarray_memory_header_clean >> simp[]) >>
  `?x b n. p.ptr_operand = Var x /\ FLOOKUP Gi x = SOME (b,n) /\
           b <= w2n a /\ w2n a + 32 + cap * type_memory_size etv <= b + n` by
    fs[valueEncodingTheory.type_memory_size_def] >>
  qexistsl [`vs`,`x`,`b`,`n`] >> simp[] >>
  `lookup_var x u = SOME a` by fs[eval_operand_def] >>
  fs[ptr_covers_def]
QED
