(* The no-copy aggregate snapshot retains the actual child endpoint. *)
Theory bodyExtPosAggregateRetainedMods
Ancestors
  bodyExtPosSavedRowMods bodySavedRhsSlotLiveMods bodyCopyReadPhysicalTypeMods
  createCtorSnapshotByteRetagMods bodyMemoryDefs
  exprPtrUnwrapStorageShape exprLoweringProps fragGasOriginPtr vyperStorageFootprint
  vyperStorageTrace valueEncodingTyping exprLowering loweringPosts bodyFullPostsMods
  compileEnv vyperInterpreter bodyPtrDefs exprSimMemDefs vyperState valueCopyBytes context
Libs monadsyntax

Theorem retained_representation[local]:
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  vv_holds_mods ce cx (post_value_type ce e) raw vv ee s /\
  ~is_word_type (lowered_value_type ce e) ==>
  ((?tag op. ext_call_arg_value (lowered_value_type ce e) vv = StackValue tag op) \/
   (?p. ext_call_arg_value (lowered_value_type ce e) vv =
          LocatedValue (lowered_value_type ce e) p /\ p.ptr_location = LocMemory) \/
   (?p. ext_call_arg_value (lowered_value_type ce e) vv =
          LocatedValue (lowered_value_type ce e) p /\ p.ptr_location <> LocMemory /\
        lowered_value_type ce e = expr_type e /\
        ext_call_arg_value (lowered_value_type ce e) vv = vv))
Proof
  strip_tac >> Cases_on `vv` >> simp[ext_call_arg_value_def] >>
  rename1 `LocatedValue tag p` >> Cases_on `p.ptr_location = LocMemory` >> simp[] >>
  drule_all_then assume_tac compile_nonmemory_lowered_value_type >>
  `post_value_type ce e = expr_type e` by simp[post_value_type_lowered] >>
  Cases_on `p.ptr_location = LocCode` >> gvs[vv_holds_mods_def,vv_holds_def]
QED

Theorem retained_value[local]:
  vv_holds_mods ce cx (post_value_type ce e) raw vv ee s /\
  vv_at ce cx (post_value_type ce e) sa sm ee raw vv s /\
  ptr_vv_ok cx (post_value_type ce e) raw vv ee G tn s /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee raw vv s /\
  read_result cx raw ee = (INL v,ee) /\
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  ~is_word_type (post_value_type ce e) /\ ~is_word_type (lowered_value_type ce e) /\
  (post_value_type ce e = lowered_value_type ce e \/
    is_bytestring_type (post_value_type ce e) /\ is_bytestring_type (lowered_value_type ce e)) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME pt /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
  value_has_type pt v /\ value_has_type rt v ==>
  ?saved. read_result cx saved ee = (INL v,ee) /\
    vv_holds_mods ce cx (lowered_value_type ce e) saved
      (ext_call_arg_value (lowered_value_type ce e) vv) ee s /\
    vv_at ce cx (lowered_value_type ce e) sa sm ee saved
      (ext_call_arg_value (lowered_value_type ce e) vv) s /\
    ptr_vv_ok cx (lowered_value_type ce e) saved
      (ext_call_arg_value (lowered_value_type ce e) vv) ee G tn s /\
    vv_store_bound cx (lowered_value_type ce e) (lowered_value_type ce e) ee saved
      (ext_call_arg_value (lowered_value_type ce e) vv) s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `val_wf rt v` by (irule (CONJUNCT1 valueEncodingTypingTheory.value_has_type_val_wf) >> simp[]) >>
  Cases_on `(?tag op. vv = StackValue tag op) \/
            (?tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory)`
  >- (Cases_on `is_bytestring_type (post_value_type ce e) /\
                is_bytestring_type (lowered_value_type ce e)`
      >- (qexists_tac `Value v` >> simp[read_result_def,vyperStateTheory.return_def] >>
          irule ctor_snapshot_bytes_retag_mods >> simp[] >>
          qexistsl [`pt`,`raw`,`post_value_type ce e`] >> simp[]) >>
      `post_value_type ce e = lowered_value_type ce e` by metis_tac[] >>
      qexists_tac `raw` >>
      Cases_on `vv` >- gvs[ext_call_arg_value_def] >>
      rename1 `LocatedValue tag p` >> gvs[] >>
      `tag = lowered_value_type ce e` by fs[vv_holds_mods_def,vv_holds_def] >>
      gvs[ext_call_arg_value_def]) >>
  Cases_on `vv` >> gvs[] >> rename1 `LocatedValue tag p` >>
  drule_all_then assume_tac compile_nonmemory_lowered_value_type >>
  `post_value_type ce e = expr_type e` by simp[post_value_type_lowered] >>
  `tag = expr_type e` by
    (Cases_on `p.ptr_location = LocCode` >> gvs[vv_holds_mods_def,vv_holds_def]) >>
  qexists_tac `raw` >> gvs[ext_call_arg_value_def]
QED

Theorem ext_pos_aggregate_retained_landing_mods:
  contract_inv mods exps ctx ce cx /\ module_body_inv mods src tops ce cx /\
  expr_body_pre_mods mods ce cx env e es /\
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  ~is_word_type (expr_type e) /\
  ~is_word_type (vv_type (ext_call_arg_value (lowered_value_type ce e) vv)) /\
  compile_snapshot_vv ce F (ext_call_arg_value (lowered_value_type ce e) vv) sm = (sv,ss) /\
  ~exprs_can_mutate ce (xs ++ kw_es) /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d ce sa s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> storage_well_formed_on cx es (FST H)) /\
  eval_expr cx e (es with gas_obs := gs) = (INL tv,ee) /\
  read_result cx tv ee = (INL v,ee) /\ ~s.vs_halted /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx e es sa sm s0 ee tv vv s /\
    vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee tv vv s /\
    s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
    alloca_history func s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    s0.vs_alloca_next <= s.vs_alloca_next /\ ghost_inv_at_mods (DF H) lo d ce cx ee G tn s /\
    ptr_vv_ok cx (post_value_type ce e) tv vv ee G tn s /\
    (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
      ?val. read_result cx tv ee = (INL val,ee) /\
        !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
          eval_operand (vv_operand vv) s = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory rt val (w2n w) mem)) /\
    (!tag op. vv = StackValue tag op /\ ~is_word_type (post_value_type ce e) ==>
      ptr_buf_ok ce e op G s) /\
    (!tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok ce e p.ptr_operand G s) /\ ghost_kept_at lo ce es sa G0 tn0 s0 G tn) ==>
  ?u Gu tu. !H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tu) /\
    ext_pos_saved_row_mods lo ce cx (xs ++ kw_es) sa ss H e sv v ee Gu tu u /\
    stmt_state_rel H ctx func ce cx ee u /\ immutable_frame_mods func ce cx ee u /\
    storage_well_formed_on cx ee (FST H) /\
    return_buf_frame d ce ss u /\ ghost_inv_at_mods (DF H) lo d ce cx ee Gu tu u /\
    ghost_kept_at lo ce es sa G0 tn0 s0 Gu tu /\
    alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    s0.vs_alloca_next <= u.vs_alloca_next /\ ~u.vs_halted /\
    u.vs_current_bb = ss.cs_current_bb /\ u.vs_inst_idx = LENGTH ss.cs_current_insts /\
    wb_frame ce es ee sa s0 u /\ (~expr_has_effect e ==> pure_frame ce func es sa s0 u) /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qexistsl [`s`,`G`,`tn`] >> qx_gen_tac `H` >> disch_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _` (drule_then strip_assume_tac) >>
  `storage_trace_frame (eval_expr cx e)` by simp[evaluate_storage_trace_frame] >>
  `valid_horizon cx st0 H es.storage_trace` by
    (drule_all valid_horizon_frame >> simp[]) >>
  `storage_well_formed_on cx es (FST H)` by simp[] >>
  drule_all_then assume_tac saved_rhs_slot_live_mods >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (qspec_then `sa` mp_tac (Q.SPECL [`ce`,`expr_type e`,`e`] (CONJUNCT1 compile_expr_ci_mono)) >>
     simp[ci_mono_def]) >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee)` by
    simp[vyperStateTheory.bind_def] >>
  drule_all_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac strip_assume_tac))
    copy_read_physical_type_gas_obs_mods >>
  `~is_word_type (lowered_value_type ce e)` by metis_tac[is_bytestring_word_type] >>
  `sv = ext_call_arg_value (lowered_value_type ce e) vv /\ ss = sm` by
    (qpat_assum `compile_snapshot_vv _ _ _ _ = _` mp_tac >>
     pure_rewrite_tac[compile_snapshot_vv_def] >> asm_rewrite_tac[] >>
     simp[comp_return_def] >> strip_tac >> simp[]) >>
  qpat_x_assum `ss = sm` SUBST_ALL_TAC >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK s,G,tn)` by
    (irule (CONJUNCT1 gas_origin_ptr_path_rules) >> simp[]) >>
  qpat_x_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _` (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  `return_buf_frame d ce sm s` by (irule return_buf_frame_frame >> simp[] >> metis_tac[]) >>
  `wb_frame ce es ee sa s0 s` by (rewrite_tac[wb_frame_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  simp[] >>
  `ext_pos_saved_row_mods lo ce cx (xs ++ kw_es) sa sm H e sv v ee G tn s` suffices_by simp[] >>
  qpat_x_assum `sv = _` SUBST_ALL_TAC >>
  drule_all_then assume_tac retained_representation >>
  drule_all_then strip_assume_tac retained_value >>
  rewrite_tac[ext_pos_saved_row_mods_def] >> conj_tac
  >- (qexistsl [`sa`,`sm`,`sm`,`vv`,`saved`,`F`] >> asm_rewrite_tac[] >> simp[]) >>
  Cases_on `vv` >- fs[ext_call_arg_value_def,vv_location_def] >>
  rename1 `LocatedValue tag p` >>
  Cases_on `p.ptr_location = LocMemory`
  >- fs[ext_call_arg_value_def,vv_location_def] >>
  drule_all_then assume_tac compile_nonmemory_lowered_value_type >>
  `post_value_type ce e = expr_type e` by simp[post_value_type_lowered] >>
  `tag = expr_type e` by
    (Cases_on `p.ptr_location = LocCode` >> gvs[vv_holds_mods_def,vv_holds_def]) >>
  gvs[ext_call_arg_value_def,vv_location_def]
QED
