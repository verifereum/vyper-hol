(* Select the live local pointer and use the reached Append suffix. *)
Theory bodyAppendMemoryRouteJoinMods
Ancestors
  bodyAppendMemoryLandingMods bodyAppendStageJoinMods bodyWriteTargetStageMods
  bodyWriteSubscriptSourceMods exprBodyPreProps exprSimHypsDefs
  vyperStorageTrace vyperStorageFootprint loweringPosts bodyFullShadowBodyInv
  bodyPtrDefs bodyFullTargetDefs ptrDiscipline venomState compileEnv
  vyperTypeInvariants vyperTypeEnv vyperState finite_map freshWrites
  exprLowering exprLoweringProps
Libs monadsyntax

Theorem append_memory_cursor[local]:
  write_target_post_mods H D lo d ctx func cenv cx bt es sa sp s0 mid
    (PlaceR (MemoryPlace id path)) (Type (ArrayT elem (Dynamic cap))) dst G0 tn0 Gm tm t /\
  lookup_scopes id mid.scopes = SOME initial ==>
  ?p bp. dst = (Var p,SOME LocMemory,SOME (ValPT (ArrayT elem (Dynamic cap)))) /\
    lookup_var p t = SOME bp /\ not_fresh_at sp p /\
    target_ptr_ok cenv (PlaceR (MemoryPlace id path)) dst Gm tm t /\
    place_ptr_rel cenv cx t (PlaceR (MemoryPlace id path)) bp (SOME LocMemory)
      (Type (ArrayT elem (Dynamic cap)))
Proof
  strip_tac >> drule_then strip_assume_tac write_target_post_view_mods >>
  qhdtm_x_assum `write_target_location_mods` mp_tac >>
  simp[write_target_location_mods_def] >> strip_tac >>
  qhdtm_assum `place_ptr_rel` (strip_assume_tac o REWRITE_RULE [place_ptr_rel_def]) >>
  qhdtm_assum `ghost_inv_at_mods` (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >>
  qpat_assum `!name entry p sz. lookup_scopes _ _ = SOME _ /\ _ ==> _`
    (drule_all_then (strip_assume_tac o REWRITE_RULE [ptr_covers_def])) >>
  qhdtm_assum `target_ptr_ok` (strip_assume_tac o REWRITE_RULE [target_ptr_ok_def]) >>
  `op_prov Gm (FST dst) <> NONE` by
    (qpat_assum `!j qs root n. _ ==> op_prov _ _ = _`
       (qspecl_then [`id`,`path`,`p`,`sz`] mp_tac) >>
     (impl_tac >- simp[]) >> disch_tac >> simp[]) >>
  PairCases_on `dst` >> Cases_on `dst0` >> gvs[op_prov_def,eval_operand_def,value_type_place_def]
QED

Theorem append_memory_entry_type[local]:
  expr_sim_inv_mods mods cenv cx env mid /\ lookup_scopes id mid.scopes = SOME initial ==>
  !ty. cenv.ce_var_type id = SOME ty ==> evaluate_type (get_tenv cx) ty = SOME initial.type
Proof
  strip_tac >> gvs[expr_sim_inv_mods_def,env_consistent_def,env_scopes_consistent_def] >>
  `?ety. FLOOKUP env.var_types id = SOME ety` by metis_tac[optionTheory.IS_SOME_EXISTS] >>
  `cenv.ce_var_type id = SOME ety` by
    (qpat_assum `!i t. _ ==> cenv.ce_var_type i = SOME t` irule >> simp[]) >>
  simp[] >> qpat_assum `!i t e. _ ==> evaluate_type _ t = SOME e.type` irule >>
  qexists_tac `id` >> simp[]
QED

Theorem append_memory_route_join_mods:
  contract_inv mods exps ctx cenv cx /\
  expr_body_pre_mods mods cenv cx env e mid /\
  type_widens_to env.type_defs (expr_type e) elem /\ assignable_type (get_tenv cx) elem /\
  stmt_exprs_ok cenv (Append bt e) /\
  target_place_type cenv bt = SOME (ValPT (ArrayT elem (Dynamic cap))) /\
  write_target_entry_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx bt es st0 sa sp shadow_sa shadow_sp dst s0 G0 tn0 /\
  append_rhs_code_mods cenv e elem sp sm shadow_sp shadow_sm op func shadow_func /\
  append_store_code_mods cenv e dst LocMemory elem cap op sm sb func /\
  (?initial v0. lookup_scopes id mid.scopes = SOME initial /\
    evaluate_subscripts initial.type initial.value path = INL v0) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    write_target_post_mods H (DF H) lo d ctx func cenv cx bt es sa sp s0 mid
      (PlaceR (MemoryPlace id path)) (Type (ArrayT elem (Dynamic cap))) dst G0 tn0 Gm tm t) /\
  (!tail. bind (eval_expr cx e) (read_result cx)
    (mid with gas_obs := gas_explicit rhsmarks t.vs_gas_readings ++ tail) =
      (INL v,ee with gas_obs := tail)) /\
  storage_trace_domain cx st0 ee.storage_trace /\ ee.gas_obs = [] /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    append_rhs_post_mods DF lo d ctx func cenv cx e mid sp sm t op Gm tm H v ee G tn u) /\
  gas_admissible (append_place cx (MemoryPlace id path) v) (stmt_res_ok lctx) ee /\
  ci_mono sa sp /\ sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!x len. cenv.ce_return_buf = SOME (PtrVar (Var x) len) ==> not_fresh_at sm x) /\
  (!x len. cenv.ce_return_pc = SOME (PtrVar (Var x) len) ==> not_fresh_at sm x) /\
  return_buf_frame d cenv sm u /\ return_buf_sep d cenv ee u /\ ~u.vs_halted /\
  s0.vs_alloca_next <= u.vs_alloca_next /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
  alloca_frame cenv es sa s0 cenv ee u /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  (!n b sz. local_region cenv ee.scopes u n b sz <=> local_region cenv es.scopes s0 n b sz) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cenv.ce_modules cx st0
    (append_place cx (MemoryPlace id path) v) (ee,u,G,tn)
    (\H res fin Gf tf s. ?ce.
      stmt_lands lctx sb res s /\ ~s.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ ce = cenv) /\
      cenv_top_ext cenv ce fin.scopes /\ stmt_state_rel H ctx func ce cx fin s /\
      immutable_frame_mods func ce cx fin s /\ storage_well_formed_on cx fin (FST H) /\
      return_buf_frame d ce sb s /\ alloca_history func s /\ return_buf_sep d ce fin s /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ s0.vs_alloca_next <= s.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d ce cx fin Gf tf s /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x s = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==>
        FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tf (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame cenv es sa s0 ce fin s /\
      (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
        (!n b len. local_region cenv es.scopes s0 n b len ==> off+sz <= b \/ b+len <= off) /\
        off <= i /\ i < off+sz /\ i IN tf.t_mem ==> i IN tn0.t_mem))
    (append_exit_mods ctx cx RetQ)
Proof
  strip_tac >>
  qpat_assum `!tail. bind _ _ _ = _`
    (qspec_then `[]` (assume_tac o REWRITE_RULE [listTheory.APPEND_NIL])) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> valid_horizon cx st0 H mid.storage_trace` by
    (rpt strip_tac >> qpat_assum `bind _ _ _ = _`
       (mp_then (Pat `f st = _`) mp_tac valid_horizon_frame) >>
     simp[storage_trace_frame_bind,evaluate_storage_trace_frame,storage_trace_frame_read_result]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. _ ==> valid_horizon _ _ _ mid.storage_trace` (drule_then assume_tac) >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
    (drule_then assume_tac) >>
  drule_all_then strip_assume_tac append_memory_cursor >> gvs[] >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  `!ty. cenv.ce_var_type id = SOME ty ==> evaluate_type (get_tenv cx) ty = SOME initial.type` by
    (match_mp_tac append_memory_entry_type >> simp[]) >>
  qhdtm_assum `write_target_entry_mods` (strip_assume_tac o REWRITE_RULE [write_target_entry_mods_def]) >>
  `local_ptrs_reserved cenv sp` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> fs[ci_mono_def]) >>
  `append_rhs_post_mods DF lo d ctx func cenv cx e mid sp sm t op Gm tm
    (storage_trace_horizon ee.storage_trace) v ee G tn u` by simp[] >>
  qhdtm_assum `append_rhs_post_mods` (strip_assume_tac o REWRITE_RULE [append_rhs_post_mods_def]) >>
  qhdtm_assum `append_rhs_code_mods` (strip_assume_tac o REWRITE_RULE [append_rhs_code_mods_def]) >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  qpat_assum `ee with gas_obs := [] = ee` (fn eq =>
    qpat_assum `bind (eval_expr _ _) _ _ = _` (assume_tac o REWRITE_RULE [eq])) >>
  irule (REWRITE_RULE [GSYM append_exit_mods_def, ETA_THM] append_memory_landing_mods) >>
  qpat_assum `compile_get_target_ptr compile_expr cenv bt sa = _` (irule_at Any) >>
  qpat_assum `lower_value compile_expr _ _ _ _ = _` (irule_at Any) >>
  qhdtm_assum `place_ptr_rel` (irule_at Any) >>
  qhdtm_assum `target_ptr_ok` (irule_at Any) >>
  qpat_assum `bind _ _ _ = (INL _,ee)` (irule_at Any) >>
  qpat_assum `lookup_scopes id mid.scopes = _` (irule_at Any) >>
  qpat_assum `evaluate_subscripts _ _ _ = _` (irule_at Any) >>
  qpat_assum `type_widens_to _ _ _` (irule_at Any) >>
  qhdtm_assum `contract_inv` (irule_at Any) >>
  simp[] >> conj_tac
  >- (qx_gen_tac `H` >> disch_tac >>
      `valid_horizon cx st0 H mid.storage_trace` by simp[] >>
      qpat_assum `!K. valid_horizon cx st0 K mid.storage_trace ==> _`
        (qspec_then `H` (drule_then (strip_assume_tac o MATCH_MP write_target_post_view_mods))) >>
      `append_rhs_post_mods DF lo d ctx func cenv cx e mid sp sm t op Gm tm H v ee G tn u` by simp[] >>
      pop_assum (strip_assume_tac o REWRITE_RULE [append_rhs_post_mods_def]) >> simp[]) >>
  fs[append_store_code_mods_def]
QED
