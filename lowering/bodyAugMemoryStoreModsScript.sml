(* Linked writeback of the saved memory place of an augmented assignment. *)
Theory bodyAugMemoryStoreMods
Ancestors
  augAssignFullMemoryStorePath augAssignFullMstoreSafety augAssignFullPathWriteRobust
  bodySimAugPlaceStore placeMemoryStateRebuild bodyFullTargetDefs bodyFullMemoryFrames
  bodyFullPostsMods gasOutcomeFullPostMods bodyFullShared bodyFullUnwrapRun
  exprOpenPrimitives bodyMemoryDefs
  stmtSimAugAssignPlaceMemory stmtSimAssignStore stmtSimDeclStore
  bodyBinopFragMemory emitHelperProps loweringShapeRules stateRelProj loweringPosts exprSimProps
  vyperScopePreservation vyperPlaceFrames vyperTypeInvariants exprBodyPreProps
  vyperStorageFootprint vyperStorageBackend venomMemProps
  exprSimHypsDefs bodySimAugPlaceLoad loweringStateRelDefs exprLoweringProps
  bodyInvSplit bodyFullShadowBodyInv bodyPtrDefs compileEnv ptrDiscipline venomState
  stmtSimDefs stmtSimProps bodySimFull valueEncodingProps valueEncodingProofs
  memoryValueEncoding vyperState tuplePlaceStep vyperLookup venomInst fragExec
  vyperTypeEnvPreservation loweringSlice
  finite_map pred_set rich_list words

Theorem aug_memory_layout[local]:
  expr_sim_inv_mods mods cenv cx env es /\
  stmt_state_rel H ctx func cenv cx es s /\
  lookup_scopes id es.scopes = SOME entry /\
  place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) a
    (SOME LocMemory) (Type ty) /\
  evaluate_type (get_tenv cx) ty = SOME ptv ==>
  ?p sz b k.
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME b /\
    mem_path_offset entry.type path = SOME (k,ptv) /\
    w2n a = w2n b + k /\
    w2n b + sz <= s.vs_alloca_next /\
    k + type_memory_size ptv <= type_memory_size entry.type /\
    type_memory_size entry.type <= sz /\
    value_has_type entry.type entry.value /\ well_formed_type_value entry.type
Proof
  strip_tac >> fs[place_ptr_rel_def] >>
  `evaluate_type (get_tenv cx) t0 = SOME entry.type` by
    (drule expr_sim_inv_mods_env >>
     fs[expr_sim_inv_mods_def, env_consistent_def, env_scopes_consistent_def] >>
     `?ety. FLOOKUP env.var_types id = SOME ety` by metis_tac[optionTheory.IS_SOME_EXISTS] >>
     metis_tac[optionTheory.SOME_11]) >>
  gvs[] >>
  `value_has_type entry.type entry.value /\ well_formed_type_value entry.type` by
    (irule aug_place_lookup_typed >>
     fs[expr_sim_inv_mods_def, state_well_typed_def] >> metis_tac[]) >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  drule_then assume_tac stmt_state_rel_alloca_room >>
  `w2n b + sz <= s.vs_alloca_next /\ type_memory_size entry.type <= sz` by
    (fs[local_ptrs_rel_def] >> first_x_assum drule_all >> simp[]) >>
  `k + type_memory_size ptv <= type_memory_size entry.type` by metis_tac[mem_path_offset_sound] >>
  `s.vs_alloca_next < dimword (:256)` by metis_tac[alloca_room_next_lt] >>
  `w2n (b + n2w k) = w2n b + k` by
    (irule buffer_offset_no_wrap >> qexists_tac `sz` >> decide_tac) >>
  simp[arithmeticTheory.ADD_COMM]
QED

Theorem aug_memory_regions[local]:
  MAP FDOM ee.scopes = MAP FDOM es.scopes ==>
  (local_region cenv ee.scopes (mstore addr wd s with vs_inst_idx := pc) n b sz <=>
   local_region cenv es.scopes s n b sz)
Proof
  strip_tac >> simp[local_region_def, lookup_var_def, mstore_def] >>
  metis_tac[lookup_scopes_same_fdoms_some, optionTheory.IS_SOME_EXISTS]
QED

Theorem aug_memory_prefix[local]:
  contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env es /\
  dead_lo_ok_mods H D lo cenv cx /\ immutable_frame_mods func cenv cx es s /\
  local_region cenv es.scopes s id b sz /\ 0 < sz /\ b <= addr ==>
  mem_bytes_at 0 lo (mstore addr wd s).vs_memory = mem_bytes_at 0 lo s.vs_memory
Proof
  strip_tac >>
  `immutable_decl_sep_mods cenv cx es.scopes s.vs_vars s.vs_allocas s.vs_alloca_next` by
    fs[immutable_frame_mods_def, immutable_alloca_sep_mods_def,
       immutable_decl_sep_mods_def, immutable_alloca_sep_def] >>
  `lo <= b` by (irule body_full_local_region_lower_bound_mods >> metis_tac[]) >>
  irule mstore_mem_bytes_at_disjoint >> decide_tac
QED

Theorem aug_memory_immutable_frame[local]:
  immutable_frame_mods func cenv cx es s /\
  local_region cenv es.scopes s id b sz /\ b <= addr /\ addr+32 <= b+sz /\
  ee.immutables = es.immutables /\ MAP FDOM ee.scopes = MAP FDOM es.scopes ==>
  immutable_frame_mods func cenv cx ee (mstore addr wd s with vs_inst_idx := pc)
Proof
  strip_tac >> drule aug_memory_regions >> strip_tac >>
  fs[immutable_frame_mods_def, immutables_rel_mods_def, immutable_alloca_sep_mods_def] >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >>
      `immutables_rel cenv cx.txn.target src cenv.ce_is_ctor es
         (mstore addr wd s with vs_inst_idx := pc)` suffices_by simp[immutables_rel_def] >>
      irule immutables_rel_mem_agree >> qexists_tac `s` >>
      `immutables_rel cenv cx.txn.target src cenv.ce_is_ctor es s` by metis_tac[] >>
      simp[mstore_memory_nondecreasing] >>
      rpt strip_tac >>
      `immutable_alloca_sep func (cenv with ce_module := src) cx es s` by metis_tac[] >>
      `local_region (cenv with ce_module := src) es.scopes s id b sz` by fs[local_region_def] >>
      `regions_disjoint off (type_memory_size tv) b sz` suffices_by
        (strip_tac >> irule mstore_mem_bytes_at_disjoint >> fs[regions_disjoint_def] >> decide_tac) >>
      qpat_x_assum `immutable_alloca_sep _ _ _ _ _`
        (mp_tac o cj 2 o REWRITE_RULE [immutable_alloca_sep_def]) >>
      simp[] >> disch_then (qspecl_then [`name`,`tv`,`v`,`off`] mp_tac) >>
      simp[] >> strip_tac >> first_x_assum drule >> simp[]) >>
  rpt gen_tac >> disch_tac >> irule immutable_alloca_sep_fields >>
  qexistsl_tac [`s`,`es`] >> simp[mstore_def] >>
  metis_tac[]
QED

(* The post-store local is represented robustly under the reduced taint mask. *)
Theorem aug_memory_local_resources[local]:
  local_ptrs_rel func cenv es.scopes s /\
  ghost_inv_at_mods D lo d cenv cx es G tn s /\
  lookup_scopes id es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\ lookup_var p s = SOME b /\
  mem_path_offset entry.type path = SOME (k,ptv) /\ k+32 <= sz /\
  value_has_type entry.type entry.value /\
  evaluate_subscripts entry.type entry.value path = INL old /\
  store_lays_out etv ptv v /\ value_has_type ptv v /\
  write_place cx (MemoryPlace id path) v es = (INL (),ee) ==>
  !name e q cap.
    lookup_scopes name ee.scopes = SOME e /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var q) cap) ==>
    ptr_covers G tn q s cap /\
    !w mem. lookup_var q s = SOME w /\
      mem_agree_outside (tn.t_mem DIFF {i | w2n b+k <= i /\ i < w2n b+k+32})
        (mstore (w2n b+k) (typed_val_to_w256 etv v) s).vs_memory mem ==>
      val_in_memory e.type e.value (w2n w) mem
Proof
  strip_tac >> drule write_memory_place_entry_update >> strip_tac >> gvs[] >>
  qpat_x_assum `replace_memory_entry _ _ _ = _` mp_tac >>
  simp[replace_memory_entry_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  qpat_x_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[ghost_inv_at_mods_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >> Cases_on `name = id`
  >- suspend "changed" >> suspend "other"
QED

Resume aug_memory_local_resources[changed]:
  gvs[] >> conj_tac >- metis_tac[] >> rpt strip_tac >>
  irule augassign_path_word_store_robust >>
  goal_assum (drule_at (Pat `mem_path_offset _ _ = _`)) >>
  goal_assum (drule_at (Pat `assign_subscripts _ _ _ _ = _`)) >>
  qexistsl_tac [`old`, `s`, `tn.t_mem`, `typed_val_to_w256 etv v`] >>
  fs[store_lays_out_def] >>
  `val_footprint ptv v <= 32` by metis_tac[val_footprint_le] >>
  simp[] >> metis_tac[]
QED

Resume aug_memory_local_resources[other]:
  `lookup_scopes name es.scopes = SOME e` by metis_tac[] >>
  conj_tac >- metis_tac[] >> rpt gen_tac >> strip_tac >>
  `local_region cenv es.scopes s id (w2n b) sz /\
   local_region cenv es.scopes s name (w2n w) cap` by
    (simp[local_region_def] >> metis_tac[]) >>
  `regions_disjoint (w2n b) sz (w2n w) cap` by
    (qpat_assum `local_ptrs_rel _ _ _ _` mp_tac >>
     rewrite_tac[local_ptrs_rel_def] >> metis_tac[]) >>
  `w2n w + cap <= w2n b+k \/ w2n b+k+32 <= w2n w` by
    (fs[regions_disjoint_def] >> decide_tac) >>
  irule wordLoadStorePtrTheory.mstore_local_robust >>
  goal_assum (drule_at (Pat `mem_agree_outside _ _ _`)) >>
  goal_assum (drule_at (Pat `local_ptrs_rel _ _ _ _`)) >>
  goal_assum (drule_at (Pat `lookup_scopes _ _ = _`)) >> simp[] >> metis_tac[]
QED

Finalise aug_memory_local_resources

Theorem aug_memory_linked_ghost[local]:
  ghost_inv_at_mods D lo d cenv cx es G tn s /\
  mem_bytes_at 0 lo (mstore a w s).vs_memory = mem_bytes_at 0 lo s.vs_memory /\
  u = (mstore a w s with vs_inst_idx := pc) /\
  un = (tn with t_mem := tn.t_mem DIFF {i | a <= i /\ i < a+32}) /\
  (!name entry p sz.
    lookup_scopes name ee.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    ptr_covers G tn p s sz /\
    !v mem. lookup_var p s = SOME v /\
      mem_agree_outside un.t_mem u.vs_memory mem ==>
      val_in_memory entry.type entry.value (w2n v) mem) ==>
  ghost_inv_at_mods D lo d cenv cx ee G un u
Proof
  strip_tac >> gvs[] >>
  qpat_x_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[ghost_inv_at_mods_def] >> strip_tac >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      first_assum (drule_all_then strip_assume_tac) >>
      gvs[ptr_covers_def, op_taint_def, lookup_var_def, mstore_def]) >>
  conj_tac
  >- (Cases_on `d` >- simp[return_buf_ptr_def] >>
      PairCases_on `x` >>
      gvs[return_buf_ptr_def, ptr_covers_def, op_taint_def,
          lookup_var_def, mstore_def] >> metis_tac[]) >>
  qpat_x_assum `!i. i < lo /\ i IN _ ==> _` (fn th =>
    `!i. i < lo /\ i IN tn.t_mem ==> imm_section_dead_mods cenv
       (mem_bytes_at 0 lo (mstore a w s).vs_memory) i` by simp[th]) >>
  fs[op_taint_def, stor_taint_ok_at_def, allocas_from_def, mstore_def] >>
  metis_tac[]
QED

Theorem aug_memory_source_rebuild[local]:
  stmt_state_rel H ctx func cenv cx es s /\
  local_region cenv es.scopes s id (w2n b) sz /\
  lookup_scopes id es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\ lookup_var p s = SOME b /\
  mem_path_offset entry.type path = SOME (k,ptv) /\ k+32 <= type_memory_size entry.type /\
  type_memory_size entry.type <= sz /\
  value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
  evaluate_subscripts entry.type entry.value path = INL old /\
  store_lays_out etv ptv v /\ value_has_type ptv v /\
  write_place cx (MemoryPlace id path) v es = (INL (),ee) ==>
  stmt_state_rel H ctx func cenv cx (ee with gas_obs := [])
    (mstore (w2n b+k) (typed_val_to_w256 etv v) s with vs_inst_idx := pc)
Proof
  strip_tac >> simp[stmt_state_rel_inst_idx] >>
  drule_then strip_assume_tac lookup_scopes_find_containing_scope >>
  qpat_x_assum `write_place _ _ _ _ = _` mp_tac >>
  simp[write_place_def, get_scopes_def, bind_def, ignore_bind_def, lift_option_type_def,
       type_check_def, assert_def, lift_sum_def, set_scopes_def, return_def, raise_def,
       replace_memory_entry_def] >>
  Cases_on `entry.assignable` >> simp[] >>
  Cases_on `assign_subscripts entry.type entry.value path (Replace v)` >>
  simp[return_def, raise_def, replace_memory_entry_def] >> strip_tac >> gvs[] >>
  rename1 `assign_subscripts entry.type entry.value path (Replace v) = INL new` >>
  suspend "rebuild"
QED

Resume aug_memory_source_rebuild[rebuild]:
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  `val_wf entry.type entry.value /\ val_in_memory entry.type entry.value (w2n b) s.vs_memory` by
    (qpat_assum `local_ptrs_rel _ _ _ _` (strip_assume_tac o REWRITE_RULE [local_ptrs_rel_def]) >>
     first_x_assum (drule_all_then strip_assume_tac) >> gvs[] >>
     metis_tac[memory_value_rel_val_in_memory]) >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  qabbrev_tac `t = mstore (w2n b+k) (typed_val_to_w256 etv v) s` >>
  `val_wf entry.type new /\ val_in_memory entry.type new (w2n b) t.vs_memory` by
    (qunabbrev_tac `t` >> irule aug_place_path_mstore >> simp[] >> metis_tac[]) >>
  `subscripts_type entry.type path = SOME ptv` by metis_tac[mem_path_offset_sound] >>
  `value_has_type entry.type new` by
    (irule vyperPlaceStatePreservationTheory.assign_subscripts_replace_type_metadata >>
     simp[] >> metis_tac[]) >>
  `memory_value_rel entry.type new (w2n b) t.vs_memory` by
    (irule val_in_memory_memory_value_rel >> simp[]) >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es t` by
    (qunabbrev_tac `t` >> irule local_mstore_immutables_at >>
     conj_tac >- (qexistsl_tac [`id`,`sz`] >> simp[] >> decide_tac) >>
     metis_tac[]) >>
  `stmt_state_rel H ctx func cenv cx
     (es with scopes := pre ++ (env |+ (id,entry with <|value := new; popped := []|>)) :: rest) t`
    suffices_by simp[stmt_state_rel_start_gas_obs] >>
  irule stmt_state_rel_write_local >>
  goal_assum (drule_at (Pat `find_containing_scope _ _ = _`)) >>
  simp[] >> qexistsl_tac [`s`,`b`] >> simp[] >>
  `LENGTH s.vs_memory <= LENGTH t.vs_memory` by simp[Abbr `t`, mstore_memory_nondecreasing] >>
  simp[] >>
  conj_tac >- simp[Abbr `t`, mstore_def, lookup_var_def] >>
  conj_tac >- (rpt strip_tac >> simp[Abbr `t`] >>
               irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  simp[Abbr `t`, mstore_def, venom_state_component_equality]
QED

Finalise aug_memory_source_rebuild

Theorem aug_memory_ptr_check[local]:
  target_ptr_ok cenv (PlaceR (MemoryPlace id path)) (dst,loc,pty) G tn s /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME b /\ w2n a = w2n b + k /\ k + 32 <= sz /\
  ptr_covers G tn p s sz /\ allocas_from lo s /\
  eval_operand dst s = SOME a /\ eval_operand op s = SOME w /\
  op_taint tn op = {} /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ptr_inst_ok D lo 0 ctx func G tn (mk_inst iid MSTORE [dst;op] []) s
Proof
  strip_tac >>
  `op_taint tn dst = {}` by fs[target_ptr_ok_def] >>
  `?q. dst = Var q /\ ptr_covers G tn q s 32` by
    (fs[target_ptr_ok_def, ptr_covers_def] >>
     `?q. dst = Var q` by
       (Cases_on `dst` >> gvs[op_prov_def] >> metis_tac[]) >>
     gvs[ptr_covers_def, op_prov_def, eval_operand_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_ADD]) >>
  irule augassign_mstore_ptr_check >> simp[] >> metis_tac[]
QED

Theorem aug_memory_history[local]:
  alloca_history func s /\ fn_has_code sa sb func /\
  emit_void MSTORE [dst;op] sa = ((),sb) /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  alloca_history func (mstore a w s with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  strip_tac >> gvs[emit_void_eq] >>
  qpat_assum `s.vs_inst_idx = _` (fn th => once_rewrite_tac[GSYM th]) >>
  irule (SRULE [] (Q.INST
    [`insts` |-> `[mk_inst sa.cs_next_id MSTORE [dst;op] []]`]
    (SPEC_ALL alloca_history_no_alloca_slice))) >>
  simp[mstore_def] >> qpat_x_assum `fn_has_code _ _ _` mp_tac >>
  simp[fn_has_code_def, IS_PREFIX_APPEND] >>
  strip_tac >> goal_assum (drule_at Any) >>
  simp[DROP_APPEND, mk_inst_def] >> metis_tac[]
QED

Theorem aug_memory_store_resources[local]:
  expr_sim_inv_mods mods cenv cx env es /\
  stmt_state_rel H ctx func cenv cx es s /\
  ghost_inv_at_mods D lo d cenv cx es G tn s /\
  lookup_scopes id es.scopes = SOME entry /\
  place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) a
    (SOME LocMemory) (Type ty) /\
  target_ptr_ok cenv (PlaceR (MemoryPlace id path)) (dst,loc,pty) G tn s /\
  evaluate_type (get_tenv cx) ty = SOME ptv /\ store_lays_out etv ptv v /\
  eval_operand dst s = SOME a /\ eval_operand op s = SOME w /\
  op_taint tn op = {} /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  w2n a+32 <= s.vs_alloca_next /\
  ptr_inst_ok D lo 0 ctx func G tn (mk_inst iid MSTORE [dst;op] []) s /\
  ?p sz b k.
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME b /\ mem_path_offset entry.type path = SOME (k,ptv) /\
    local_region cenv es.scopes s id (w2n b) sz /\
    w2n a = w2n b+k /\ k+32 <= type_memory_size entry.type /\
    type_memory_size entry.type <= sz /\
    value_has_type entry.type entry.value /\ well_formed_type_value entry.type
Proof
  strip_tac >> drule_all aug_memory_layout >> strip_tac >>
  `type_memory_size ptv = 32` by fs[store_lays_out_def] >>
  conj_tac >- decide_tac >>
  conj_tac
  >- (`ptr_covers G tn p s sz /\ allocas_from lo s` by
        (qpat_x_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _` mp_tac >>
         rewrite_tac[ghost_inv_at_mods_def] >> metis_tac[]) >>
      `k+32 <= sz` by decide_tac >>
      drule_all aug_memory_ptr_check >> simp[]) >>
  qexistsl_tac [`p`,`sz`,`b`,`k`] >>
  simp[local_region_def]
QED

Theorem augassign_memory_writeback_mods:
  contract_inv mods exps ctx cenv cx /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  expr_sim_inv_mods mods cenv cx env es /\
  lookup_scopes id es.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value path = INL old /\
  place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) a
    (SOME LocMemory) (Type ty) /\
  target_ptr_ok cenv (PlaceR (MemoryPlace id path)) (dst,loc,pty) G tn s /\
  store_lays_out etv ptv v /\ evaluate_type (get_tenv cx) ty = SOME ptv /\
  value_has_type ptv v /\
  write_place cx (MemoryPlace id path) v es = (res,es') /\ stmt_res_ok lctx res /\
  emit_void MSTORE [dst;op] sa = ((),sb) /\ fn_has_code sa sb func /\
  eval_operand dst s = SOME a /\
  eval_operand op s = SOME (typed_val_to_w256 etv v) /\ op_taint tn op = {} /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  u = (mstore (w2n a) (typed_val_to_w256 etv v) s
        with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  un = (tn with t_mem := tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a+32}) /\
  (!H. valid_horizon cx st0 H es'.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\
    immutable_frame_mods func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx es G tn s /\
    return_buf_frame d cenv sa s /\ return_buf_sep d cenv es s /\
    alloca_history func s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    s0.vs_alloca_next <= s.vs_alloca_next /\
    (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
      lookup_var x s = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
      FLOOKUP s.vs_allocas aid = SOME b) /\
    ghost_kept_at lo cenv es0 sa0 G0 tn0 s0 G tn /\
    alloca_frame c0 es0 sa0 s0 cenv es s) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    (write_place cx (MemoryPlace id path) v) (es,s,G,tn)
    (\H r ee G' tn' t.
      r = INL () /\ t = u /\ G' = G /\ tn' = un /\
      stmt_lands lctx sb r t /\ ~t.vs_halted /\ ~block_is_terminated sb /\
      cenv_top_ext cenv cenv ee.scopes /\
      stmt_state_rel H ctx func cenv cx ee t /\
      immutable_frame_mods func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv sb t /\ return_buf_sep d cenv ee t /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee G' tn' t /\
      (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
        lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
        FLOOKUP t.vs_allocas aid = SOME b) /\
      ghost_kept_at lo cenv es0 sa0 G0 tn0 s0 G' tn' /\
      alloca_frame c0 es0 sa0 s0 cenv ee t) R
Proof
  strip_tac >>
  `res = INL ()` by (drule_all aug_place_memory_write_success >> simp[]) >>
  `MAP FDOM es'.scopes = MAP FDOM es.scopes` by metis_tac[write_place_scopes_dom] >>
  `es'.immutables = es.immutables /\ es'.accounts = es.accounts /\
   es'.tStorage = es.tStorage` by (drule write_memory_place_frame >> strip_tac >> simp[]) >>
  irule gas_outcome_full_mods_pure >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`G`, `es'`, `res`, `u`, `un`] >> simp[NoAsms] >>
  conj_tac >- metis_tac[aug_place_memory_write_gas_obs] >>
  `!J. valid_horizon cx st0 J es'.storage_trace ==>
     ptr_inst_ok (DF J) lo 0 ctx func G tn (mk_inst sa.cs_next_id MSTORE [dst;op] []) s` by
    suspend "safety" >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  suspend "endpoint"
QED

Resume augassign_memory_writeback_mods[safety]:
  rpt strip_tac >>
  qpat_assum `!H. _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  drule_all (cj 2 aug_memory_store_resources) >> simp[]
QED

Resume augassign_memory_writeback_mods[endpoint]:
  drule_all aug_memory_store_resources >>
  disch_then (qspec_then `sa.cs_next_id` strip_assume_tac) >>
  `step_prov PG G (mk_inst sa.cs_next_id MSTORE [dst;op] [])
     (mstore (w2n a) (typed_val_to_w256 etv v) s) = G /\
   step_taint (mk_inst sa.cs_next_id MSTORE [dst;op] []) s
     (mstore (w2n a) (typed_val_to_w256 etv v) s) tn = un` by
    (qpat_assum `un = _` (fn th => pure_once_rewrite_tac[th]) >>
     irule augassign_mstore_clean_transition >> simp[]) >>
  conj_tac
  >- (irule (cj 1 augassign_mstore_endpoint_path) >> simp[] >>
      goal_assum (drule_at (Pat `emit_void _ _ _ = _`)) >> simp[] >>
      qexistsl_tac [`cx`, `es'`, `st0`] >> simp[]) >>
  suspend "post"
QED

Resume augassign_memory_writeback_mods[post]:
  `write_place cx (MemoryPlace id path) v es = (INL (),es')` by metis_tac[] >>
  `k+32 <= sz` by decide_tac >>
  `stmt_state_rel H ctx func cenv cx es' u` by
    (`stmt_state_rel H ctx func cenv cx (es' with gas_obs := []) u` suffices_by
       simp[stmt_state_rel_start_gas_obs] >>
     drule_all aug_memory_source_rebuild >> simp[]) >>
  `immutable_frame_mods func cenv cx (es' with gas_obs := []) u` by
    (qpat_assum `u = _` (fn th => pure_once_rewrite_tac[th]) >>
     irule aug_memory_immutable_frame >>
     goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
     simp[] >> decide_tac) >>
  `storage_well_formed_on cx (es' with gas_obs := []) (FST H)` by
    fs[storage_well_formed_on_def, boolTheory.FORALL_BOOL, get_storage_def] >>
  suspend "ghost"
QED

Resume augassign_memory_writeback_mods[ghost]:
  `dead_lo_ok_mods H (DF H) lo cenv cx` by simp[] >>
  `0 < sz /\ w2n b <= w2n a` by decide_tac >>
  `mem_bytes_at 0 lo (mstore (w2n a) (typed_val_to_w256 etv v) s).vs_memory =
   mem_bytes_at 0 lo s.vs_memory` by
    (drule_all aug_memory_prefix >> simp[]) >>
  `local_ptrs_rel func cenv es.scopes s` by metis_tac[stmt_state_rel_local_ptrs_alloca] >>
  `ghost_inv_at_mods (DF H) lo d cenv cx (es' with gas_obs := []) G un u` by
    (irule aug_memory_linked_ghost >>
     goal_assum (drule_at (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `u = _`)) >>
     simp[] >> rpt gen_tac >> strip_tac >>
     drule_all aug_memory_local_resources >> simp[]) >>
  suspend "frames"
QED

Resume augassign_memory_writeback_mods[frames]:
  `~block_is_terminated sb` by (drule emit_void_terminated >> simp[is_terminator_def]) >>
  `sa.cs_next_var = sb.cs_next_var /\ sa.cs_current_bb = sb.cs_current_bb` by
    (qpat_assum `emit_void _ _ _ = _` mp_tac >> simp[NoAsms, emit_void_eq] >>
     disch_then (SUBST1_TAC o SYM) >> simp[]) >>
  `return_buf_frame d cenv sb u` by
    (irule return_buf_frame_frame >>
     goal_assum (drule_at (Pat `return_buf_frame _ _ _ _`)) >>
     simp[lookup_var_def, mstore_def]) >>
  `alloca_history func u` by
    (qpat_assum `u = _` (fn th => pure_once_rewrite_tac[th]) >>
     drule_all aug_memory_history >> simp[]) >>
  `!n base cap. local_region cenv es'.scopes u n base cap =
                 local_region cenv es.scopes s n base cap` by
    (qpat_assum `u = _` (fn th => pure_once_rewrite_tac[th]) >>
     drule aug_memory_regions >> simp[]) >>
  `!base. allocas_from base u = allocas_from base s` by
    simp[allocas_from_def, mstore_def] >>
  `return_buf_sep d cenv (es' with gas_obs := []) u` by
    (qpat_x_assum `return_buf_sep _ _ _ _` mp_tac >>
     Cases_on `d` >- simp[return_buf_sep_def] >> PairCases_on `x` >>
     simp[return_buf_sep_def, IgnAsm `u = _`] >> metis_tac[]) >>
  `alloca_frame c0 es0 sa0 s0 cenv es' u` by
    (irule alloca_frame_region_write >>
     goal_assum (drule_at (Pat `alloca_frame _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
     simp[] >> conj_tac >- simp[mstore_def, lookup_var_def] >>
     rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  `ghost_kept_at lo cenv es0 sa0 G0 tn0 s0 G un` by
    (qpat_x_assum `ghost_kept_at _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[ghost_kept_at_def, op_taint_def] >> POP_ASSUM_LIST (K all_tac) >>
     strip_tac >> conj_tac
     >- (rpt gen_tac >> strip_tac >>
         qpat_assum `!aid off cap i. FLOOKUP _ aid = SOME (off,cap) /\ _ ==> _`
           (drule_all_then ACCEPT_TAC)) >>
     rpt gen_tac >> strip_tac >>
     qpat_assum `!n b cap i. local_region _ _ _ n b cap /\ _ ==> _`
       (drule_all_then ACCEPT_TAC)) >>
  `allocas_below_fmp u = allocas_below_fmp s` by
    simp[allocas_below_fmp_def, mstore_def] >>
  `!x. lookup_var x u = lookup_var x s` by simp[lookup_var_def, mstore_def] >>
  simp[stmt_lands_def, cenv_top_ext_refl,
       mstore_def, Excl "lookup_var_def"]
QED

Finalise augassign_memory_writeback_mods
