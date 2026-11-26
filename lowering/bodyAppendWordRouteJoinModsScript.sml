(* The slot word route continues at the actual target and RHS cuts. *)
Theory bodyAppendWordRouteJoinMods
Ancestors
  bodyAppendSlotWordMods bodyAppendStageJoinMods bodyWriteTargetStageMods
  stmtSimAugAssignPlaceStorage stmtSimAugAssignPlace bodySimStmtFacts
  exprBodyPreProps exprWordOperand exprSimPrecompiles typedMemoryCopy
  exprSimUnwrap exprSimHypsDefs stateRelProj exprLoweringProps freshWrites
  loweringPosts exprSimProps bodyFullPostsMods bodyPtrDefs ptrDiscipline
  vyperStorageTrace vyperStorageFootprint vyperTypeEvalCaseProofs
  vyperTypeInvariants vyperTypeExprSoundness vyperValue vyperState vyperAST
  compileEnv context venomState words finite_map arithmetic
  exprLowering vyperTypeSystem exprSimSource entryDecodeStaticProps
Libs monadsyntax

Theorem append_slot_word_target_shape[local]:
  is_word_type elem /\
  evaluate_type (get_tenv cx) (ArrayT elem (Dynamic cap)) = SOME leaf ==>
  ?tv. leaf = ArrayTV tv (Dynamic cap) /\
       evaluate_type (get_tenv cx) elem = SOME tv /\ cap < dimword (:256)
Proof
  simp[Once evaluate_type_def, AllCaseEqs(), LET_THM, bound_length_def] >>
  strip_tac >> qexists_tac `tv` >> simp[] >>
  `type_slot_size tv = 1` by drule_all_then ACCEPT_TAC word_type_slot_size >>
  gvs[type_slot_size_def] >> decide_tac
QED

Theorem append_slot_word_target_not_label[local]:
  compile_get_target_ptr cfn cenv bt sa = (r,sp) /\
  FST (SND r) = SOME (slot_loc tr) ==> !l. FST r <> Label l
Proof
  Cases_on `bt`
  >~ [`NameTarget id`]
  >- (simp[compile_get_target_ptr_def] >>
      rename1 `FLOOKUP cenv.ce_vars id` >>
      Cases_on `FLOOKUP cenv.ce_vars id` >> simp[comp_return_def, slot_loc_def] >>
      rename1 `FLOOKUP cenv.ce_vars id = SOME entry` >>
      Cases_on `entry` >> Cases_on `tr` >> simp[comp_return_def, slot_loc_def] >>
      rpt strip_tac >> gvs[])
  >~ [`TopLevelNameTarget key`]
  >- (simp[compile_get_target_ptr_def] >>
      Cases_on `FLOOKUP cenv.ce_module_vars key` >> simp[comp_return_def] >>
      rename1 `FLOOKUP cenv.ce_module_vars key = SOME entry` >>
      Cases_on `entry` >> simp[comp_return_def] >> rpt strip_tac >> gvs[]) >>
  strip_tac >> drule aug_place_target_ptr_not_label >> simp[]
QED

Theorem append_slot_word_saved_address[local]:
  ghost_kept_at lo cenv mid sp Gm tm t G tn ==>
  !bop u slot.
    (!l. bop <> Label l) /\
    (!x. bop = Var x ==> not_fresh_at sp x) /\
    (!x w. not_fresh_at sp x /\ lookup_var x t = SOME w ==> lookup_var x u = SOME w) /\
    eval_operand bop t = SOME slot /\ op_taint tm bop = {} ==>
    eval_operand bop u = SOME slot /\ op_taint tn bop = {}
Proof
  simp[ghost_kept_at_def] >> strip_tac >> Cases >>
  simp[eval_operand_def, op_taint_def] >> rpt strip_tac >>
  first_x_assum (drule_then strip_assume_tac) >> simp[]
QED

Theorem append_slot_word_rhs[local]:
  expr_body_pre_mods mods cenv cx env e mid /\
  bind (eval_expr cx e) (read_result cx) mid = (INL v,ee) /\
  type_widens_to env.type_defs (expr_type e) elem /\ is_word_type elem /\
  evaluate_type (get_tenv cx) elem = SOME tv /\
  lower_value compile_expr cenv elem e sp = (op,sm) /\
  expr_post_mods H ctx func cenv cx e mid sp sm t ee v op u /\
  ptr_val_ok cx (post_value_type cenv e) v op G tn u ==>
  type_memory_bytes cenv elem = 32 /\ value_has_type tv v /\
  eval_operand op u = SOME (typed_val_to_w256 tv v) /\
  op_taint tn op = {} /\ (!x. op = Var x ==> not_fresh_at sm x)
Proof
  strip_tac >>
  drule_all_then assume_tac compileEnvTheory.type_widens_to_word >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  `value_has_type tv v` by
    (drule_all_then strip_assume_tac (REWRITE_RULE [ETA_THM] expr_body_pre_eval_mods) >>
     gvs[value_runtime_typed_def]) >>
  `!id ty. FLOOKUP env.var_types id = SOME ty ==> well_formed_type (get_tenv cx) ty` by
    (simp[well_formed_type_def] >> rpt strip_tac >>
     drule_all env_consistent_var_type_evaluates >> simp[]) >>
  `!x. op = Var x ==> not_fresh_at sm x` by
    (drule lower_value_word_shape >> disch_then (qspec_then `env` mp_tac) >>
     simp[] >> (impl_tac >- first_assum ACCEPT_TAC) >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `type_memory_bytes cenv elem = type_memory_size tv` by
    (irule typed_copy_memory_size >> qexists_tac `get_tenv cx` >>
     fs[expr_sim_inv_mods_def] >> rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `type_memory_size tv = 32` by metis_tac[word_type_memory_size] >>
  fs[ptr_val_ok_def, expr_post_mods_def] >>
  drule expr_post_typed_stack_operand >> simp[]
QED

Theorem append_slot_word_exit[local]:
  append_exit_mods ctx cx RetQ = (\H res ee gt r.
    (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
    halt_exit H cx ee res r /\
    (ctx_has_dalloca ctx ==>
     !z. (r = Halt z \/ ?ir. r = IntRet ir z) ==> allocas_below_fmp z))
Proof
  simp[FUN_EQ_THM, append_exit_mods_def]
QED

Theorem append_slot_word_route_join_mods:
  is_word_type elem /\ type_widens_to env.type_defs (expr_type e) elem /\
  write_target_entry_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx bt es st0 sa sp shadow_sa shadow_sp dst s0 G0 tn0 /\
  lower_value compile_expr cenv elem e sp = (op,sm) /\
  append_store_code_mods cenv e dst (slot_loc tr) elem cap op sm sb func /\
  eval_target_place cx bt (es with gas_obs := ts) =
    (INL (StoragePlace tr slot leaf),mid) /\
  bind (eval_expr cx e) (read_result cx) mid = (INL v,ee) /\
  expr_body_pre_mods mods cenv cx env e mid /\
  storage_trace_domain cx st0 ee.storage_trace /\ ~u.vs_halted /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    write_target_post_mods H (DF H) lo d ctx func cenv cx bt es sa sp s0 mid
      (PlaceR (StoragePlace tr slot leaf)) (Type (ArrayT elem (Dynamic cap)))
      dst G0 tn0 Gm tm t) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    append_rhs_post_mods DF lo d ctx func cenv cx e mid sp sm t op Gm tm H v ee G tn u) /\
  sa.cs_next_var <= sm.cs_next_var /\ s0.vs_alloca_next <= u.vs_alloca_next /\
  return_buf_frame d cenv sm u /\ return_buf_sep d cenv ee u /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
  alloca_frame cenv es sa s0 cenv ee u /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  cenv_top_ext cenv0 cenv ee.scopes ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cenv.ce_modules
    cx st0 (append_place cx (StoragePlace tr slot leaf) v) (ee,u,G,tn)
    (\H res fin Gf tf z. ?cenv'.
      stmt_lands lctx sb res z /\ ~z.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ cenv' = cenv) /\
      cenv_top_ext cenv0 cenv' fin.scopes /\
      stmt_state_rel H ctx func cenv' cx fin z /\ immutable_frame_mods func cenv' cx fin z /\
      storage_well_formed_on cx fin (FST H) /\ return_buf_frame d cenv' sb z /\
      alloca_history func z /\ return_buf_sep d cenv' fin z /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\ s0.vs_alloca_next <= z.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv' cx fin Gf tf z /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x z = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP z.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==>
        FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tf (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame cenv es sa s0 cenv' fin z /\
      (!aid off sz i.
        FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
        (!n b sz'. local_region cenv es.scopes s0 n b sz' ==> off + sz <= b \/ b + sz' <= off) /\
        off <= i /\ i < off + sz /\ i IN tf.t_mem ==> i IN tn0.t_mem))
    (append_exit_mods ctx cx RetQ)
Proof
  strip_tac >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       valid_horizon cx st0 H mid.storage_trace` by
    (rpt strip_tac >>
     `storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
       simp[storage_trace_frame_bind,evaluate_storage_trace_frame,storage_trace_frame_read_result] >>
     drule_all_then ACCEPT_TAC valid_horizon_frame) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) mid.storage_trace` by simp[] >>
  qhdtm_assum `write_target_entry_mods`
    (strip_assume_tac o REWRITE_RULE [write_target_entry_mods_def]) >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
    (drule_then assume_tac) >>
  drule_then strip_assume_tac write_target_storage_view_mods >>
  drule_all_then (qx_choose_then `tv` strip_assume_tac) append_slot_word_target_shape >>
  qpat_x_assum `leaf = _` SUBST_ALL_TAC >>
  drule_then strip_assume_tac write_target_post_view_mods >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> append_rhs_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (drule_then (strip_assume_tac o REWRITE_RULE [append_rhs_post_mods_def])) >>
  drule_all_then strip_assume_tac append_slot_word_rhs >>
  suspend "operand"
QED

Resume append_slot_word_route_join_mods[operand]:
  `!l. FST dst <> Label l` by drule_all_then ACCEPT_TAC append_slot_word_target_not_label >>
  `FST (SND dst) = SOME (slot_loc tr)` by first_assum ACCEPT_TAC >>
  `eval_operand (FST dst) u = SOME slot /\ op_taint tn (FST dst) = {}` by
    (qpat_assum `ghost_kept_at lo cenv mid sp Gm tm t G tn`
       (mp_tac o MATCH_MP append_slot_word_saved_address) >>
     disch_then (qspecl_then [`FST dst`,`u`,`slot`] mp_tac) >>
     fs[expr_post_mods_def, expr_post_def]) >>
  `sp.cs_next_var <= sm.cs_next_var` by
    metis_tac[ci_mono_lower_value_compile_expr, ci_mono_def, pairTheory.SND] >>
  `!x. FST dst = Var x \/ op = Var x ==> not_fresh_at sm x` by
    (rpt strip_tac >> simp[] >>
     irule not_fresh_at_mono >> qexists_tac `sp` >> simp[]) >>
  suspend "store"
QED

Resume append_slot_word_route_join_mods[store]:
  `compile_dynarray_append cenv (FST dst) op 1 1 elem (lowered_value_type cenv e)
      cap T (if tr then LocTransient else LocStorage) sm = ((),sb) /\ fn_has_code sm sb func` by
    (qhdtm_x_assum `append_store_code_mods` mp_tac >>
     Cases_on `tr` >> simp[append_store_code_mods_def, slot_loc_def,
       word_scale_def, elem_size_in_location_def, is_slot_addressed_def]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee u /\
    storage_well_formed_on cx ee (FST H) /\ immutable_frame_mods func cenv cx ee u /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee G tn u /\
    storage_place_observed H (StoragePlace tr slot (ArrayTV tv (Dynamic cap)))` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> append_rhs_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (drule_then (strip_assume_tac o REWRITE_RULE [append_rhs_post_mods_def,expr_post_mods_def,expr_post_def])) >>
     simp[] >>
     qpat_assum `eval_target_place cx bt _ = (INL _,mid)`
       (mp_then (Pos hd) mp_tac aug_place_target_observed) >>
     disch_then (qspec_then `st0` mp_tac) >> simp[]) >>
  `alloca_inv u` by
    (qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     drule_then (ACCEPT_TAC o cj 2) stmt_state_rel_local_ptrs_alloca) >>
  rewrite_tac[append_slot_word_exit] >>
  irule append_slot_word_landing_mods >>
  qpat_assum `compile_dynarray_append _ _ _ 1 1 _ _ _ _ _ _ = _` (irule_at Any) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise append_slot_word_route_join_mods
