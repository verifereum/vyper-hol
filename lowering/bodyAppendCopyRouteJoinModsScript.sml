(* The nonword storage/transient Append landing at the two reached cuts. *)
Theory bodyAppendCopyRouteJoinMods
Ancestors
  bodyAppendSlotCopyMods bodyAppendStageJoinMods bodyWriteTargetStageMods
  vyperStorageFootprint vyperEvalPreservesScopes loweringPosts
  vyperState vyperTypeValues finite_map list
Libs monadsyntax

Theorem append_copy_origin[local]:
  MAP FDOM sc = MAP FDOM sc' /\ cenv_top_ext cenv0 cenv sc ==>
  cenv_top_ext cenv0 cenv sc'
Proof
  Cases_on `sc` >> Cases_on `sc'` >> simp[cenv_top_ext_def] >>
  rpt strip_tac >> first_x_assum drule >>
  strip_tac >> simp[] >> irule lookup_scopes_none_map_fdom >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem append_slot_copy_route_join_mods:
  contract_inv mods exps ctx cenv cx /\
  compile_get_target_ptr compile_expr cenv bt sa = (dst,sp) /\
  lower_value compile_expr cenv elem e sp = (op,sm) /\
  append_store_code_mods cenv e dst loc elem cap op sm sf func /\
  FST (SND dst) = SOME loc /\
  ~is_word_type elem /\ stmt_exprs_ok cenv (Append bt e) /\
  target_place_type cenv bt = SOME (ValPT (ArrayT elem (Dynamic cap))) /\
  expr_body_pre_mods mods cenv cx env e reached /\
  type_widens_to env.type_defs (expr_type e) elem /\
  (!tail. eval_target_place cx bt (es with gas_obs := ts ++ tail) =
    (INL (StoragePlace tr slot aty),reached with gas_obs := tail)) /\
  (!tail. bind (eval_expr cx e) (read_result cx) (reached with gas_obs := gs ++ tail) =
    (INL v,mid with gas_obs := tail)) /\
  reached.gas_obs = [] /\ mid.gas_obs = [] /\
  storage_trace_domain cx st0 reached.storage_trace /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H reached.storage_trace ==>
    write_target_post_mods H (DF H) lo d ctx func cenv cx bt es sa sp s0 reached
      (PlaceR (StoragePlace tr slot aty))
      (Type (ArrayT elem (Dynamic cap))) dst G0 tn0 Gp tp p) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    append_rhs_post_mods DF lo d ctx func cenv cx e reached sp sm p op Gp tp H v mid G tn s) /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sp /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sm x) /\
  (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sm x) /\
  return_buf_frame d cenv sm s /\ return_buf_sep d cenv mid s /\ ~s.vs_halted /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x s = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
  alloca_frame cenv es sa s0 cenv mid s /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  (!n b sz. local_region cenv mid.scopes s n b sz <=> local_region cenv es.scopes s0 n b sz) /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\ cenv_top_ext cenv0 cenv es.scopes ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    (append_place cx (StoragePlace tr slot aty) v) (mid,s,G,tn)
    (\H res ee Gf tf u. ?cenv'.
      stmt_lands lctx sf res u /\ ~u.vs_halted /\
      (res = INL () ==> ~block_is_terminated sf /\ cenv' = cenv) /\
      cenv_top_ext cenv0 cenv' ee.scopes /\
      stmt_state_rel H ctx func cenv' cx ee u /\ immutable_frame_mods func cenv' cx ee u /\
      storage_well_formed_on cx ee (FST H) /\ return_buf_frame d cenv' sf u /\
      alloca_history func u /\ return_buf_sep d cenv' ee u /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\ s0.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv' cx ee Gf tf u /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==>
        FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tf (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame cenv es sa s0 cenv' ee u /\
      (!aid off sz i.
        FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
        (!n b sz'. local_region cenv es.scopes s0 n b sz' ==> off + sz <= b \/ b + sz' <= off) /\
        off <= i /\ i < off + sz /\ i IN tf.t_mem ==> i IN tn0.t_mem))
    (append_exit_mods ctx cx RetQ)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon reached.storage_trace) reached.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H reached.storage_trace ==> _`
    (drule_then (strip_assume_tac o MATCH_MP write_target_storage_view_mods)) >>
  qpat_assum `evaluate_type _ (ArrayT _ _) = _`
    (strip_assume_tac o MATCH_MP vyperTypeValuesTheory.evaluate_type_ArrayT_cases) >>
  gvs[] >>
  `cenv_top_ext cenv0 cenv mid.scopes` by drule_all_then ACCEPT_TAC append_copy_origin >>
  qpat_assum `!tail. eval_target_place _ _ _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE bool_ss [APPEND_NIL])) >>
  qpat_assum `!tail. bind _ _ _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE bool_ss [APPEND_NIL])) >>
  `reached with gas_obs := [] = reached /\ mid with gas_obs := [] = mid` by
    simp[evaluation_state_component_equality] >>
  fs[] >>
  irule append_slot_copy_landing_mods >>
  qpat_assum `expr_body_pre_mods _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `eval_target_place _ _ _ = _` (irule_at Any) >>
  qpat_assum `bind _ _ _ = _` (irule_at Any) >>
  qpat_assum `lower_value compile_expr _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `compile_get_target_ptr compile_expr _ _ _ = _` (irule_at Any) >>
  qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
  qexistsl_tac [`tp`,`p`,`Gp`] >> simp[]
QED
