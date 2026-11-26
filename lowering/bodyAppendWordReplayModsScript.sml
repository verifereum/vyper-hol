(* The target replay leaves the observations consumed by the RHS replay. *)
Theory bodyAppendWordReplayMods
Ancestors
  bodyAppendWordRouteJoinMods bodyWriteSubscriptSourceMods exprSimExtract32Post
  bodyFullPostsMods bodyInvSplit exprLoweringProps loweringStateRelDefs
  bodyFullShadowBodyInv vyperStorageFootprint bodyWriteTargetStageMods
  exprSimWordArgs targetSubscriptSplit bodyAppendStageJoinMods bodyPtrDefs
  vyperState
Libs monadsyntax

Theorem word_replay_target_frames_mods[local]:
  (immutable_frame_mods func cenv cx (es with gas_obs := gs) s <=>
   immutable_frame_mods func cenv cx es s) /\
  (ghost_inv_at_mods D lo d cenv cx (es with gas_obs := gs) G tn s <=>
   ghost_inv_at_mods D lo d cenv cx es G tn s) /\
  (storage_well_formed_on cx (es with gas_obs := gs) A <=>
   storage_well_formed_on cx es A)
Proof
  rpt conj_tac
  >- (simp[immutable_frame_mods_def,immutables_rel_mods_def,
       immutable_alloca_sep_mods_def,immutable_alloca_sep_def,immutables_rel_def] >> metis_tac[])
  >- simp[ghost_inv_at_mods_def] >>
  irule storage_well_formed_on_backends >> simp[]
QED

Theorem word_replay_target_post_mods[local]:
  write_target_post_mods H D lo d ctx func cenv cx bt es sa sp s0
    (mid with gas_obs := gs) (PlaceR (StoragePlace tr slot leaf))
    vt dst G0 tn0 Gm tm t <=>
  write_target_post_mods H D lo d ctx func cenv cx bt es sa sp s0
    mid (PlaceR (StoragePlace tr slot leaf)) vt dst G0 tn0 Gm tm t
Proof
  simp[write_target_post_mods_def, write_target_location_mods_def,
       stmt_state_rel_start_gas_obs, wb_frame_gas_obs,
       word_replay_target_frames_mods, target_subscript_readable_gas_obs]
QED

Theorem word_replay_rhs_post_mods[local]:
  append_rhs_post_mods DF lo d ctx func cenv cx e (mid with gas_obs := gs)
    sp sm t op Gm tm H v ee G tn u <=>
  append_rhs_post_mods DF lo d ctx func cenv cx e mid
    sp sm t op Gm tm H v ee G tn u
Proof
  simp[append_rhs_post_mods_def, expr_post_mods_def,
       extract32_expr_post_start_gas_obs, ghost_kept_at_def]
QED

Theorem append_slot_word_replay_join_mods:
  is_word_type elem /\ type_widens_to env.type_defs (expr_type e) elem /\
  write_target_entry_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx bt es st0 sa sp shadow_sa shadow_sp dst s0 G0 tn0 /\
  lower_value compile_expr cenv elem e sp = (op,sm) /\
  append_store_code_mods cenv e dst (slot_loc tr) elem cap op sm sb func /\
  (!tail. eval_target_place cx bt (es with gas_obs := ts ++ tail) =
    (INL (StoragePlace tr slot leaf),mid with gas_obs := tail)) /\
  (!tail. bind (eval_expr cx e) (read_result cx) (mid with gas_obs := gs ++ tail) =
    (INL v,ee with gas_obs := tail)) /\
  mid.gas_obs = [] /\ ee.gas_obs = [] /\
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
  qpat_assum `!tail. eval_target_place _ _ _ = _` (qspec_then `gs` assume_tac) >>
  qpat_assum `!tail. bind (eval_expr _ _) _ _ = _` (qspec_then `[]` mp_tac) >>
  `ee with gas_obs := [] = ee` by
    (qpat_assum `ee.gas_obs = []`
      (fn th => pure_rewrite_tac [GSYM th, evaluation_state_fupdselfid]) >> REFL_TAC) >>
  qpat_assum `ee with gas_obs := [] = ee`
    (fn th => pure_rewrite_tac [listTheory.APPEND_NIL, th]) >> disch_tac >>
  irule append_slot_word_route_join_mods >>
  qpat_assum `write_target_entry_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `eval_target_place _ _ _ = _` (irule_at Any) >>
  qpat_assum `bind (eval_expr _ _) _ _ = _` (irule_at Any) >>
  simp[word_replay_target_post_mods, word_replay_rhs_post_mods,
       write_subscript_source_gas_obs_mods] >>
  qpat_assum `append_store_code_mods _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `expr_body_pre_mods _ _ _ _ _ _` (irule_at Any) >>
  map_every qexists_tac [`tm`, `t`, `Gm`] >> simp[]
QED
