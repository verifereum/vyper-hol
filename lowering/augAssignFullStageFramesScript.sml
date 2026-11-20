(* Reindex the actual ordinary stages at the store's horizon. *)
Theory augAssignFullStageFrames
Ancestors
  augAssignFullEntryFrame stmtSimAugAssign bodySimAugPlaceLoad
  bodySimAugPlaceScopes bodySimStmtFacts supportedStmts
  vyperStorageTrace vyperStorageFootprint gasOutcomeFull
  bodySimFull loweringPosts freshWrites compileEnv venomState
  vyperState exprSimSource
  bodyMemoryDefs bodyPtrDefs stmtSimDefs finite_map pred_set list arithmetic

(* TEMPORARILY CHEATED - SCRATCH SEQ-8501 census (never lands)
Proof
  strip_tac >>
  `st.scopes = es0.scopes` by metis_tac[aug_place_target_scopes] >>
  `supported_expr tops e` by metis_tac[supported_augassign_contract] >>
  `ee.scopes = st.scopes` by
    (qpat_x_assum `bind _ _ _ = _` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> rpt strip_tac >>
     metis_tac[aug_place_supported_expr_scopes, read_result_state]) >>
  qx_gen_tac `H` >> strip_tac >>
  `valid_horizon cx st0 H ee.storage_trace` by
    (qpat_assum `write_place _ _ _ _ = _` mp_tac >>
     qpat_assum `valid_horizon _ _ _ ff.storage_trace` mp_tac >>
     POP_ASSUM_LIST kall_tac >>
     metis_tac[valid_horizon_frame, storage_trace_frame_write_place]) >>
  `valid_horizon cx st0 H st.storage_trace` by
    (qpat_assum `bind _ _ _ = _` mp_tac >>
     qpat_assum `valid_horizon _ _ _ ee.storage_trace` mp_tac >>
     POP_ASSUM_LIST kall_tac >>
     metis_tac[valid_horizon_frame, augassign_rhs_trace_frame]) >>
  `valid_horizon cx st0 H es0.storage_trace` by
    (qpat_assum `eval_target_place _ _ _ = _` mp_tac >>
     qpat_assum `valid_horizon _ _ _ st.storage_trace` mp_tac >>
     POP_ASSUM_LIST kall_tac >>
     metis_tac[valid_horizon_frame, cj 8 evaluate_storage_trace_frame]) >>
  map_every (fn trace => qpat_x_assum trace (qspec_then `H` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac)
    [`!h. valid_horizon _ _ h es0.storage_trace ==> _`,
     `!h. valid_horizon _ _ h st.storage_trace ==> _`,
     `!h. valid_horizon _ _ h ee.storage_trace ==> _`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  match_mp_tac (GEN_ALL augassign_entry_operator_frame) >>
  goal_assum (drule_at (Pat `target_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >>
  goal_assum (drule_at (Pat `ghost_kept_at _ _ _ sa0 _ _ _ _ _`)) >>
  goal_assum (drule_at Any) >> simp[]
QED
*)
Theorem augassign_staged_store_frame:
  eval_target_place cx bt es0 = (INL p,st) /\
  bind (eval_expr cx e) (read_result cx) st = (INL rhs,ee) /\
  write_place cx p v ee = (res,ff) /\
  supported_stmt tops bindings (AugAssign ty bt bop e) /\
  supported_target_info tops bindings bt = SOME info /\
  expr_body_pre cenv cx env e st /\
  local_ptrs_reserved cenv sa0 /\ local_ptrs_reserved cenv sb /\
  local_ptrs_reserved cenv sc /\ local_ptrs_reserved cenv sd /\
  sa0.cs_next_var <= sb.cs_next_var /\ sb.cs_next_var <= sc.cs_next_var /\
  sc.cs_next_var <= sd.cs_next_var /\ sd.cs_next_var <= se.cs_next_var /\
  sa0.cs_next_id <= sb.cs_next_id /\ sb.cs_next_id <= sc.cs_next_id /\
  sc.cs_next_id <= sd.cs_next_id /\
  (!H. valid_horizon cx st0 H es0.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es0 s0) /\
  (!H. valid_horizon cx st0 H st.storage_trace ==>
    target_post H ctx func cenv cx es0 sa0 sb s0 st pv vt r t /\
    stmt_state_rel H ctx func cenv cx st u /\
    ghost_kept_at lo cenv es0 sa0 G0 tn0 s0 Gu tnu) /\
  u.vs_memory = t.vs_memory /\ u.vs_allocas = t.vs_allocas /\
  u.vs_alloca_next = t.vs_alloca_next /\
  (!x z. not_fresh_at sb x /\ lookup_var x t = SOME z ==>
    lookup_var x u = SOME z) /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post H ctx func cenv cx e st sc sd u ee rhs op q /\
    ghost_kept_at lo cenv st sc Gu tnu u Gq tnq /\
    ghost_kept_at lo cenv ee sd Gq tnq q Gw tnw /\
    stmt_state_rel H ctx func cenv cx ee w /\
    storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx ee Gw tnw w) /\
  (!x z. not_fresh_at sd x /\ lookup_var x q = SOME z ==>
    lookup_var x w = SOME z) /\
  w.vs_memory = q.vs_memory /\ w.vs_allocas = q.vs_allocas /\
  w.vs_alloca_next = q.vs_alloca_next /\
  u.vs_alloca_next <= q.vs_alloca_next /\
  return_buf_frame d cenv sd q /\ alloca_history func w /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp w) ==>
  !H. valid_horizon cx st0 H ff.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee w /\
    storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx ee Gw tnw w /\
    return_buf_frame d cenv se w /\ alloca_history func w /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp w) /\
    s0.vs_alloca_next <= w.vs_alloca_next /\
    (!x z. not_fresh_at sa0 x /\ lookup_var x s0 = SOME z ==>
      lookup_var x w = SOME z) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
      FLOOKUP w.vs_allocas aid = SOME b) /\
    (!x. not_fresh_at sa0 x ==> FLOOKUP Gw x = FLOOKUP G0 x /\
      op_taint tnw (Var x) = op_taint tn0 (Var x)) /\
    alloca_frame cenv es0 sa0 s0 cenv ee w /\
    (!aid off sz i.
      FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa0.cs_next_id /\
      (!n b sz'. local_region cenv es0.scopes s0 n b sz' ==>
        off + sz <= b \/ b + sz' <= off) /\
      off <= i /\ i < off + sz /\ i IN tnw.t_mem ==> i IN tn0.t_mem)
Proof
  cheat
QED
