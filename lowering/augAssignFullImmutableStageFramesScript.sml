(* Reindex the immutable store frame at the actual write trace. *)
Theory augAssignFullImmutableStageFrames
Ancestors
  vyperEvalExprPreservesScopesDom
  augAssignFullEntryFrame bodySimAugPlaceScopes stmtSimAugAssign
  vyperStorageFootprint vyperStorageTrace vyperScopePreservation vyperState
  supportedStmts finite_map pred_set list

Theorem augassign_immutable_staged_store_frame:
  (!H. valid_horizon cx st0 H es0.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es0 s0 /\
    stmt_state_rel H ctx func cenv cx es0 u) /\
  local_ptrs_reserved cenv sa0 /\ local_ptrs_reserved cenv sc /\
  local_ptrs_reserved cenv sd /\
  sa0.cs_next_var <= sc.cs_next_var /\ sc.cs_next_var <= sd.cs_next_var /\
  sd.cs_next_var <= se.cs_next_var /\
  sa0.cs_next_id <= sc.cs_next_id /\ sc.cs_next_id <= sd.cs_next_id /\
  u.vs_memory = s0.vs_memory /\ u.vs_allocas = s0.vs_allocas /\
  u.vs_alloca_next = s0.vs_alloca_next /\
  (!x z. not_fresh_at sa0 x /\ lookup_var x s0 = SOME z ==>
    lookup_var x u = SOME z) /\
  ghost_kept_at lo cenv es0 sa0 G0 tn0 s0 Gu tnu /\
  bind (eval_expr cx e) (read_result cx) es0 = (INL rhs,ee) /\
  supported_expr tops e /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post H ctx func cenv cx e es0 sc sd u ee rhs op q) /\
  ghost_kept_at lo cenv es0 sc Gu tnu u Gq tnq /\
  ghost_kept_at lo cenv ee sd Gq tnq q Gw tnw /\
  (!x z. not_fresh_at sd x /\ lookup_var x q = SOME z ==>
    lookup_var x w = SOME z) /\
  w.vs_memory = q.vs_memory /\ w.vs_allocas = q.vs_allocas /\
  w.vs_alloca_next = q.vs_alloca_next /\
  u.vs_alloca_next <= q.vs_alloca_next /\
  return_buf_frame d cenv sd q /\ alloca_history func w /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp w) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee w /\
    storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx ee Gw tnw w) /\
  write_place cx (ImmutablePlace src id []) v ee = (res,ff) ==>
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
  strip_tac >>
  `MAP FDOM ee.scopes = MAP FDOM es0.scopes` by
    (qpat_assum `vyperState$bind _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST kall_tac >>
     simp[bind_def, AllCaseEqs()] >> rpt strip_tac >>
     imp_res_tac read_result_state >> gvs[] >>
     drule eval_expr_preserves_scopes_dom >> simp[]) >>
  qx_gen_tac `H` >> strip_tac >>
  `valid_horizon cx st0 H ee.storage_trace` by
    (qpat_assum `write_place _ _ _ _ = _` mp_tac >>
     qpat_assum `valid_horizon _ _ _ ff.storage_trace` mp_tac >>
     POP_ASSUM_LIST kall_tac >>
     metis_tac[valid_horizon_frame, storage_trace_frame_write_place]) >>
  `valid_horizon cx st0 H es0.storage_trace` by
    (qpat_assum `vyperState$bind _ _ _ = _` mp_tac >>
     qpat_assum `valid_horizon _ _ _ ee.storage_trace` mp_tac >>
     POP_ASSUM_LIST kall_tac >>
     metis_tac[valid_horizon_frame, augassign_rhs_trace_frame]) >>
  map_every (fn post => qpat_x_assum post (qspec_then `H` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac)
    [`!h. valid_horizon _ _ h es0.storage_trace ==> _`,
     `!h. _ ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`,
     `!h. _ ==> stmt_state_rel _ _ _ _ _ ee w /\ _`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  match_mp_tac (GEN_ALL augassign_immutable_entry_operator_frame) >>
  goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >>
  metis_tac[]
QED
