(* The memory AugAssign suffix lands on the endpoint of the selected MSTORE. *)
Theory bodyAugMemoryRouteJoinMods
Ancestors
  bodyAugMemoryStoreMods gasOutcomeFullPostMods bodyFullPostsMods
  vyperStorageTrace vyperStorageFootprint bodyPtrDefs

Theorem augassign_memory_route_join_mods:
  contract_inv mods exps ctx cenv cx /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  expr_sim_inv_mods mods cenv cx env ee /\
  target_ptr_ok cenv (PlaceR (MemoryPlace id path)) r Gw tnw w /\
  eval_operand result w = SOME (typed_val_to_w256 ptv value) /\
  op_taint tnw result = {} /\
  ~w.vs_halted /\ w.vs_current_bb = s3.cs_current_bb /\
  w.vs_inst_idx = LENGTH s3.cs_current_insts /\
  fn_has_code s3 sf func /\ evaluate_type (get_tenv cx) ty = SOME ptv /\
  value_has_type ptv value /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee w /\
    immutable_frame_mods func cenv cx ee w /\
    storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee Gw tnw w /\
    return_buf_frame d cenv s3 w /\ return_buf_sep d cenv ee w /\
    alloca_history func w /\ (ctx_has_dalloca ctx ==> allocas_below_fmp w) /\
    s0.vs_alloca_next <= w.vs_alloca_next /\
    (!x z. not_fresh_at sa x /\ lookup_var x s0 = SOME z ==> lookup_var x w = SOME z) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP w.vs_allocas aid = SOME b) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 Gw tnw /\
    alloca_frame cenv es sa s0 cenv ee w) /\
  lookup_scopes id ee.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value path = INL previous /\
  place_ptr_rel cenv cx w (PlaceR (MemoryPlace id path)) addr (SOME LocMemory) (Type ty) /\
  store_lays_out ptv ptv value /\
  write_place cx (MemoryPlace id path) value ee = (res,ff) /\ stmt_res_ok lctx res /\
  emit_void MSTORE [FST r;result] s3 = ((),sf) /\ eval_operand (FST r) w = SOME addr ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    (write_place cx (MemoryPlace id path) value) (ee,w,Gw,tnw)
    (\H res fin G tn t. ?ce.
      stmt_lands lctx sf res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sf /\ ce = cenv) /\
      cenv_top_ext cenv ce fin.scopes /\ stmt_state_rel H ctx func ce cx fin t /\
      immutable_frame_mods func ce cx fin t /\ storage_well_formed_on cx fin (FST H) /\
      return_buf_frame d ce sf t /\ alloca_history func t /\ return_buf_sep d ce fin t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d ce cx fin G tn t /\
      (!x z. not_fresh_at sa x /\ lookup_var x s0 = SOME z ==> lookup_var x t = SOME z) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
        op_taint tn (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame cenv es sa s0 ce fin t /\
      (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
        (!n b len. local_region cenv es.scopes s0 n b len ==> off+sz <= b \/ b+len <= off) /\
        off <= i /\ i < off+sz /\ i IN tn.t_mem ==> i IN tn0.t_mem)) R
Proof
  strip_tac >> PairCases_on `r` >> fs[] >>
  `!H. valid_horizon cx st0 H ff.storage_trace ==> valid_horizon cx st0 H ee.storage_trace` by
    (rpt strip_tac >>
     qpat_assum `write_place _ _ _ _ = _` (mp_then (Pat `f st = _`) mp_tac valid_horizon_frame) >>
     simp[storage_trace_frame_write_place]) >>
  qabbrev_tac `u = mstore (w2n addr) (typed_val_to_w256 ptv value) w with
                   vs_inst_idx := LENGTH sf.cs_current_insts` >>
  qabbrev_tac `un = tnw with t_mem := tnw.t_mem DIFF {i | w2n addr <= i /\ i < w2n addr+32}` >>
  irule gas_outcome_full_mods_post_source >>
  irule_at (Pat `gas_outcome_full_mods _ _ _ _ _ _ _ _`) augassign_memory_writeback_mods >>
  qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
  qpat_assum `expr_sim_inv_mods _ _ _ _ _` (irule_at Any) >>
  qpat_assum `write_place _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `stmt_res_ok _ _` (irule_at Any) >>
  qpat_assum `emit_void _ _ _ = _` (irule_at Any) >>
  qpat_assum `target_ptr_ok _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `place_ptr_rel _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `store_lays_out _ _ _` (irule_at Any) >>
  qpat_assum `lookup_scopes _ _ = _` (irule_at Any) >>
  qpat_assum `evaluate_subscripts _ _ _ = _` (irule_at Any) >>
  simp[] >> qexistsl_tac [`tn0`,`sa`,`s0`,`es`,`d`,`cenv`,`R`,`G0`] >>
  conj_tac
  >- (qx_gen_tac `H` >> strip_tac >>
      qpat_assum `!H. _ ==> valid_horizon _ _ H ee.storage_trace`
        (drule_then assume_tac) >>
      qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
        (drule_then strip_assume_tac) >> simp[]) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `ghost_kept_at _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
  simp[] >> first_assum ACCEPT_TAC
QED
