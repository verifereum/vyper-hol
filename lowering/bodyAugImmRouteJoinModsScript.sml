(* The qualified immutable AugAssign suffix uses the selected owner's word store. *)
Theory bodyAugImmRouteJoinMods
Ancestors
  bodyWriteImmWordMods gasOutcomeFullPostMods bodyFullPostsMods
  vyperStorageFootprint bodyPtrDefs

Theorem augassign_immutable_route_join_mods:
  contract_inv mods exps ctx cenv cx /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  sa.cs_next_var <= s3.cs_next_var /\ s3.cs_next_var <= sf.cs_next_var /\
  expr_sim_inv_mods mods cenv cx env ee /\
  eval_operand result w = SOME (typed_val_to_w256 ptv value) /\ op_taint tnw result = {} /\
  (!x. result = Var x ==> not_fresh_at s3 x) /\ local_ptrs_reserved cenv s3 /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at s3 x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at s3 x) /\
  ~w.vs_halted /\ w.vs_current_bb = s3.cs_current_bb /\ w.vs_inst_idx = LENGTH s3.cs_current_insts /\
  fn_has_code s3 sf func /\ evaluate_type (get_tenv cx) ty = SOME ptv /\
  is_word_type ty /\ value_has_type ptv value /\
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
  cenv.ce_is_ctor /\ ALOOKUP cenv.ce_modules owner = SOME target_tops /\
  ALOOKUP ee.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables owner imms) id = SOME (itv,now) /\
  FLOOKUP cenv.ce_module_vars (owner,id) = SOME (ImmutableLoc off) /\
  mem_path_offset itv path = SOME (k,ptv) /\
  write_place cx (ImmutablePlace owner id path) value ee = (INL (),ff) /\
  compile_imm_store_word cenv.ce_imm_alloca (FST r) result s3 = ((),sf) /\
  eval_operand (FST r) w = SOME (n2w (off+k)) /\ op_taint tnw (FST r) = {} /\
  op_prov Gw (FST r) = NONE ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    (write_place cx (ImmutablePlace owner id path) value) (ee,w,Gw,tnw)
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
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `ghost_kept_at _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
  irule gas_outcome_full_mods_post_source >>
  irule_at (Pat `gas_outcome_full_mods _ _ _ _ _ _ _ _`) immutable_word_writeback_mods >>
  qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
  qpat_assum `expr_sim_inv_mods _ _ _ _ _` (irule_at Any) >>
  qpat_assum `write_place _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `compile_imm_store_word _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `ALOOKUP cenv.ce_modules owner = SOME _` (irule_at Any) >>
  qpat_assum `ALOOKUP ee.immutables _ = SOME _` (irule_at Any) >>
  qpat_assum `FLOOKUP (get_source_immutables _ _) _ = SOME _` (irule_at Any) >>
  qpat_assum `FLOOKUP cenv.ce_module_vars _ = SOME _` (irule_at Any) >>
  qpat_assum `evaluate_type (get_tenv cx) ty = SOME _` (irule_at Any) >>
  qpat_assum `mem_path_offset _ _ = SOME _` (irule_at Any) >>
  qpat_assum `alloca_frame _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `return_buf_frame _ _ _ _` (irule_at Any) >>
  qexistsl_tac [`tn0`,`lctx`,`R`,`G0`] >>
  simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >> first_assum ACCEPT_TAC
QED
