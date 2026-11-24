(* Original-site resources after reading the RHS of a fresh declaration. *)
Theory bodyAnnCopyReadFrameMods
Ancestors
  bodyFullPostsMods stmtSimDefs bodyPtrDefs bodyMemoryDefs bodySimFull
  vyperEvalPreservesScopes vyperStorageTrace vyperStorageFootprint
  exprLoweringProps loweringPosts assignTuplePtrCopyLen freshWrites

Theorem ann_copy_read_install_frame_mods:
  lookup_scopes id es.scopes = NONE /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  local_ptrs_reserved ce a /\ not_fresh_at a p /\
  sa.cs_next_id <= a.cs_next_id /\ a.cs_next_var <= b.cs_next_var /\
  (!x. not_fresh_at sa x ==> not_fresh_at a x) /\
  (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at a x) /\
  (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at a x) /\
  return_buf_frame d ce a entry /\
  lookup_var p entry = SOME w /\ ptr_covers Ga tna p entry sz /\
  FLOOKUP entry.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
  w2n w + sz <= entry.vs_alloca_next /\
  s0.vs_alloca_next <= entry.vs_alloca_next /\ entry.vs_alloca_next <= s.vs_alloca_next /\
  (!x. not_fresh_at sa x ==> lookup_var x entry = lookup_var x s0) /\
  (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==>
             FLOOKUP entry.vs_allocas aid = SOME ent) /\
  alloca_frame old es sa s0 ce es entry /\
  ghost_kept_at lo old es sa G0 tn0 s0 Ga tna /\
  (!J. valid_horizon cx st0 J es.storage_trace ==> stmt_state_rel J ctx func ce cx es entry) /\
  (!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks entry.vs_gas_readings ++ tail) =
    (INL v,mid with gas_obs := tail)) /\
  valid_horizon cx st0 H mid.storage_trace /\
  expr_post_mods H ctx func ce cx e es a b entry mid v op s /\
  ghost_kept_at lo ce es a Ga tna entry G tn ==>
  MAP FDOM mid.scopes = MAP FDOM es.scopes /\
  lookup_scopes id mid.scopes = NONE /\ not_local_ptr ce mid.scopes p /\
  lookup_var p s = SOME w /\ ptr_covers G tn p s sz /\
  FLOOKUP s.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
  w2n w + sz <= s.vs_alloca_next /\
  not_fresh_at b p /\ local_ptrs_reserved ce b /\
  (!x. not_fresh_at sa x ==> not_fresh_at b x) /\
  (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x) /\
  (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x) /\
  return_buf_frame d ce b s /\
  stmt_state_rel H ctx func ce cx mid s /\ storage_well_formed_on cx mid (FST H) /\
  immutable_frame_mods func ce cx mid s /\
  (!x z. not_fresh_at sa x /\ lookup_var x s0 = SOME z ==> lookup_var x s = SOME z) /\
  (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==> FLOOKUP s.vs_allocas aid = SOME ent) /\
  (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
                            op_taint tn (Var x) = op_taint tn0 (Var x)) /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  alloca_frame old es sa s0 ce mid s /\
  (!aid off len i.
    FLOOKUP s0.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id /\
    (!name x cap. local_region old es.scopes s0 name x cap ==>
                  off + len <= x \/ x + cap <= off) /\
    off <= i /\ i < off + len /\ i IN tn.t_mem ==> i IN tn0.t_mem)
Proof
  strip_tac >>
  qpat_x_assum `!tail. bind _ _ _ = _` (qspec_then `[]` assume_tac) >>
  `MAP FDOM mid.scopes = MAP FDOM es.scopes` by
    (drule eval_read_preserves_scopes_dom >> simp[]) >>
  `lookup_scopes id mid.scopes = NONE` by
    (irule lookup_scopes_none_map_fdom >> qexists_tac `es.scopes` >> simp[]) >>
  `not_local_ptr ce mid.scopes p` by
    (irule local_ptrs_reserved_not_live >> conj_tac
     >- (qexistsl_tac [`id`,`sz`] >> simp[]) >> qexists_tac `a` >> simp[]) >>
  `valid_horizon cx st0 H es.storage_trace` by
    (drule_at (Pat `f st = _`) valid_horizon_frame >>
     simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
          storage_trace_frame_read_result]) >>
  `stmt_state_rel H ctx func ce cx es entry` by
    (qpat_assum `!J. valid_horizon _ _ J es.storage_trace ==> _` (drule_then ACCEPT_TAC)) >>
  qhdtm_assum `expr_post_mods` (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
  `alloca_frame ce es a entry ce mid s` by
    (drule expr_post_alloca_frame >> simp[]) >>
  qhdtm_x_assum `expr_post` (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  `return_buf_frame d ce b s` by
    (irule return_buf_frame_frame >> qexistsl_tac [`ce`,`entry`,`a`] >> simp[]) >>
  `alloca_frame old es sa s0 ce mid s` by
    (irule alloca_frame_trans >> qexistsl_tac [`ce`,`es`,`entry`,`a`] >> simp[]) >>
  suspend "compose"
QED

Resume ann_copy_read_install_frame_mods[compose]:
  `lookup_var p s = SOME w` by (first_assum irule >> simp[]) >>
  `ptr_covers G tn p s sz` by
    (irule ptr_covers_lookup_frame >> qexistsl_tac [`Ga`,`entry`,`tna`] >>
     fs[ghost_kept_at_def]) >>
  `local_ptrs_reserved ce b` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `a` >> simp[]) >>
  `!x. not_fresh_at a x ==> not_fresh_at b x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `not_fresh_at b p /\ (!x. not_fresh_at sa x ==> not_fresh_at b x) /\
   (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x) /\
   (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x)` by
    (rpt conj_tac >> rpt strip_tac >> first_assum irule >> simp[]) >>
  `w2n w + sz <= s.vs_alloca_next /\ s0.vs_alloca_next <= s.vs_alloca_next` by
    decide_tac >>
  `!x z. not_fresh_at sa x /\ lookup_var x s0 = SOME z ==> lookup_var x s = SOME z` by
    (rpt strip_tac >> first_assum irule >> simp[]) >>
  `!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==> FLOOKUP s.vs_allocas aid = SOME ent` by
    (rpt strip_tac >> first_assum irule >> first_assum irule >> simp[]) >>
  `!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
                            op_taint tn (Var x) = op_taint tn0 (Var x)` by
    (fs[ghost_kept_at_def] >> rpt strip_tac >> metis_tac[]) >>
  `!aid off len i.
    FLOOKUP s0.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id /\
    (!name x cap. local_region old es.scopes s0 name x cap ==>
                  off + len <= x \/ x + cap <= off) /\
    off <= i /\ i < off + len /\ i IN tn.t_mem ==> i IN tn0.t_mem` by
    (qpat_x_assum `ghost_kept_at _ old _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
     qpat_x_assum `ghost_kept_at _ ce _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
     qpat_assum `alloca_frame old es sa s0 ce es entry`
       (mp_then Any mp_tac alloca_taint_kept_trans) >>
     disch_then (qspecl_then [`tn`,`tna`,`tn0`,`a`] mp_tac) >>
     asm_rewrite_tac[]) >>
  asm_rewrite_tac[] >>
  qpat_assum `!aid ent. FLOOKUP entry.vs_allocas aid = SOME ent ==> _` irule >> simp[]
QED

Finalise ann_copy_read_install_frame_mods
