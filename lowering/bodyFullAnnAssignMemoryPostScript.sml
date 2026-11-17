(* Capacity-parametric installation after the joint aggregate store. *)
Theory bodyFullAnnAssignMemoryPost
Ancestors
  stmtSimDeclCopyFrame stmtSimDeclCompose stmtSimDeclSource
  bodyFullMemoryFrames bodySimFull stateRelProj bodyMemoryDefs
  typedCopyOriginPtrBase exprSimStorageCopy bodyBinopFragMemory
  loweringPosts compileEnv vyperState vyperValue venomState finite_map

Theorem annassign_memory_full_ghost_store[local]:
  stmt_state_rel H ctx func ce cx mid u /\ fn_inst_ids_distinct func /\
  ghost_inv_at D lo d ce cx mid G1 tn1 u /\ local_ptrs_reserved ce b /\
  (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x) /\
  (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x) /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_local_ptr ce mid.scopes p /\ lookup_var p u = SOME w /\
  MEM inst (fn_insts func) /\ inst.inst_outputs = [p] /\
  FLOOKUP u.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
  type_memory_size tyv <= sz /\
  typed_copy_state_frame b (w2n w) (type_memory_size tyv) u t /\
  tnf.t_stor = tn1.t_stor /\ tnf.t_trans = tn1.t_trans /\ tnf.t_imm = tn1.t_imm /\
  (!i. ~(w2n w <= i /\ i < w2n w + type_memory_size tyv) ==>
    (i IN tnf.t_mem <=> i IN tn1.t_mem)) /\
  (!q. not_fresh_at b q ==> FLOOKUP Gf q = FLOOKUP G1 q /\
    op_taint tnf (Var q) = op_taint tn1 (Var q)) ==>
  ghost_inv_at D lo d ce cx mid Gf tnf t
Proof
  strip_tac >>
  qpat_assum `typed_copy_state_frame _ _ _ _ _`
    (strip_assume_tac o SRULE [typedMemoryCopyTheory.typed_copy_state_frame_def,
                              venomStateTheory.venom_state_component_equality]) >>
  `lo <= w2n w` by
    (fs[bodyPtrDefsTheory.ghost_inv_at_def, ptrDisciplineTheory.allocas_from_def] >>
     metis_tac[]) >>
  irule bodyFullMemoryFramesTheory.body_full_memory_ghost_frame >>
  conj_tac >- fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  conj_tac >- (fs[bodyPtrDefsTheory.ghost_inv_at_def,
    ptrDisciplineTheory.allocas_from_def] >> metis_tac[]) >>
  qexistsl_tac [`G1`, `u`, `b`, `tn1`,
    `{i | w2n w <= i /\ i < w2n w + type_memory_size tyv}`] >>
  simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `local_ptrs_rel func ce mid.scopes u /\ alloca_inv u` by
        metis_tac[stateRelProjTheory.stmt_state_rel_local_ptrs_alloca] >>
      `local_region ce mid.scopes u name (w2n w') sz'` by
        (simp[loweringStateRelDefsTheory.local_region_def] >> metis_tac[]) >>
      `regions_disjoint (w2n w) sz (w2n w') sz'` by
        (irule localPtrsPropsTheory.local_ptrs_rel_alloca_disjoint >>
         goal_assum (drule_at Any) >> metis_tac[]) >>
      fs[loweringStateRelDefsTheory.local_ptrs_rel_def] >>
      first_x_assum drule_all >> strip_tac >> gvs[] >>
      drule exprSimPropsTheory.val_footprint_le >>
      fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  conj_tac >- (fs[typedMemoryCopyTheory.typed_copy_frame_def] >>
    rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  conj_tac >- (rpt strip_tac >>
    `~(w2n w <= i /\ i < w2n w + type_memory_size tyv)` by decide_tac >>
    metis_tac[]) >>
  fs[typedMemoryCopyTheory.typed_copy_frame_def]
QED

Theorem annassign_memory_full_installation_post:
  !H D lo d ctx func old ce cx es mid out sa b sf s0 s t G0 tn0 G tn Gf tf
   id p sz w inst n tyv v sc rest lctx.
    new_variable id tyv v mid = (INL (),out) /\
    mid.scopes = sc::rest /\ lookup_scopes id mid.scopes = NONE /\
    out = mid with scopes :=
      (sc |+ (id,<|assignable := T; type := tyv; value := v; popped := []|>))::rest /\
    (!name. name <> id ==> FLOOKUP ce.ce_vars name = FLOOKUP old.ce_vars name) /\
    ce with <|ce_vars := old.ce_vars; ce_var_type := old.ce_var_type;
              ce_dynarray_capacity := old.ce_dynarray_capacity|> = old /\
    FLOOKUP old.ce_vars id = NONE /\
    stmt_state_rel H ctx func ce cx mid s /\
    storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at D lo d ce cx mid G tn s /\ fn_inst_ids_distinct func /\
    FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr ce mid.scopes p /\ lookup_var p s = SOME w /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [p] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
    sa.cs_next_id <= inst.inst_id /\ ptr_covers G tn p s sz /\
    local_ptrs_reserved ce b /\ not_fresh_at b p /\
    (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x) /\
    (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x) /\
    (!x. not_fresh_at sa x ==> not_fresh_at b x) /\
    n <= type_memory_size tyv /\ type_memory_size tyv <= sz /\
    val_wf tyv v /\ value_has_type tyv v /\
    typed_copy_state_frame b (w2n w) n s t /\
    val_in_memory tyv v (w2n w) t.vs_memory /\
    (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
      val_in_memory tyv v (w2n w) mem) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!i. ~(w2n w <= i /\ i < w2n w+n) ==>
      (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    (!x. not_fresh_at b x ==>
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    alloca_frame old es sa s0 ce mid s /\
    (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==>
      FLOOKUP s.vs_allocas aid = SOME ent) /\
    (!aid off len i.
      FLOOKUP s0.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id /\
      (!name a cap. local_region old es.scopes s0 name a cap ==>
        off+len <= a \/ a+cap <= off) /\
      off <= i /\ i < off+len /\ i IN tn.t_mem ==> i IN tn0.t_mem) /\
    (!x z. not_fresh_at sa x /\ lookup_var x s0 = SOME z ==> lookup_var x s = SOME z) /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP G x = FLOOKUP G0 x /\ op_taint tn (Var x) = op_taint tn0 (Var x)) /\
    s0.vs_alloca_next <= s.vs_alloca_next /\
    ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
    t.vs_inst_idx = LENGTH sf.cs_current_insts /\ ~block_is_terminated sf /\
    return_buf_frame d ce sf t /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) ==>
    stmt_lands lctx sf (INL ()) t /\ ~t.vs_halted /\ ~block_is_terminated sf /\
    cenv_top_ext old ce out.scopes /\
    stmt_state_rel H ctx func ce cx out t /\
    storage_well_formed_on cx out (FST H) /\
    return_buf_frame d ce sf t /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at D lo d ce cx out Gf tf t /\
    (!x z. not_fresh_at sa x /\ lookup_var x s0 = SOME z ==> lookup_var x t = SOME z) /\
    (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==> FLOOKUP t.vs_allocas aid = SOME ent) /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tf (Var x) = op_taint tn0 (Var x)) /\
    alloca_frame old es sa s0 ce out t /\
    (!aid off len i.
      FLOOKUP s0.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id /\
      (!name a cap. local_region old es.scopes s0 name a cap ==>
        off+len <= a \/ a+cap <= off) /\
      off <= i /\ i < off+len /\ i IN tf.t_mem ==> i IN tn0.t_mem)
Proof
  rpt gen_tac >> strip_tac >>
  `typed_copy_state_frame b (w2n w) (type_memory_size tyv) s t` by
    (irule typedMemoryCopyTheory.typed_copy_state_frame_subinterval >>
     qexistsl_tac [`w2n w`, `n`] >> simp[]) >>
  `ghost_inv_at D lo d ce cx mid Gf tf t` by
    (irule annassign_memory_full_ghost_store >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `typed_copy_state_frame _ _ (type_memory_size _) _ _`)) >>
     goal_assum (drule_at (Pat `MEM _ (fn_insts _)`)) >> simp[] >>
     rpt strip_tac >> (metis_tac[])) >>
  `stmt_state_rel H ctx func ce cx out t` by suspend "state" >>
  `ghost_inv_at D lo d ce cx out Gf tf t` by suspend "ghost" >>
  `cenv_top_ext old ce out.scopes` by suspend "cenv" >>
  `storage_well_formed_on cx out (FST H)` by suspend "storage" >>
  `!aid off len. FLOOKUP s0.vs_allocas aid = SOME (off,len) /\
    aid < sa.cs_next_id ==> off+len <= w2n w \/ w2n w+sz <= off` by
    (rpt strip_tac >>
     `allocas_non_overlapping s` by
       (metis_tac[stateRelProjTheory.stmt_state_rel_local_ptrs_alloca,
         venomMemDefsTheory.alloca_inv_def]) >>
     `FLOOKUP s.vs_allocas aid = SOME (off,len)` by metis_tac[] >>
     `aid <> inst.inst_id` by decide_tac >>
     fs[venomMemDefsTheory.allocas_non_overlapping_def] >>
     qpat_x_assum `!a1 a2 b1 sz1 b2 sz2. _` drule_all >> simp[]) >>
  `!aid off len i. FLOOKUP s0.vs_allocas aid = SOME (off,len) /\
    aid < sa.cs_next_id /\ off <= i /\ i < off+len ==>
    (i IN tf.t_mem <=> i IN tn.t_mem)` by
    (rpt strip_tac >>
     `off+len <= w2n w \/ w2n w+sz <= off` by metis_tac[] >>
     first_x_assum irule >> decide_tac) >>
  `alloca_frame old es sa s0 ce out t` by suspend "frame" >>
  qpat_assum `typed_copy_state_frame _ _ n _ _`
    (strip_assume_tac o SRULE [typedMemoryCopyTheory.typed_copy_state_frame_def,
                              venomStateTheory.venom_state_component_equality]) >>
  simp[loweringPostsTheory.stmt_lands_def] >> rpt strip_tac >> gvs[] >>
  qpat_x_assum `!aid off len i. _ ==> i IN tn0.t_mem` irule >>
  conj_tac >- (qexistsl_tac [`aid`, `len`, `off`] >> simp[] >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `!aid off len i. _ ==> (i IN tf.t_mem <=> _)` drule_all >> simp[]
QED

Resume annassign_memory_full_installation_post[state]:
  simp[] >> irule stmtSimDeclCopyFrameTheory.stmt_state_rel_declare_copy_frame >>
  simp[] >> qexistsl_tac [`inst`, `s`, `b`, `w`] >> simp[] >>
  qpat_assum `typed_copy_state_frame _ _ (type_memory_size _) _ _`
    (strip_assume_tac o SRULE [typedMemoryCopyTheory.typed_copy_state_frame_def,
                              venomStateTheory.venom_state_component_equality]) >>
  fs[exprSimStorageCopyTheory.copy_static_def,
     venomStateTheory.venom_state_component_equality,
     typedMemoryCopyTheory.typed_copy_frame_def] >>
  conj_tac >- first_assum ACCEPT_TAC >> gvs[]
QED

Resume annassign_memory_full_installation_post[ghost]:
  simp[] >> fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `name = id`
  >- (gvs[lookup_scopes_def, FLOOKUP_UPDATE] >>
      `lookup_var p t = lookup_var p s` by
        (fs[typedMemoryCopyTheory.typed_copy_state_frame_def] >> metis_tac[]) >>
      conj_tac
      >- (irule assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame >>
          qexistsl_tac [`G`, `s`, `tn`] >> simp[] >> metis_tac[]) >>
      rpt strip_tac >> gvs[] >> metis_tac[]) >>
  `lookup_scopes name mid.scopes = SOME entry` by
    gvs[lookup_scopes_def, FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Resume annassign_memory_full_installation_post[frame]:
  rewrite_tac[stmtSimDefsTheory.alloca_frame_def] >> rpt gen_tac >> strip_tac >>
  Q.SUBGOAL_THEN `off + sz' <= w2n w \/ w2n w + sz <= off` assume_tac
  >- metis_tac[] >>
  qpat_x_assum `alloca_frame _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [stmtSimDefsTheory.alloca_frame_def]) >>
  disch_then drule_all >> strip_tac >>
  `!x. not_fresh_at b x ==> lookup_var x t = lookup_var x s` by
    fs[typedMemoryCopyTheory.typed_copy_state_frame_def] >>
  conj_tac
  >- (`mem_bytes_at off sz' t.vs_memory = mem_bytes_at off sz' s.vs_memory` by
        (fs[typedMemoryCopyTheory.typed_copy_state_frame_def,
            typedMemoryCopyTheory.typed_copy_frame_def] >>
         first_x_assum irule >> decide_tac) >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `!name q cap. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var q) cap) ==>
    lookup_var q t = lookup_var q s` by
    (rpt strip_tac >> first_x_assum irule >>
     fs[loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[]) >>
  Cases_on `n' = id`
  >- (gvs[loweringStateRelDefsTheory.local_region_def] >> metis_tac[]) >>
  qpat_x_assum `!n b sz. local_region ce mid.scopes s _ _ _ ==> _` irule >>
  qexists_tac `n'` >>
  gvs[loweringStateRelDefsTheory.local_region_def, lookup_scopes_def,
      FLOOKUP_UPDATE] >> metis_tac[]
QED

Resume annassign_memory_full_installation_post[cenv]:
  simp[loweringPostsTheory.cenv_top_ext_def] >>
  rpt strip_tac >> `n' = id` by metis_tac[] >> gvs[] >>
  qpat_x_assum `lookup_scopes id _ = NONE` mp_tac >>
  simp[lookup_scopes_def, CaseEq "option"]
QED

Resume annassign_memory_full_installation_post[storage]:
  irule (iffRL vyperStorageFootprintTheory.storage_well_formed_on_backends) >>
  qexists_tac `mid` >> simp[]
QED

Finalise annassign_memory_full_installation_post
