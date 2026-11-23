(* Physical nonword copy, with a separate endpoint for the optional snapshot. *)
Theory bodyLocalTypedCopyPathMods
Ancestors
  arithmetic assignTuplePtrCopyLen bodyFullMemoryStage bodyFullMemoryStore
  bodyFullPathHistory bodyMemBopRestWordPath bodyMemoryDefs bodyPtrDefs
  compileEnv exprLoweringProps finite_map fragExec fragGasOriginPtr fragGasMode
  fragGasOrigin fragGasOriginPtrLoop freshWrites loweringPosts loweringStateRelDefs ptrDiscipline
  reasonCopySourcePtr stateRelProj stmtLowering stmtSimDefs typedCopyOriginPtrBase
  typedMemoryCopy venomMemDefs venomState words
Libs
  monadsyntax

Theorem local_typed_copy_path_mods:
  compile_assign_value ce (Var xd) LocMemory (Var xs) F loc dty sty
    (type_memory_bytes ce dty) sa = ((),sf) /\
  ~is_word_type dty /\ ~is_word_type sty /\
  stmt_state_rel (H0 : (bool # 256 word # type_value) list # num list)
    ctx func ce cx mid s /\
  fn_has_code sa sf func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ alloca_history func s /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,len). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      len = type_memory_size tv) fields) /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  type_memory_bytes ce sty = type_memory_size stv /\
  type_memory_bytes ce dty = type_memory_size dtv /\
  type_memory_size stv < dimword (:256) /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  not_fresh_at sa xs /\ not_fresh_at sa xd /\
  lookup_var xs s = SOME sw /\ lookup_var xd s = SOME dw /\
  ptr_covers G tn xs s (type_memory_size stv) /\ ptr_covers G tn xd s cap /\
  type_memory_size dtv <= cap /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory stv v (w2n sw) mem) /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  w2n dw + type_memory_size dtv < dimword (:256) /\
  (type_memory_size stv = 0 \/ w2n sw + type_memory_size stv <= s.vs_alloca_next) /\
  (type_memory_size dtv = 0 \/ w2n dw + type_memory_size dtv <= s.vs_alloca_next) /\
  (loc = SOME LocMemory ==>
    expr_val_at ce cx sty start sa mid v (Var xs) s /\
    ?b len. b <= w2n dw /\ w2n dw + type_memory_size dtv <= b + len /\
      ((?name. local_region ce mid.scopes s name b len) \/
       ?aid. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len))) /\
  (loc <> SOME LocMemory ==>
    w2n sw + type_memory_size stv <= w2n dw \/
    w2n dw + type_memory_size dtv <= w2n sw) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ lo <= w2n dw /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!x len. ce.ce_return_buf = SOME (PtrVar (Var x) len) ==> not_fresh_at sa x) /\
  (!x len. ce.ce_return_pc = SOME (PtrVar (Var x) len) ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u sc Gu tu t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    (!H : (bool # 256 word # type_value) list # num list.
      stmt_state_rel H ctx func ce cx mid s ==> stmt_state_rel H ctx func ce cx mid u) /\
    (!D d. ghost_inv_at D lo d ce cx mid G tn s ==>
      ghost_inv_at D lo d ce cx mid Gu tu u) /\
    alloca_frame ce mid sa s ce mid u /\
    (!aid off len i.
      FLOOKUP s.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id /\
      (!name a sz. local_region ce mid.scopes s name a sz ==>
        off+len <= a \/ a+sz <= off) /\
      off <= i /\ i < off+len /\ i IN tu.t_mem ==> i IN tn.t_mem) /\
    (!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==> FLOOKUP u.vs_allocas aid = SOME ent) /\
    s.vs_alloca_next <= u.vs_alloca_next /\ sa.cs_next_id <= sc.cs_next_id /\
    local_ptrs_reserved ce sc /\
    (!name b len. local_region ce mid.scopes u name b len <=>
      local_region ce mid.scopes s name b len) /\
    (!x. not_fresh_at sa x ==> not_fresh_at sc x /\ lookup_var x u = lookup_var x s /\
      FLOOKUP Gu x = FLOOKUP G x /\ op_taint tu (Var x) = op_taint tn (Var x)) /\
    lookup_var xd u = SOME dw /\ ptr_covers Gu tu xd u cap /\
    typed_copy_state_frame sc (w2n dw) (type_memory_size dtv) u t /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
      val_in_memory dtv v (w2n dw) mem) /\
    tf.t_stor = tu.t_stor /\ tf.t_trans = tu.t_trans /\ tf.t_imm = tu.t_imm /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size dtv) ==>
      (i IN tf.t_mem <=> i IN tu.t_mem)) /\
    (!x. not_fresh_at sc x ==> lookup_var x t = lookup_var x u /\
      FLOOKUP Gf x = FLOOKUP Gu x /\ op_taint tf (Var x) = op_taint tu (Var x)) /\
    ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
    t.vs_inst_idx = LENGTH sf.cs_current_insts /\
    alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo u.vs_memory /\
    (!i. i < lo ==> (i IN tf.t_mem <=> i IN tu.t_mem))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ptr_covers G tn xd s (type_memory_size dtv)` by
    metis_tac[ptr_covers_mono] >>
  Cases_on `loc = SOME LocMemory`
  >- suspend "staged" >>
  `compile_store_memory ce (Var xs) (Var xd) dty sty sa = ((),sf)` by
    fs[compile_assign_value_def] >>
  suspend "direct"
QED

Resume local_typed_copy_path_mods[direct]:
  mp_tac (Q.INST [`tenv` |-> `get_tenv cx`, `cenv` |-> `ce`, `sb` |-> `sf`]
    (SPEC_ALL body_full_memory_store_path)) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  `alloca_history func t` by
    (qpat_assum `!D. gas_origin_ptr_path _ _ _ _`
       (qspec_then `cx_dead H0 cx` assume_tac) >>
     metis_tac[body_full_path_alloca_history, stmt_state_rel_local_ptrs_alloca]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (drule typed_copy_state_frame_allocas_below_fmp >> simp[]) >>
  `alloca_frame ce mid sa s ce mid s` by rw[alloca_frame_def] >>
  qexistsl_tac [`s`,`sa`,`G`,`tn`,`t`,`Gf`,`tf`] >> simp[] >>
  suspend "direct_low"
QED

Resume local_typed_copy_path_mods[direct_low]:
  qhdtm_assum `typed_copy_state_frame`
    (strip_assume_tac o REWRITE_RULE [typed_copy_state_frame_def,typed_copy_frame_def]) >>
  first_x_assum irule >> simp[]
QED

Resume local_typed_copy_path_mods[staged]:
  qpat_x_assum `loc = SOME LocMemory ==> _` drule >>
  disch_then (fn th => assume_tac (CONJUNCT1 th) >> assume_tac (CONJUNCT2 th)) >>
  qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_assign_value_def,comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  rename1 `compile_alloc_buffer _ sa = (buf,sb)` >>
  rename1 `compile_copy_memory _ (Var xs) _ sb = (r,sc)` >>
  Cases_on `r` >>
  `ci_mono sa sb /\ ci_mono sb sc /\ ci_mono sc sf` by
    metis_tac[ci_mono_compile_alloc_buffer,ci_mono_compile_copy_memory,
      ci_mono_compile_store_memory,pairTheory.SND] >>
  `fn_has_code sa sb func /\ fn_has_code sb sc func /\ fn_has_code sc sf func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split,cs_extends_trans]) >>
  mp_tac (Q.INST [`cenv` |-> `ce`,`es` |-> `mid`,`tv` |-> `stv`,
    `n` |-> `type_memory_size stv`,`sm` |-> `sb`,`sb` |-> `sc`]
    (SPEC_ALL (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``]
      body_full_memory_stage_frame_path))) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`u`,`root`,`b0`,`Gu`,`tu`] strip_assume_tac) >>
  suspend "staged_store"
QED

Resume local_typed_copy_path_mods[staged_store]:
  `ci_mono sa sc` by metis_tac[ci_mono_trans] >>
  `sa.cs_next_id <= sc.cs_next_id /\ sa.cs_next_var <= sc.cs_next_var` by
    (qpat_assum `ci_mono sa sc` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >> simp[]) >>
  `local_ptrs_reserved ce sc` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `!name a len. local_region ce mid.scopes u name a len <=>
    local_region ce mid.scopes s name a len` by
    (rw[local_region_def] >> metis_tac[local_ptrs_reserved_def]) >>
  `lookup_var xd u = SOME dw /\ not_fresh_at sc xd` by metis_tac[] >>
  `ptr_covers Gu tu xd u cap /\ ptr_covers Gu tu xd u (type_memory_size dtv)` by
    metis_tac[ptr_covers_lookup_frame] >>
  `b0 < dimword (:256)` by decide_tac >>
  `w2n ((n2w b0):bytes32) = b0` by simp[] >>
  `compile_store_memory ce (Var root) (Var xd) dty sty sc = ((),sf)` by fs[] >>
  `s.vs_alloca_next <= u.vs_alloca_next` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _`
       (qspec_then `cx_dead H0 cx` mp_tac) >>
     disch_then (strip_assume_tac o MATCH_MP gas_origin_ptr_path_projections) >>
     drule gas_origin_path_erase >> strip_tac >> drule gas_marked_path_exec >>
     strip_tac >> drule rest_word_path_frontier >> simp[]) >>
  `b0 + type_memory_size stv <= w2n dw \/
   w2n dw + type_memory_size dtv <= b0` by suspend "snapshot_separation" >>
  mp_tac (Q.INST [`tenv` |-> `get_tenv cx`,`cenv` |-> `ce`,`xs` |-> `root`,
    `sa` |-> `sc`,`sb` |-> `sf`,`s` |-> `u`,`G` |-> `Gu`,`tn` |-> `tu`,
    `sw` |-> `(n2w b0):bytes32`] (SPEC_ALL body_full_memory_store_path)) >>
  (impl_tac >-
    (qpat_assum `w2n (n2w b0 : bytes32) = b0` (fn th => pure_rewrite_tac[th]) >>
     simp[] >> rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, decide_tac])) >>
  strip_tac >> suspend "store_post"
QED

Resume local_typed_copy_path_mods[snapshot_separation]:
  first_x_assum (CHOOSE_THEN (CHOOSE_THEN strip_assume_tac)) >>
  rename1 `w2n dw + type_memory_size dtv <= dstbase + len` >>
  `regions_disjoint b0 (type_memory_size stv) dstbase len` by
    (FIRST
       [qpat_assum `local_region ce mid.scopes s _ dstbase len` mp_tac >>
        qpat_assum `!name a len. local_region ce mid.scopes u name a len ==> _` mp_tac >>
        simp[] >> metis_tac[],
        `stmt_state_rel H0 ctx func ce cx mid u` by simp[] >>
        `alloca_inv u` by metis_tac[stmt_state_rel_local_ptrs_alloca] >>
        `FLOOKUP u.vs_allocas aid = SOME (dstbase,len)` by simp[] >>
        `sa.cs_next_id <> aid` by decide_tac >>
        qpat_x_assum `alloca_inv u`
          (strip_assume_tac o REWRITE_RULE [alloca_inv_def,allocas_non_overlapping_def]) >>
        qpat_x_assum `!a1 a2 b1 sz1 b2 sz2. _`
          (qspecl_then [`sa.cs_next_id`,`aid`,`b0`,`type_memory_size stv`,`dstbase`,`len`] mp_tac) >>
        simp[loweringStateRelDefsTheory.regions_disjoint_def]]) >>
  qpat_x_assum `regions_disjoint _ _ _ _` mp_tac >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Resume local_typed_copy_path_mods[store_post]:
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK t,Gf,tf)` by
    (gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gu`,`u`,`tu`] >> simp[]) >>
  `alloca_history func t` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ (OK t,Gf,tf)`
       (qspec_then `cx_dead H0 cx` assume_tac) >>
     metis_tac[body_full_path_alloca_history, stmt_state_rel_local_ptrs_alloca]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (drule typed_copy_state_frame_allocas_below_fmp >> simp[]) >>
  `mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo u.vs_memory` by
    (qhdtm_assum `typed_copy_state_frame`
       (strip_assume_tac o REWRITE_RULE [typed_copy_state_frame_def,typed_copy_frame_def]) >>
     first_x_assum irule >> simp[]) >>
  qexistsl_tac [`u`,`sc`,`Gu`,`tu`,`t`,`Gf`,`tf`] >>
  simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise local_typed_copy_path_mods
