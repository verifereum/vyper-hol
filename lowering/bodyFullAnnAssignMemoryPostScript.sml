Theory bodyFullAnnAssignMemoryPost
Ancestors
  bodyFullMemoryStage bodyFullMemoryStore bodyFullPathHistory stateRelProj
  stmtLowering exprLoweringProps compileEnv context localPtrsProps
  fragGasOriginPtr fragGasSeqPtr fragExec emitHelperProps
  reasonCopySourcePtr allocaSiteResource venomMemDefs venomState
  typedCopyOriginPtrBase stmtSimDefs bodyMemAggregatePath bodyMemBopRestWordPath
  fragGasOrigin fragGasMode fragGasPath assignTuplePtrCopyLen

Theorem annassign_memory_full_assign_path:
  !H0 ctx func ce cx mid s sa sf xs p sw dw src_loc dty sty stv dtv v
   n sz aid0 start lo explicit PG G tn.
    compile_assign_value ce (Var p) LocMemory (Var xs) F src_loc
      dty sty (type_memory_bytes ce dty) sa = ((),sf) /\
    ~is_word_type dty /\ ~is_word_type sty /\
    stmt_state_rel H0 ctx func ce cx mid s /\
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
    type_memory_bytes ce sty = n /\ type_memory_size stv = n /\
    type_memory_bytes ce dty = type_memory_size dtv /\
    type_memory_size dtv <= sz /\ n < dimword (:256) /\
    value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
    not_fresh_at sa xs /\ not_fresh_at sa p /\
    lookup_var xs s = SOME sw /\ lookup_var p s = SOME dw /\
    FLOOKUP s.vs_allocas aid0 = SOME (w2n dw,sz) /\ aid0 < sa.cs_next_id /\
    ptr_covers G tn xs s n /\ ptr_covers G tn p s sz /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory stv v (w2n sw) mem) /\
    w2n sw+n < dimword (:256) /\
    w2n dw+type_memory_size dtv < dimword (:256) /\
    (n = 0 \/ w2n sw+n <= s.vs_alloca_next) /\
    (type_memory_size dtv = 0 \/ w2n dw+type_memory_size dtv <= s.vs_alloca_next) /\
    (src_loc = SOME LocMemory ==>
      expr_val_at ce cx sty start sa mid v (Var xs) s) /\
    (src_loc <> SOME LocMemory ==>
      w2n sw+n <= w2n dw \/ w2n dw+type_memory_size dtv <= w2n sw) /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
    (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?u sm Gu tnu t Gf tf.
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK t,Gf,tf)) /\
      (!H. stmt_state_rel H ctx func ce cx mid s ==>
        stmt_state_rel H ctx func ce cx mid u) /\
      (!D d. ghost_inv_at D lo d ce cx mid G tn s ==>
        ghost_inv_at D lo d ce cx mid Gu tnu u) /\
      alloca_frame ce mid sa s ce mid u /\
      (!aid off len i.
        FLOOKUP s.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id /\
        (!name a cap. local_region ce mid.scopes s name a cap ==>
          off+len <= a \/ a+cap <= off) /\
        off <= i /\ i < off+len /\ i IN tnu.t_mem ==> i IN tn.t_mem) /\
      (!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==> FLOOKUP u.vs_allocas aid = SOME ent) /\
      s.vs_alloca_next <= u.vs_alloca_next /\
      sa.cs_next_id <= sm.cs_next_id /\ local_ptrs_reserved ce sm /\
      (!x. not_fresh_at sa x ==>
        not_fresh_at sm x /\ lookup_var x u = lookup_var x s /\
        FLOOKUP Gu x = FLOOKUP G x /\ op_taint tnu (Var x) = op_taint tn (Var x)) /\
      lookup_var p u = SOME dw /\ ptr_covers Gu tnu p u sz /\
      typed_copy_state_frame sm (w2n dw) (type_memory_size dtv) u t /\
      val_in_memory dtv v (w2n dw) t.vs_memory /\
      (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
        val_in_memory dtv v (w2n dw) mem) /\
      tf.t_stor = tnu.t_stor /\ tf.t_trans = tnu.t_trans /\ tf.t_imm = tnu.t_imm /\
      (!i. ~(w2n dw <= i /\ i < w2n dw+type_memory_size dtv) ==>
        (i IN tf.t_mem <=> i IN tnu.t_mem)) /\
      (!x. not_fresh_at sm x ==>
        lookup_var x t = lookup_var x u /\ FLOOKUP Gf x = FLOOKUP Gu x /\
        op_taint tf (Var x) = op_taint tnu (Var x)) /\
      ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `alloca_inv s` by metis_tac[stmt_state_rel_local_ptrs_alloca] >>
  `ptr_covers G tn p s (type_memory_size dtv)` by
    metis_tac[ptr_covers_mono] >>
  Cases_on `src_loc = SOME LocMemory`
  >- suspend "staged" >>
  `compile_store_memory ce (Var xs) (Var p) dty sty sa = ((),sf)` by
    gvs[compile_assign_value_def] >>
  qpat_x_assum `type_memory_size stv = n` (SUBST_ALL_TAC o SYM) >>
  drule body_full_memory_store_path >>
  disch_then (drule_at (Pat `evaluate_type _ sty = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ dty = _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ xs _ _`)) >>
  disch_then (drule_at (Pat `value_has_type stv _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `lookup_var p s = _`)) >>
  disch_then (drule_at (Pat `lookup_var xs s = _`)) >>
  disch_then (qspecl_then [`explicit`,`ctx`,`PG`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  disch_then (qx_choosel_then [`t`,`Gf`,`tf`] strip_assume_tac) >>
  `alloca_history func t` by
    metis_tac[body_full_path_alloca_history] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (drule typed_copy_state_frame_allocas_below_fmp >> simp[]) >>
  qexistsl_tac [`s`,`sa`,`G`,`tn`,`t`,`Gf`,`tf`] >>
  simp[alloca_frame_def] >> metis_tac[]
QED

Resume annassign_memory_full_assign_path[staged]:
  gvs[compile_assign_value_def,comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rename1 `compile_alloc_buffer _ sa = (buf,sb)` >>
  rename1 `compile_copy_memory _ (Var xs) _ sb = ((),sm)` >>
  `ci_mono sa sb /\ ci_mono sb sm /\ ci_mono sm sf` by
    metis_tac[ci_mono_compile_alloc_buffer,ci_mono_compile_copy_memory,
      ci_mono_compile_store_memory,pairTheory.SND] >>
  `cs_extends sa sb /\ cs_extends sb sm /\ cs_extends sm sf` by fs[ci_mono_def] >>
  `fn_has_code sa sb func /\ fn_has_code sb sm func /\ fn_has_code sm sf func` by
    metis_tac[fn_has_code_split,cs_extends_trans] >>
  drule_at (Pat `compile_alloc_buffer _ _ = _`) body_full_memory_stage_frame_path >>
  disch_then (drule_at (Pat `compile_copy_memory _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ xs _ _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ sty = _`)) >>
  disch_then (drule_at (Pat `lookup_var xs s = _`)) >>
  disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  disch_then (qx_choosel_then [`u`,`root`,`b`,`Gu`,`tnu`] strip_assume_tac) >>
  qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _`
    (qspec_then `cx_dead H0 cx` mp_tac) >>
  disch_then (strip_assume_tac o MATCH_MP gas_origin_ptr_path_projections) >>
  drule gas_origin_path_erase >> strip_tac >>
  `gas_path_mem ctx func s 0 (OK u)` by fs[gas_marked_path_def] >>
  `alloca_inv u` by metis_tac[bodyMemAggregatePathTheory.aggregate_mem_path_alloca_inv] >>
  `s.vs_alloca_next <= u.vs_alloca_next` by
    (drule gas_marked_path_exec >> strip_tac >>
     drule bodyMemBopRestWordPathTheory.rest_word_path_frontier >> simp[]) >>
  `not_fresh_at sm p /\ lookup_var p u = SOME dw /\
   FLOOKUP Gu p = FLOOKUP G p /\ op_taint tnu (Var p) = op_taint tn (Var p)` by
    metis_tac[] >>
  `ptr_covers Gu tnu p u sz /\ ptr_covers Gu tnu p u (type_memory_size dtv)` by
    metis_tac[ptr_covers_lookup_frame] >>
  `FLOOKUP u.vs_allocas aid0 = SOME (w2n dw,sz)` by metis_tac[] >>
  (Q.SUBGOAL_THEN `b + type_memory_size stv <= w2n dw \/ w2n dw + sz <= b` assume_tac
  >-
    (qpat_assum `alloca_inv u`
       (strip_assume_tac o REWRITE_RULE [alloca_inv_def,allocas_non_overlapping_def]) >>
     qpat_x_assum `!a1 a2 b1 sz1 b2 sz2. _`
       (qspecl_then [`sa.cs_next_id`,`aid0`,`b`,
         `type_memory_size stv`,`w2n dw`,`sz`] mp_tac) >> simp[])) >>
  `compile_store_memory ce (Var root) (Var p) dty sty sm = ((),sf)` by
    metis_tac[] >>
  `b < dimword (:256)` by decide_tac >>
  `w2n ((n2w b):bytes32) = b` by simp[] >>
  (Q.SUBGOAL_THEN `w2n ((n2w b):bytes32) + type_memory_size stv < dimword (:256) /\
   (type_memory_size stv = 0 \/ w2n ((n2w b):bytes32) + type_memory_size stv <= u.vs_alloca_next) /\
   (type_memory_size dtv = 0 \/ w2n dw + type_memory_size dtv <= u.vs_alloca_next) /\
   (w2n ((n2w b):bytes32) + type_memory_size stv <= w2n dw \/
    w2n dw + type_memory_size dtv <= w2n ((n2w b):bytes32))` assume_tac
  >- (simp[] >> decide_tac)) >>
  drule_at (Pat `compile_store_memory ce (Var root) _ _ _ _ = _`)
    body_full_memory_store_path >>
  disch_then (fn th => qpat_assum `evaluate_type _ sty = SOME stv`
    (mp_then (Pat `evaluate_type _ sty = _`) mp_tac th)) >>
  disch_then (fn th => qpat_assum `evaluate_type _ dty = SOME dtv`
    (mp_then (Pat `evaluate_type _ dty = _`) mp_tac th)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ root _ _`)) >>
  disch_then (drule_at (Pat `value_has_type stv _`)) >>
  disch_then (drule_at (Pat `allocas_from _ u`)) >>
  disch_then (drule_at (Pat `fn_has_code sm sf _`)) >>
  disch_then (drule_at (Pat `lookup_var p u = _`)) >>
  disch_then (drule_at (Pat `lookup_var root u = _`)) >>
  disch_then (qspecl_then [`explicit`,`ctx`,`PG`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  disch_then (qx_choosel_then [`t`,`Gf`,`tf`] strip_assume_tac) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)` by
    (gen_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _`
       (qspec_then `D` mp_tac) >>
     disch_then (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
     disch_then (qspecl_then [`u`,`Gu`,`tnu`,`[]`,`OK t`,`Gf`,`tf`] mp_tac) >>
     simp[]) >>
  `alloca_history func t` by metis_tac[body_full_path_alloca_history] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (drule typed_copy_state_frame_allocas_below_fmp >> simp[]) >>
  `sa.cs_next_id <= sm.cs_next_id` by
    (qpat_assum `ci_mono sa sb` mp_tac >>
     qpat_assum `ci_mono sb sm` mp_tac >>
     pure_rewrite_tac[ci_mono_def] >> rpt strip_tac >> decide_tac) >>
  `local_ptrs_reserved ce sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >>
     simp[] >> qpat_assum `ci_mono sa sb` mp_tac >>
     qpat_assum `ci_mono sb sm` mp_tac >>
     pure_rewrite_tac[ci_mono_def] >> rpt strip_tac >> decide_tac) >>
  qexistsl_tac [`u`,`sm`,`Gu`,`tnu`,`t`,`Gf`,`tf`] >>
  simp[] >> rpt conj_tac >>
  FIRST
    [qpat_x_assum `typed_copy_state_frame _ _ _ _ _` mp_tac >> simp[] >> NO_TAC,
     map_every qx_gen_tac [`aid`,`off`,`len`,`i`] >> strip_tac >>
     qpat_x_assum `!aid off sz i. _`
       (qspecl_then [`aid`,`off`,`len`,`i`] mp_tac) >>
     simp[arithmeticTheory.ADD_COMM] >> disch_then irule >>
     rpt strip_tac >>
     qpat_x_assum `!name a cap. local_region ce mid.scopes s name a cap ==> _` drule >>
     simp[]]
QED

Finalise annassign_memory_full_assign_path
