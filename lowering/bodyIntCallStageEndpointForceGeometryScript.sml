(* One forcing witness carrying separation from an older destination. *)
Theory bodyIntCallStageEndpointForceGeometry
Ancestors
  bodyIntCallFamCallIntForcingLocal bodyIntCallFamCallIntForcingFrames
  bodyIntCallWindowPosts bodyIntCallForcingReadOnly exprSimAggregateChildren
  exprSimCopy exprSimProps exprLoweringProps context bodyIntCallWindowStorage

Theorem intcall_stage_protected_forcing:
  unwrap_value ce vv sa = (op,sb) /\
  vv_holds ce cx ty (Value v) vv es s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  type_memory_bytes ce ty = type_memory_size tv /\ type_memory_size tv < 2**64 /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sa /\
  allocas_above lo s /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sa x) /\
  (!q x. reserved q /\ q = Var x ==> not_fresh_at sa x) /\
  (!p k. P p k ==> p+k <= lo) /\
  (!p k. Win p k ==> ?id a len. id < sa.cs_next_id /\
    FLOOKUP s.vs_allocas id = SOME (a,len) /\ a <= p /\ p+k <= a+len) /\
  (ty <> NoneT /\ ~is_word_type ty /\ ~is_bytestring_type ty /\
    (case vv of StackValue _ _ => T | LocatedValue _ p => p.ptr_location = LocMemory) ==>
    ?w a k. eval_operand (vv_operand vv) s = SOME w /\
      a <= w2n w /\ w2n w + type_memory_size tv <= a+k /\ a+k < dimword (:256) /\
      (lo <= a \/ ?d z. staged d z /\ d <= a /\ a+k <= d+z)) /\
  FLOOKUP s.vs_allocas aid = SOME (b,cap) /\ aid < sa.cs_next_id /\
  ((case vv of StackValue _ _ => ~is_word_type ty
      | LocatedValue _ p => p.ptr_location = LocMemory) ==>
    !src. val_footprint tv v <> 0 /\ eval_operand (vv_operand vv) s = SOME src ==>
      regions_disjoint (w2n src) (val_footprint tv v) b cap) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    expr_val_rel cx ty v op u /\ stmt_state_rel ctx func ce cx es u /\
    allocas_above lo u /\ s.vs_alloca_next <= u.vs_alloca_next /\
    (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==> FLOOKUP u.vs_allocas id = SOME entry) /\
    (!p k. P p k ==> mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (!p k. Win p k ==> mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (!q. reserved q ==> eval_operand q u = eval_operand q s) /\
    (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==> lookup_var x u = SOME w) /\
    locals_kept ce es es s u /\
    (!sv. sv.cs_next_id <= sa.cs_next_id /\ vv_at ce cx ty sv sa es (Value v) vv s ==>
      expr_val_at ce cx ty sv sb es v op u) /\
    (!name a n. local_region ce scopes u name a n <=> local_region ce scopes s name a n) /\
    (ty <> NoneT /\ ~is_word_type ty /\ ~is_bytestring_type ty ==>
      ?w a k. eval_operand op u = SOME w /\ a <= w2n w /\
        w2n w + type_memory_size tv <= a+k /\ a+k < dimword (:256) /\
        (lo <= a \/ ?d z. staged d z /\ d <= a /\ a+k <= d+z)) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!src. ~is_word_type ty /\ val_footprint tv v <> 0 /\ eval_operand op u = SOME src ==>
      regions_disjoint (w2n src) (val_footprint tv v) b cap)
Proof
  strip_tac >> Cases_on `vv`
  >- suspend "stack" >>
  rename1 `LocatedValue ann p` >>
  Cases_on `is_word_type ty`
  >- suspend "word" >>
  Cases_on `p.ptr_location = LocMemory`
  >- suspend "memory" >>
  `ann = ty` by fs[loweringPostsTheory.vv_holds_def] >> gvs[] >>
  `p.ptr_location <> LocCalldata` by
    (Cases_on `p.ptr_location` >> fs[loweringPostsTheory.vv_holds_def]) >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sa x` by fs[vv_operand_def] >>
  `sa.cs_next_id < sb.cs_next_id` by
    (drule_all unwrap_materialization_id >> simp[]) >>
  Cases_on `p.ptr_location = LocCode`
  >- suspend "code" >> suspend "storage"
QED

Resume intcall_stage_protected_forcing[stack]:
  drule (SRULE [] protected_identity_value_forcing) >>
  disch_then drule >> simp[] >>
  disch_then (qspecl_then [`func`, `ctx`] strip_assume_tac) >>
  qexists `s` >> gvs[vv_operand_def] >>
  simp[loweringPostsTheory.vv_at_def, loweringPostsTheory.vv_own_def,
       vyperStateTheory.read_result_def, vyperStateTheory.return_def]
QED
Resume intcall_stage_protected_forcing[word]:
  drule_all protected_word_value_frame_forcing >>
  disch_then (qspec_then `scopes` strip_assume_tac) >>
  `u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
   u.vs_alloca_next = s.vs_alloca_next` by
    (rpt conj_tac >> qpat_assum `u = _` (fn th => simp[Once th])) >>
  qexists `u` >> fs[intCallFrameTheory.allocas_above_def,
    loweringPostsTheory.expr_val_at_def] >> metis_tac[]
QED
Resume intcall_stage_protected_forcing[memory]:
  drule protected_identity_value_forcing >> disch_then drule >> simp[] >>
  disch_then (qspecl_then [`func`, `ctx`] strip_assume_tac) >>
  qexists `s` >> gvs[vv_operand_def] >>
  simp[loweringPostsTheory.vv_at_def, loweringPostsTheory.expr_val_at_def,
       vyperStateTheory.read_result_def, vyperStateTheory.return_def]
QED
Resume intcall_stage_protected_forcing[code]:
  mp_tac (Q.INST [`reserved` |-> `reserved`, `Win` |-> `Win`, `P` |-> `P`,
      `scopes` |-> `scopes`, `tv` |-> `tv`, `ty` |-> `ann`]
      (SPEC_ALL intcall_code_forcing_frames)) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `!name a n. local_region ce es.scopes u name a n <=>
    local_region ce es.scopes s name a n` by
    (irule copy_buffer_local_region_frame >> qexists `sa` >> simp[]) >>
  mp_tac (Q.INST [`ty` |-> `ann`, `s` |-> `s`, `u` |-> `u`]
    materialized_value_location) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> disch_tac >>
  `regions_disjoint (w2n w) (type_memory_size tv) b cap` by
    (irule exprSimPrecompilesTheory.state_allocations_disjoint >>
     goal_assum (drule_at Any) >> `sa.cs_next_id <> aid` by decide_tac >> metis_tac[]) >>
  `val_footprint tv v <= type_memory_size tv` by metis_tac[val_footprint_le] >>
  qexists `u` >> simp[] >>
  conj_tac >- (strip_tac >> qexistsl_tac [`w2n w`, `type_memory_size tv`] >> simp[]) >>
  rpt strip_tac >> gvs[] >> fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED
Resume intcall_stage_protected_forcing[storage]:
  `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient` by
    (Cases_on `p.ptr_location` >> fs[]) >>
  mp_tac (Q.INST [`reserved` |-> `reserved`, `Win` |-> `Win`, `P` |-> `P`,
      `scopes` |-> `scopes`, `tv` |-> `tv`, `ty` |-> `ann`]
      (SPEC_ALL intcall_storage_forcing_frames)) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `!name a n. local_region ce es.scopes u name a n <=>
    local_region ce es.scopes s name a n` by
    (irule copy_buffer_local_region_frame >> qexists `sa` >> simp[]) >>
  mp_tac (Q.INST [`ty` |-> `ann`, `s` |-> `s`, `u` |-> `u`]
    materialized_value_location) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> disch_tac >>
  `regions_disjoint (w2n w) (type_memory_size tv) b cap` by
    (irule exprSimPrecompilesTheory.state_allocations_disjoint >>
     goal_assum (drule_at Any) >> `sa.cs_next_id <> aid` by decide_tac >> metis_tac[]) >>
  `val_footprint tv v <= type_memory_size tv` by metis_tac[val_footprint_le] >>
  (qexists `u` >> simp[] >>
   conj_tac >- (strip_tac >> qexistsl_tac [`w2n w`, `type_memory_size tv`] >> simp[]) >>
   rpt strip_tac >> gvs[] >> fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac)
QED
Finalise intcall_stage_protected_forcing
