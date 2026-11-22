(* Plain raw-blueprint unwrap, with the already allocated snapshot destination
   carried to the same endpoint as the physical source. *)
Theory createBlueprintRawUnwrap
Ancestors
  createCtorMaterializePhysical createCtorUnwrapIdentityArrival
  createCtorUnwrapRuntimeCodeArrival createCtorUnwrapCtorCodeArrival
  createCtorUnwrapSlotArrival exprLoweringProps exprOperandVar
  exprSimProps exprSimSubscriptArrayFrame stateRelProj allocaSiteResource
  reasonCopySourcePtr valueCopyBytes bodyMemoryDefs freshWrites
  loweringPosts bodyPtrDefs ptrDiscipline venomState finite_map
  context compileEnv vyperValue vyperState vyperTyping vyperStorageFootprint relation words

Theorem create_blueprint_raw_unwrap_store_entry:
  expr_body_pre ce cx env e es /\
  compile_expr ce ty e sa = (vv,sm) /\
  eval_expr cx e es = (INL pv,ee) /\
  read_result cx pv ee = (INL (BytesV bytes),ee) /\
  is_bytestring_type (post_value_type ce e) /\
  is_bytestring_type (lowered_value_type ce e) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rty /\
  type_memory_bytes ce (post_value_type ce e) = type_memory_size rty /\
  type_memory_size rty < 2**64 /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
  unwrap_value ce vv mid = (src,su) /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_var <= mid.cs_next_var /\ sm.cs_next_id <= mid.cs_next_id /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  fn_has_code mid su func /\ fn_inst_ids_distinct func /\
  (!bb. lookup_block su.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx func ce cx e es sa sm s0 ee pv vv a /\
    ghost_inv_at (DF H) lo d ce cx ee Ga ta a) /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee pv vv a /\
  ~a.vs_halted /\ a.vs_current_bb = mid.cs_current_bb /\
  a.vs_inst_idx = LENGTH mid.cs_current_insts /\
  alloca_history func a /\ s0.vs_alloca_next <= a.vs_alloca_next /\
  ptr_vv_ok cx (post_value_type ce e) pv vv ee Ga ta a /\
  (!t op. vv = StackValue t op ==> ptr_buf_ok ce e op Ga a) /\
  (!t q. vv = LocatedValue t q /\ q.ptr_location = LocMemory ==>
    ptr_buf_ok ce e q.ptr_operand Ga a) /\
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    !w. eval_operand (vv_operand vv) a = SOME w ==>
      w2n w + type_memory_size rty <= lo /\
      (!mem. mem_agree_outside ta.t_mem a.vs_memory mem ==>
        val_in_memory rty (BytesV bytes) (w2n w) mem)) /\
  ghost_kept_at lo ce es sa Gi ti s0 Ga ta /\ return_buf_frame d ce mid a /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  not_fresh_at mid p /\ lookup_var p a = SOME dw /\ ptr_covers Ga ta p a N /\
  aid < mid.cs_next_id /\ FLOOKUP a.vs_allocas aid = SOME (w2n dw,N) /\
  (!name b len. local_region ce ee.scopes a name b len ==>
    regions_disjoint (w2n dw) N b len) ==>
  ?z Gz tz q sw.
    RTC (\u v. ?i. ctor_segment_fetch func u = SOME i /\
      mid.cs_next_id <= i.inst_id /\ i.inst_id < su.cs_next_id /\
      i.inst_opcode <> INVOKE /\ ctor_segment_next func u i = SOME v) a z /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (a,Ga,ta) [] (OK z,Gz,tz) /\
      stmt_state_rel H ctx func ce cx ee z /\ ghost_inv_at (DF H) lo d ce cx ee Gz tz z) /\
    ~z.vs_halted /\ z.vs_current_bb = su.cs_current_bb /\
    z.vs_inst_idx = LENGTH su.cs_current_insts /\
    alloca_history func z /\ a.vs_alloca_next <= z.vs_alloca_next /\
    src = Var q /\ lookup_var q z = SOME sw /\ eval_operand src z = SOME sw /\
    not_fresh_at su q /\ not_fresh_at su p /\
    value_has_type tv (BytesV bytes) /\ val_wf tv (BytesV bytes) /\
    (!mem. mem_agree_outside tz.t_mem z.vs_memory mem ==>
      val_in_memory tv (BytesV bytes) (w2n sw) mem) /\
    ptr_covers Gz tz q z (val_store_size tv (BytesV bytes)) /\
    w2n sw + val_store_size tv (BytesV bytes) <= z.vs_alloca_next /\
    lookup_var p z = SOME dw /\ ptr_covers Gz tz p z N /\
    FLOOKUP z.vs_allocas aid = SOME (w2n dw,N) /\ w2n dw + N <= z.vs_alloca_next /\
    (!name b len. local_region ce ee.scopes z name b len ==>
      regions_disjoint (w2n dw) N b len) /\
    (!name b len. local_region ce es.scopes s0 name b len ==>
      regions_disjoint (w2n dw) N b len) /\
    (!x. not_fresh_at mid x ==> lookup_var x z = lookup_var x a /\
      FLOOKUP Gz x = FLOOKUP Ga x /\ op_taint tz (Var x) = op_taint ta (Var x)) /\
    local_ptrs_reserved ce su /\ return_buf_frame d ce su z /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    wb_frame ce es ee sa s0 z /\ ghost_kept_at lo ce es sa Gi ti s0 Gz tz /\
    (~expr_has_effect e ==> pure_frame ce func es sa s0 z)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by fs[storage_trace_domain_def,Abbr `H0`] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `H0` (drule_then strip_assume_tac)) >>
  `~is_word_type (post_value_type ce e) /\ ~is_word_type (lowered_value_type ce e)` by
    simp[is_bytestring_word_type] >>
  `ci_mono mid su` by metis_tac[ci_mono_unwrap_value,pairTheory.SND] >>
  `mid.cs_next_var <= su.cs_next_var` by fs[ci_mono_def] >>
  `?z Gz tz.
    RTC (\u v. ?i. ctor_segment_fetch func u = SOME i /\
      mid.cs_next_id <= i.inst_id /\ i.inst_id < su.cs_next_id /\
      i.inst_opcode <> INVOKE /\ ctor_segment_next func u i = SOME v) a z /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (a,Ga,ta) [] (OK z,Gz,tz) /\
      expr_post H ctx func ce cx e es sa su s0 ee (BytesV bytes) src z /\
      ghost_inv_at (DF H) lo d ce cx ee Gz tz z) /\
    ~z.vs_halted /\ z.vs_current_bb = su.cs_current_bb /\
    z.vs_inst_idx = LENGTH su.cs_current_insts /\
    alloca_history func z /\ a.vs_alloca_next <= z.vs_alloca_next /\
    ptr_val_ok cx (post_value_type ce e) (BytesV bytes) src Gz tz z /\
    ptr_buf_ok ce e src Gz z /\
    (!rt w. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
      eval_operand src z = SOME w ==>
      type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    ghost_kept_at lo ce es sa Gi ti s0 Gz tz /\
    (!x. not_fresh_at mid x ==> lookup_var x z = lookup_var x a /\
      FLOOKUP Gz x = FLOOKUP Ga x /\ op_taint tz (Var x) = op_taint ta (Var x)) /\
    wb_frame ce ee ee mid a z /\ ghost_kept_at lo ce ee mid Ga ta a Gz tz` by suspend "unwrap" >>
  suspend "physical"
QED

Resume create_blueprint_raw_unwrap_store_entry[unwrap]:
  Q.SUBGOAL_THEN
    `((?ann op. vv = StackValue ann op) \/
      (?ann q. vv = LocatedValue ann q /\ q.ptr_location = LocMemory /\ ~is_word_type ann)) \/
     (?ann q. vv = LocatedValue ann q /\ q.ptr_location = LocCode /\ ~is_word_type ann) \/
     (?ann q. vv = LocatedValue ann q /\
        (q.ptr_location = LocStorage \/ q.ptr_location = LocTransient) /\ ~is_word_type ann)`
    (DISJ_CASES_THEN2 assume_tac
      (DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac assume_tac)))))
  >- (Cases_on `vv` >- simp[] >>
      qpat_assum `vv_post H0 _ _ _ _ _ _ _ _ _ _ _ _ a`
        (mp_tac o REWRITE_RULE[vv_post_def]) >>
      rename1 `vv_holds _ _ _ _ (LocatedValue ann q) _ _` >>
      Cases_on `q.ptr_location` >> simp[vv_holds_def] >>
      metis_tac[is_bytestring_word_type])
  >- suspend "identity"
  >- suspend "code"
  >> suspend "slot"
QED

Resume create_blueprint_raw_unwrap_store_entry[identity]:
  drule_all ctor_unwrap_identity_arrival >>
  disch_then (qspecl_then [`explicit`,`PG`] (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qpat_x_assum `?v0. read_result cx pv ee = (INL v0,ee) /\ _`
    (qx_choose_then `v0` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `v0 = BytesV bytes` by fs[] >> pop_assum SUBST_ALL_TAC >>
  qexistsl_tac [`a`,`Ga`,`ta`] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]
QED

Resume create_blueprint_raw_unwrap_store_entry[code]:
  rename1 `vv = LocatedValue ann q` >>
  `!x. q.ptr_operand = Var x ==> not_fresh_at sm x` by fs[vv_operand_def] >>
  Cases_on `ce.ce_is_ctor`
  >- (Q.SUBGOAL_THEN
       `?val. read_result cx pv ee = (INL val,ee) /\
        !w. eval_operand q.ptr_operand a = SOME w ==>
          w2n w + type_memory_size rty <= lo /\
          (!mem. mem_agree_outside ta.t_mem a.vs_memory mem ==>
            val_in_memory rty val (w2n w) mem)` assume_tac
      >- (qexists_tac `BytesV bytes` >> fs[vv_location_def,vv_operand_def]) >>
      qpat_x_assum `vv = LocatedValue ann q` SUBST_ALL_TAC >>
      drule_all ctor_unwrap_ctor_code_arrival >>
      disch_then (qspecl_then [`explicit`,`PG`]
        (qx_choosel_then [`v0`,`z`,`Gz`,`tz`] (MAP_EVERY assume_tac o CONJUNCTS))) >>
      `v0 = BytesV bytes` by fs[] >> pop_assum SUBST_ALL_TAC >>
      qexistsl_tac [`z`,`Gz`,`tz`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule_all ctor_unwrap_runtime_code_arrival >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`v0`,`z`,`Gz`,`tz`] (MAP_EVERY assume_tac o CONJUNCTS))) >>
  `v0 = BytesV bytes` by fs[] >> pop_assum SUBST_ALL_TAC >>
  qexistsl_tac [`z`,`Gz`,`tz`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume create_blueprint_raw_unwrap_store_entry[slot]:
  rename1 `vv = LocatedValue ann q` >>
  `!x. q.ptr_operand = Var x ==> not_fresh_at sm x` by fs[vv_operand_def] >>
  qpat_x_assum `vv = LocatedValue ann q` SUBST_ALL_TAC >>
  drule_all ctor_unwrap_slot_arrival >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`v0`,`z`,`Gz`,`tz`] (MAP_EVERY assume_tac o CONJUNCTS))) >>
  `v0 = BytesV bytes` by fs[] >> pop_assum SUBST_ALL_TAC >>
  qexistsl_tac [`z`,`Gz`,`tz`] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]
QED

Resume create_blueprint_raw_unwrap_store_entry[physical]:
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H0` (drule_then strip_assume_tac)) >>
  drule_all ctor_materialize_unwrap_physical >>
  disch_then (CONJUNCTS_THEN2 (qx_choosel_then [`tv0`,`sw`] (MAP_EVERY assume_tac o CONJUNCTS)) assume_tac) >>
  `tv0 = tv` by fs[] >> pop_assum SUBST_ALL_TAC >>
  qpat_x_assum `!p w aid b n. not_fresh_at mid p /\ _ ==> _` drule_all >>
  strip_tac >>
  `stmt_state_rel H0 ctx func ce cx ee a` by fs[vv_post_def] >>
  `stmt_state_rel H0 ctx func ce cx ee z /\ wb_frame ce es ee sa s0 z /\
     (~expr_has_effect e ==> pure_frame ce func es sa s0 z)` by
    (qpat_assum `expr_post H0 _ _ _ _ _ _ _ _ _ _ _ _ z`
       (STRIP_ASSUME_TAC o REWRITE_RULE[expr_post_def]) >>
     pure_rewrite_tac[wb_frame_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "source_span"
QED

Resume create_blueprint_raw_unwrap_store_entry[source_span]:
  `0 < val_store_size tv (BytesV bytes)` by
    (drule_all bytestring_type_value >> strip_tac >>
     gvs[val_store_size_def,value_has_type_def]) >>
  `val_store_size tv (BytesV bytes) <= type_memory_size tv` by simp[val_store_size_le] >>
  `0 < type_memory_size tv` by decide_tac >>
  qpat_assum `0 < type_memory_size tv ==> ?x. _`
    (drule_then (qx_choose_then `root` strip_assume_tac)) >>
  `lookup_var root z = SOME sw` by fs[eval_operand_def] >>
  `ptr_covers Gz tz root z (val_store_size tv (BytesV bytes))` by
    (irule ptr_covers_mono >> goal_assum (drule_at Any) >> simp[]) >>
  `w2n sw + type_memory_size tv <= z.vs_alloca_next` by decide_tac >>
  `w2n sw + val_store_size tv (BytesV bytes) <= z.vs_alloca_next` by decide_tac >>
  `!x. src = Var x ==> not_fresh_at su x` by
    (rpt strip_tac >> irule compiler_unwrap_value_var >>
     qexistsl_tac [`ce`,`src`,`mid`,`vv`] >> simp[] >>
     Cases_on `vv` >> fs[vv_operand_def] >> metis_tac[not_fresh_at_mono]) >>
  suspend "finish"
QED

(* This resume keeps frame transport separate from the source-span proof. *)
Resume create_blueprint_raw_unwrap_store_entry[finish]:
  `local_ptrs_reserved ce mid /\ local_ptrs_reserved ce su` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `local_ptrs_rel func ce ee.scopes a /\ alloca_inv z` by
    metis_tac[stmt_state_rel_local_ptrs_alloca] >>
  `!name b len. local_region ce ee.scopes z name b len ==>
     regions_disjoint (w2n dw) N b len` by
    (rpt strip_tac >>
     `local_region ce ee.scopes a name b len` by
       (drule_all local_region_wb_frame >>
        disch_then (qspecl_then [`len`,`name`,`b`] mp_tac) >> simp[]) >>
     metis_tac[]) >>
  `!name b len. local_region ce es.scopes s0 name b len ==>
     regions_disjoint (w2n dw) N b len` by
    (rpt strip_tac >>
     `local_region ce ee.scopes z name b len` by
       (irule local_region_frame_fwd >>
        qexistsl_tac [`s0`,`sa`,`es.scopes`] >> simp[] >> fs[wb_frame_def]) >>
     metis_tac[]) >>
  `w2n dw + N <= z.vs_alloca_next` by (drule_all alloca_site_registered_below >> simp[]) >>
  `return_buf_frame d ce su z` by
    (irule return_buf_frame_frame >> qexistsl_tac [`ce`,`a`,`mid`] >> simp[] >> metis_tac[]) >>
  `sa.cs_next_var <= su.cs_next_var` by decide_tac >>
  `!x. not_fresh_at sa x \/ not_fresh_at mid x ==> not_fresh_at su x` by
    metis_tac[not_fresh_at_mono] >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp z)` by
    (qpat_assum `stmt_state_rel H0 _ _ _ _ _ z`
      (mp_then Any ACCEPT_TAC bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  qexistsl_tac [`z`,`Gz`,`tz`,`root`,`sw`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (rpt strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
        (drule_then strip_assume_tac) >> fs[expr_post_def]) >>
  metis_tac[]
QED

Finalise create_blueprint_raw_unwrap_store_entry
