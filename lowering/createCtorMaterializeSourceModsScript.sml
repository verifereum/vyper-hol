(* The snapshot's destination allocation is an original-function step. *)
Theory createCtorMaterializeSourceMods
Ancestors
  createCtorMaterializeSource createExprSizeExitDefsMods
  createCtorStraightBand bodyFullAllocaFresh abiBufferAllocationCode
  exprLoweringProps exprSimAlloc fragExec fragGasOriginPtr loweringStateRelDefs
  ptrDiscipline venomState venomInst venomExecSemantics finite_map list rich_list relation words
  createCtorMaterializeAllocFrameMods createCtorMaterializePhysicalMods
  createCtorUnwrapIdentityArrivalMods createCtorUnwrapRuntimeCodeArrivalMods
  createCtorUnwrapCtorCodeArrivalMods createCtorUnwrapSlotArrivalMods
  exprOperandVar exprSimProps stateRelProj exprSimSubscriptArrayFrame
  valueEncodingTyping valueCopyBytes venomExecProps arithmetic abiEncodeMaterialize
  compileEnv loweringPosts bodyPtrDefs vyperStorageFootprint bodyFullHashKeccakFixed
  context freshWrites allocationPathGrowth allocationGrowth
  bodyFullPostsMods bodyFullShadowBodyInv
Libs horizonTypeLib

Theorem ctor_materialize_source_arrival_mods:
  compile_expr ce ty e sa = (vv,sm) /\
  compile_materialize_vv ce (lowered_value_type ce e)
    (ext_call_arg_value (lowered_value_type ce e) vv) sm = (dst,sb) /\
  expr_body_pre_mods mods ce cx env e es /\
  eval_expr cx e es = (INL pv,ee) /\ read_result cx pv ee = (INL v,ee) /\
  ~is_word_type (lowered_value_type ce e) /\
  type_memory_bytes ce (lowered_value_type ce e) + 64 < dimword (:256) /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx e es sa sm s0 ee pv vv s /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee pv vv s /\
  ptr_vv_ok cx (post_value_type ce e) pv vv ee G tn s /\
  (!t op. vv = StackValue t op ==> ptr_buf_ok ce e op G s) /\
  (!t q. vv = LocatedValue t q /\ q.ptr_location = LocMemory ==>
    ptr_buf_ok ce e q.ptr_operand G s) /\
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?val. read_result cx pv ee = (INL val,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
        eval_operand (vv_operand vv) s = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory rt val (w2n w) mem)) /\
  ghost_kept_at lo ce es sa Gi ti s0 G tn /\ return_buf_frame d ce sm s /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?buf mid su src p dw tv sw z Gz tz inst.
    dst = Var p /\ buf.buf_operand = Var p /\
    compile_alloc_buffer (type_memory_bytes ce (lowered_value_type ce e)) sm = (buf,mid) /\
    unwrap_value ce (ext_call_arg_value (lowered_value_type ce e) vv) mid = (src,su) /\
    compile_store_memory ce src (Var p) (lowered_value_type ce e)
      (lowered_value_type ce e) su = ((),sb) /\
    fn_has_code su sb func /\
    RTC (\u v. ?i. ctor_segment_fetch func u = SOME i /\
       sm.cs_next_id <= i.inst_id /\ i.inst_id < su.cs_next_id /\
       i.inst_opcode <> INVOKE /\ ctor_segment_next func u i = SOME v) s z /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gz,tz) /\
       stmt_state_rel H ctx func ce cx ee z /\
       immutable_frame_mods func ce cx ee z /\ ghost_inv_at_mods (DF H) lo d ce cx ee Gz tz z) /\
    ~z.vs_halted /\ z.vs_current_bb = su.cs_current_bb /\
    z.vs_inst_idx = LENGTH su.cs_current_insts /\
    alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next /\
    evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
    value_has_type tv v /\ val_wf tv v /\
    type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
    type_memory_size tv + 64 < dimword (:256) /\
    eval_operand src z = SOME sw /\ lookup_var p z = SOME dw /\
    (!x. src = Var x ==> not_fresh_at su x) /\ not_fresh_at su p /\
    (!mem. mem_agree_outside tz.t_mem z.vs_memory mem ==>
      val_in_memory tv v (w2n sw) mem) /\
    (0 < type_memory_size tv ==>
       w2n sw + type_memory_size tv <= z.vs_alloca_next /\
       ?x. src = Var x /\ ptr_covers Gz tz x z (type_memory_size tv)) /\
    ptr_covers Gz tz p z (type_memory_size tv) /\
    w2n dw + type_memory_size tv <= z.vs_alloca_next /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = sm.cs_next_id /\
    FLOOKUP z.vs_allocas inst.inst_id = SOME (w2n dw,type_memory_size tv) /\
    sa.cs_next_id <= inst.inst_id /\ sa.cs_next_var <= su.cs_next_var /\
    local_ptrs_reserved ce su /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x) /\
    (!name b len. local_region ce ee.scopes z name b len ==>
       regions_disjoint (w2n dw) (type_memory_size tv) b len) /\
    (!name b len. local_region ce es.scopes s0 name b len ==>
       regions_disjoint (w2n dw) (type_memory_size tv) b len) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    wb_frame ce es ee sa s0 z /\ ghost_kept_at lo ce es sa Gi ti s0 Gz tz /\
    (~expr_has_effect e ==> pure_frame ce func es sa s0 z)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by fs[storage_trace_domain_def,Abbr `H0`] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `H0` (drule_then strip_assume_tac)) >>
  drule materialize_compile_trace >>
  disch_then (qx_choosel_then [`buf`,`mid`,`src`,`su`] strip_assume_tac) >>
  drule_all ctor_materialize_unwrap_retag_mods >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (qx_choose_then `rty` strip_assume_tac))) >>
  `ci_mono sm mid /\ ci_mono mid su /\ ci_mono su sb` by
    metis_tac[ci_mono_compile_alloc_buffer,ci_mono_unwrap_value,
              ci_mono_compile_store_memory,pairTheory.SND] >>
  `fn_has_code sm mid func /\ fn_has_code mid su func /\ fn_has_code su sb func` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans,fn_has_code_split]) >>
  `stmt_state_rel H0 ctx func ce cx ee s` by fs[vv_post_mods_def] >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp s)` by
    (drule stmt_state_rel_allocas_below_fmp >> simp[]) >>
  `type_memory_bytes ce (lowered_value_type ce e) < dimword (:256)` by decide_tac >>
  drule_all (horizonTypeLib.at_horizon alloc_buffer_origin_ptr_path_with_raw_endpoint) >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`]
    (qx_choosel_then [`p`,`dw`,`a`,`Ga`,`ta`,`r`] (MAP_EVERY assume_tac o CONJUNCTS))) >>
  suspend "allocation"
QED

Resume ctor_materialize_source_arrival_mods[allocation]:
  `allocation_growth s a` by
    (qpat_assum `a = r with vs_inst_idx := _` SUBST1_TAC >>
     simp[allocation_growth_index] >> drule run_inst_seq_allocation_growth >> simp[]) >>
  `!aid b sz. FLOOKUP a.vs_allocas aid = SOME (b,sz) /\
      FLOOKUP s.vs_allocas aid = NONE ==> s.vs_alloca_next <= b` by
    (drule allocation_growth_new >> simp[]) >>
  drule compile_alloc_buffer_code >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts sm mid) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_assum `fn_has_code sm mid func` (strip_assume_tac o REWRITE_RULE[fn_has_code_def]) >>
     qexists_tac `bb` >> gvs[IS_PREFIX_APPEND] >> simp[DROP_APPEND]) >>
  `LENGTH mid.cs_current_insts = s.vs_inst_idx + LENGTH (emitted_insts sm mid)` by simp[] >>
  `RTC (\u v. ?i. ctor_segment_fetch func u = SOME i /\
        sm.cs_next_id <= i.inst_id /\ i.inst_id < mid.cs_next_id /\
        i.inst_opcode <> INVOKE /\ ctor_segment_next func u i = SOME v) s a` by
    (qpat_assum `a = r with vs_inst_idx := _` SUBST1_TAC >>
     qpat_assum `LENGTH mid.cs_current_insts = _` SUBST1_TAC >>
     irule ctor_straight_band_run >> reverse (rpt conj_tac)
     >- (qexists_tac `bb` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     simp[mk_inst_def,is_terminator_def]) >>
  `val_wf rty v` by metis_tac[value_has_type_val_wf] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ ghost_inv_at_mods _ _ _ _ _ _ G tn s`
    (mp_then Any (drule_at_then (Pat `compile_alloc_buffer _ _ = _`) drule_all)
      (horizonTypeLib.at_horizon ctor_materialize_alloc_vv_frame_mods)) >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `Ga = step_prov _ _ _ r` kall_tac >>
  qpat_x_assum `ta = step_taint _ _ r _` kall_tac >>
  qpat_x_assum `a = r with vs_inst_idx := _` kall_tac >>
  qpat_x_assum `eval_operand (vv_operand vv) a = eval_operand (vv_operand vv) s` kall_tac >>
  suspend "unwrap"
QED

Resume ctor_materialize_source_arrival_mods[unwrap]:
  `sm.cs_next_var <= mid.cs_next_var /\ sm.cs_next_id < mid.cs_next_id /\
    sm.cs_next_id <= mid.cs_next_id` by
    (drule compile_alloc_buffer_code >> simp[]) >>
  `mid.cs_next_var <= su.cs_next_var /\ mid.cs_next_id <= su.cs_next_id` by fs[ci_mono_def] >>
  `vv_post_mods H0 ctx func ce cx e es sa sm s0 ee pv vv a` by simp[] >>
  `!bb. lookup_block su.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> drule lookup_block_MEM >> simp[]) >>
  `?z Gz tz.
      RTC (\u v. ?i. ctor_segment_fetch func u = SOME i /\
         mid.cs_next_id <= i.inst_id /\ i.inst_id < su.cs_next_id /\
         i.inst_opcode <> INVOKE /\ ctor_segment_next func u i = SOME v) a z /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (a,Ga,ta) [] (OK z,Gz,tz) /\
        expr_post_mods H ctx func ce cx e es sa su s0 ee v src z /\
        ghost_inv_at_mods (DF H) lo d ce cx ee Gz tz z) /\
      ~z.vs_halted /\ z.vs_current_bb = su.cs_current_bb /\
      z.vs_inst_idx = LENGTH su.cs_current_insts /\ alloca_history func z /\
      a.vs_alloca_next <= z.vs_alloca_next /\
      ptr_val_ok cx (post_value_type ce e) v src Gz tz z /\
      ptr_buf_ok ce e src Gz z /\
      (!rt w. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
          eval_operand src z = SOME w ==>
          type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
      ghost_kept_at lo ce es sa Gi ti s0 Gz tz /\
      wb_frame ce ee ee mid a z /\ ghost_kept_at lo ce ee mid Ga ta a Gz tz` by suspend "location" >>
  suspend "physical"
QED

Resume ctor_materialize_source_arrival_mods[location]:
  Q.SUBGOAL_THEN
    `((?ann op. vv = StackValue ann op) \/
      (?ann q. vv = LocatedValue ann q /\ q.ptr_location = LocMemory /\ ~is_word_type ann)) \/
     (?ann q. vv = LocatedValue ann q /\ q.ptr_location = LocCode /\ ~is_word_type ann) \/
     (?ann q. vv = LocatedValue ann q /\
        (q.ptr_location = LocStorage \/ q.ptr_location = LocTransient) /\ ~is_word_type ann)`
    (DISJ_CASES_THEN2 assume_tac
      (DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac assume_tac)))))
  >- (Cases_on `vv` >- simp[] >>
      qpat_assum `vv_post_mods H0 _ _ _ _ _ _ _ _ _ _ _ _ a`
        (strip_assume_tac o REWRITE_RULE[vv_post_mods_def]) >>
      rename1 `vv_holds_mods _ _ _ _ (LocatedValue ann q) _ _` >>
      qpat_x_assum `vv_holds_mods _ _ _ _ (LocatedValue ann q) _ _` mp_tac >>
      Cases_on `q.ptr_location` >> simp[vv_holds_mods_def,vv_holds_def] >>
      metis_tac[is_bytestring_word_type])
  >- suspend "identity"
  >- suspend "code"
  >> suspend "slot"
QED

Resume ctor_materialize_source_arrival_mods[identity]:
  drule_all ctor_unwrap_identity_arrival_mods >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 assume_tac (qx_choose_then `v0` strip_assume_tac))))) >>
  `v0 = v` by fs[] >> pop_assum SUBST_ALL_TAC >>
  qexistsl_tac [`a`,`Ga`,`ta`] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]
QED

Resume ctor_materialize_source_arrival_mods[code]:
  rename1 `vv = LocatedValue ann q` >>
  `!x. q.ptr_operand = Var x ==> not_fresh_at sm x` by fs[vv_operand_def] >>
  Cases_on `ce.ce_is_ctor`
  >- suspend "ctor_code"
  >> suspend "runtime_code"
QED

Resume ctor_materialize_source_arrival_mods[ctor_code]:
  `?val. read_result cx pv ee = (INL val,ee) /\
      !w. eval_operand q.ptr_operand a = SOME w ==>
        w2n w + type_memory_size rty <= lo /\
        (!mem. mem_agree_outside ta.t_mem a.vs_memory mem ==>
           val_in_memory rty val (w2n w) mem)` by
    (`vv_location vv = SOME LocCode` by simp[vv_location_def] >>
     qpat_assum `ce.ce_is_ctor /\ vv_location vv = _ ==> ?val. _ /\ !rt w. _ ==>
                   _ /\ (!mem. mem_agree_outside ta.t_mem _ mem ==> _)`
       (drule_all_then (qx_choose_then `v0` strip_assume_tac)) >>
     qexists_tac `v0` >> conj_tac >- first_assum ACCEPT_TAC >>
     gen_tac >> strip_tac >>
     `eval_operand (vv_operand vv) a = SOME w` by simp[vv_operand_def] >>
     qpat_assum `!rt w. _ /\ eval_operand (vv_operand vv) a = SOME w ==> _`
       (drule_all_then ACCEPT_TAC)) >>
  qpat_x_assum `vv = LocatedValue ann q` SUBST_ALL_TAC >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ ghost_inv_at_mods _ _ _ _ _ _ Ga ta a`
    (mp_then Any mp_tac ctor_unwrap_ctor_code_arrival_mods) >>
  disch_then (fn th => qpat_assum `unwrap_value ce (LocatedValue ann q) mid = _`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `ghost_kept_at lo ce es sa Gi ti s0 Ga ta`
    (mp_then Any mp_tac th)) >>
  disch_then (drule_at_then (Pat `compile_expr _ _ _ _ = _`) mp_tac) >>
  disch_then (drule_at_then (Pat `evaluate_type _ _ = SOME _`) mp_tac) >>
  disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[])) >>
  disch_then (qx_choosel_then [`v0`,`z`,`Gz`,`tz`] (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `v0 = v` by fs[] >> pop_assum SUBST_ALL_TAC >>
  qexistsl_tac [`z`,`Gz`,`tz`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume ctor_materialize_source_arrival_mods[runtime_code]:
  drule_all ctor_unwrap_runtime_code_arrival_mods >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`v0`,`z`,`Gz`,`tz`] (MAP_EVERY assume_tac o CONJUNCTS))) >>
  `v0 = v` by fs[] >> pop_assum SUBST_ALL_TAC >>
  qexistsl_tac [`z`,`Gz`,`tz`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume ctor_materialize_source_arrival_mods[slot]:
  rename1 `vv = LocatedValue ann q` >>
  `!x. q.ptr_operand = Var x ==> not_fresh_at sm x` by fs[vv_operand_def] >>
  qpat_x_assum `vv = LocatedValue ann q` SUBST_ALL_TAC >>
  drule_all ctor_unwrap_slot_arrival_mods >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`v0`,`z`,`Gz`,`tz`] (MAP_EVERY assume_tac o CONJUNCTS))) >>
  `v0 = v` by fs[] >> pop_assum SUBST_ALL_TAC >>
  qexistsl_tac [`z`,`Gz`,`tz`] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]
QED

Resume ctor_materialize_source_arrival_mods[physical]:
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H0` (drule_then strip_assume_tac)) >>
  drule_at_then (Pat `expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`) drule_all
    ctor_materialize_unwrap_physical_mods >>
  disch_then (CONJUNCTS_THEN2 (qx_choosel_then [`tv`,`sw`] (MAP_EVERY assume_tac o CONJUNCTS)) assume_tac) >>
  qpat_x_assum `!p w aid b k. not_fresh_at mid p /\ _ ==> _` drule_all >>
  strip_tac >>
  `stmt_state_rel H0 ctx func ce cx ee a` by fs[vv_post_mods_def] >>
  `stmt_state_rel H0 ctx func ce cx ee z /\ wb_frame ce es ee sa s0 z /\
     (~expr_has_effect e ==> pure_frame ce func es sa s0 z)` by
    (qpat_assum `expr_post_mods H0 _ _ _ _ _ _ _ _ _ _ _ _ z`
       (strip_assume_tac o REWRITE_RULE[expr_post_mods_def,expr_post_def]) >>
     pure_rewrite_tac[wb_frame_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!name b len. local_region ce ee.scopes z name b len ==>
       regions_disjoint (w2n dw) (type_memory_size tv) b len` by suspend "locals_current" >>
  `!name b len. local_region ce es.scopes s0 name b len ==>
       regions_disjoint (w2n dw) (type_memory_size tv) b len` by suspend "locals_original" >>
  suspend "output"
QED

Resume ctor_materialize_source_arrival_mods[locals_current]:
  `local_ptrs_rel func ce ee.scopes a` by
    (qpat_assum `stmt_state_rel H0 _ _ _ _ _ a`
       (mp_then Any (assume_tac o CONJUNCT1) stmt_state_rel_local_ptrs_alloca) >> simp[]) >>
  `!name b len. local_region ce ee.scopes z name b len <=>
                local_region ce ee.scopes a name b len` by
    (rpt gen_tac >> irule local_region_wb_frame >>
     conj_tac >- (qexists_tac `func` >> first_assum ACCEPT_TAC) >>
     qexistsl_tac [`ee`,`mid`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  `local_region ce ee.scopes a name b len` by
    (qpat_assum `!name b len. local_region ce ee.scopes z name b len <=> _`
       (qspecl_then [`name`,`b`,`len`] (irule o fst o EQ_IMP_RULE)) >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `!name b len. local_region ce ee.scopes a name b len ==> _`
    (drule_then mp_tac) >> simp[]
QED

Resume ctor_materialize_source_arrival_mods[locals_original]:
  rpt strip_tac >>
  `local_region ce ee.scopes z name b len` by
    (irule local_region_frame_fwd >>
     qexistsl_tac [`s0`,`sa`,`es.scopes`] >> simp[] >>
     fs[wb_frame_def]) >>
  qpat_assum `!name b len. local_region ce ee.scopes z name b len ==> _`
    (drule_then ACCEPT_TAC)
QED

Resume ctor_materialize_source_arrival_mods[output]:
  `!x. src = Var x ==> not_fresh_at su x` by
    (rpt strip_tac >> irule compiler_unwrap_value_var >>
     qexistsl_tac [`ce`,`src`,`mid`,`vv`] >> simp[] >>
     Cases_on `vv` >> fs[vv_operand_def] >>
     metis_tac[not_fresh_at_mono]) >>
  `sa.cs_next_var <= su.cs_next_var /\ s.vs_alloca_next <= z.vs_alloca_next` by decide_tac >>
  `local_ptrs_reserved ce su` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `mid` >> simp[]) >>
  `!x. not_fresh_at sa x \/ not_fresh_at mid x ==> not_fresh_at su x` by
    metis_tac[not_fresh_at_mono] >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp z)` by
    (qpat_assum `stmt_state_rel H0 _ _ _ _ _ z`
      (mp_then Any ACCEPT_TAC stmt_state_rel_allocas_below_fmp)) >>
  `ptr_covers Gz tz p z (type_memory_size tv)` by
    (qpat_assum `type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv`
       (once_rewrite_tac o single o SYM) >> first_assum ACCEPT_TAC) >>
  `RTC (\u v. ?i. ctor_segment_fetch func u = SOME i /\
       sm.cs_next_id <= i.inst_id /\ i.inst_id < su.cs_next_id /\
       i.inst_opcode <> INVOKE /\ ctor_segment_next func u i = SOME v) s z` by suspend "band" >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gz,tz) /\
       stmt_state_rel H ctx func ce cx ee z /\ immutable_frame_mods func ce cx ee z /\
       ghost_inv_at_mods (DF H) lo d ce cx ee Gz tz z` by suspend "horizon" >>
  suspend "package"
QED

Resume ctor_materialize_source_arrival_mods[package]:
  drule_all buffer_alloc_code >> strip_tac >>
  qabbrev_tac `ai = mk_inst sm.cs_next_id ALLOCA
    [Lit (n2w (type_memory_bytes ce (lowered_value_type ce e)))]
    [STRING #"%" (toString sm.cs_next_var)]` >>
  `MEM ai (fn_insts func)` by simp[Abbr `ai`] >>
  `ai.inst_opcode = ALLOCA /\ ai.inst_id = sm.cs_next_id` by simp[Abbr `ai`,mk_inst_def] >>
  `w2n dw + type_memory_size tv <= z.vs_alloca_next` by decide_tac >>
  `dst = Var p` by
    (qpat_assum `buf.buf_operand = Var p` (once_rewrite_tac o single o SYM) >>
     first_assum ACCEPT_TAC) >>
  qexistsl_tac [`buf`,`mid`,`su`,`src`,`p`,`dw`,`tv`,`sw`,`z`,`Gz`,`tz`,`ai`] >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]) >>
  qpat_assum `buf.buf_operand = Var p` (once_rewrite_tac o single o SYM) >>
  first_assum ACCEPT_TAC
QED

Resume ctor_materialize_source_arrival_mods[band]:
  irule RTC_TRANS >> qexists_tac `a` >> conj_tac
  >- (irule RTC_MONOTONE >> goal_assum (drule_at Any) >>
      simp[] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  irule RTC_MONOTONE >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[LESS_EQ_TRANS]
QED

Resume ctor_materialize_source_arrival_mods[horizon]:
  rpt gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  conj_tac
  >- (qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] (OK a,Ga,ta)`
        (qspec_then `DF H` (mp_then Any mp_tac gas_origin_ptr_path_append)) >>
      simp[] >> disch_then irule >> first_assum ACCEPT_TAC) >>
  qpat_assum `expr_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ z`
    (strip_assume_tac o REWRITE_RULE[expr_post_mods_def,expr_post_def]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise ctor_materialize_source_arrival_mods
