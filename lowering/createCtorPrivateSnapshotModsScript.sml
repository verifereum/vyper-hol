(* The allocating snapshot and the supplied traversal have the same first
   arrival. Keep the ghosts constructed by allocation, unwrap, and store. *)
Theory createCtorPrivateSnapshotMods
Ancestors
  createCtorPrivateSnapshot createExprSizeExitDefsMods
  createCtorMaterializeSourceMods createCtorMaterializeStoreMods bodyFullMaterializedOperandEndpointProps
  createCtorSegmentArrival bodyFullExtCallPosList bodyFullExtCallPosAggregate
  abiEncodeArgsCase exprSimSource exprSimProps exprBodyPreProps exprOperandVar
  exprLowering exprLoweringProps exprSimHypsDefs exprReasonOperand
  exprNamedConstResult exprSimConcatResult abiBuiltinDispatchCorrect
  createCtorSnapshotTypingMods stmtLoweringMono bodyMemoryDefs
  loweringPosts loweringStateRelDefs bodyPtrDefs stateRelProj
  exprSimWordArgs wordArgsPtr bodyFullPathHistory fragGasOriginPtrLoop fragExec
  context compileEnv vyperState vyperStorageTrace vyperStorageFootprint valueEncodingProps
  exprSimHyps aggregateEvaluatedLayout abiBufferAllocationCode
  venomState venomInst relation arithmetic list finite_map words freshWrites
Libs horizonTypeLib

Theorem extcall_operand_snapshot_type_mods[local]:
  expr_body_pre_mods mods cenv cx env e es /\
  compile_expr cenv (expr_type e) e sa = (vv,sm) ==>
  vv_type (ext_call_arg_value (lowered_value_type cenv e) vv) =
    lowered_value_type cenv e
Proof
  strip_tac >> namedCases_on `vv` ["tag op", "tag p"] >>
  simp[ext_call_arg_value_def, vv_type_def] >>
  Cases_on `lowered_value_type cenv e = expr_type e`
  >- (`well_typed_expr env e /\
       (!id t. FLOOKUP env.var_types id = SOME t ==>
         ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz))` by
        (drule expr_body_pre_mods_inv >>
         fs[expr_sim_inv_mods_def] >>
         metis_tac[expr_body_pre_mods_well_typed]) >>
      `reason_uniform_shape compile_expr cenv (expr_type e) e` by
        metis_tac[compile_expr_reason_uniform] >>
      qpat_x_assum `reason_uniform_shape _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [reason_uniform_shape_def]) >>
      qpat_x_assum `!sa vv sb. _ ==> reason_result_shape _ _ _`
        (drule_then assume_tac) >>
      gvs[reason_result_shape_def]) >>
  `(?n st. e = Literal (BaseT (StringT n)) (StringL st)) \/
   (?n bs. e = Literal (BaseT (BytesT (Dynamic n))) (BytesL bs)) \/
   (?n bs. e = Literal (BaseT (BytesT (Dynamic n))) (HexBytesL bs)) \/
   (?ann n args. e = Builtin ann (Concat n) args) \/
   (?ann en method tys args. e = TypeBuiltin ann (AbiEncode en method) tys args) \/
   (?ann fid args dr. e = Call ann (IntCall fid) args dr)` by
    (qpat_x_assum `lowered_value_type cenv e <> expr_type e` mp_tac >>
     Cases_on `e` >> simp[lowered_value_type_def]
     >~ [`Literal ty lit`]
     >- (Cases_on `ty` >> simp[lowered_value_type_def] >>
         rename1 `BaseT bt` >> Cases_on `bt` >>
         Cases_on `lit` >> simp[lowered_value_type_def] >>
         rename1 `BytesT bound` >> Cases_on `bound` >>
         simp[lowered_value_type_def])
     >~ [`Builtin ann bt args`]
     >- (Cases_on `bt` >> simp[lowered_value_type_def] >>
         Cases_on `is_word_type ann`
         >- (`is_word_type (expr_type (Builtin ann NamedConst args))` by
               simp[vyperASTTheory.expr_type_def] >>
             irule vyperTypeArgFitsTheory.arg_type_fits_prim_word >>
             simp[membership_element_word_boundary] >>
             drule_all ctor_snapshot_word_types_mods >> simp[]) >>
         drule_all named_const_nonword_compile_shape >> simp[])
     >~ [`TypeBuiltin ann tb tys args`]
     >- (Cases_on `tb` >> simp[lowered_value_type_def]) >>
     rename1 `Call ann tgt args dr` >> Cases_on `tgt` >>
     simp[lowered_value_type_def]) >>
  pop_assum mp_tac >> strip_tac
  >- (gvs[Once compile_expr_raw_def, compile_expr_body_def,
          vyperASTTheory.expr_type_def,
          compile_literal_vv_def, comp_bind_def, comp_return_def] >>
      pairarg_tac >> gvs[])
  >- (gvs[Once compile_expr_raw_def, compile_expr_body_def,
          vyperASTTheory.expr_type_def,
          compile_literal_vv_def, comp_bind_def, comp_return_def] >>
      pairarg_tac >> gvs[])
  >- (gvs[Once compile_expr_raw_def, compile_expr_body_def,
          vyperASTTheory.expr_type_def,
          compile_literal_vv_def, comp_bind_def, comp_return_def] >>
      pairarg_tac >> gvs[])
  >- (gvs[] >> drule concat_compile_shape >> simp[])
  >- (qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
      simp[Once compile_expr_component_eq] >>
      simp[Once compile_expr_raw_def, compile_type_builtin_dispatch_body_def] >>
      rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
      rpt (pairarg_tac >> gvs[]) >>
      Cases_on `LENGTH args = 1 /\ ~en` >>
      Cases_on `is_word_type (expr_type (HD args))` >>
      gvs[] >> drule as_ptr_val_result >> simp[])
  >> (gvs[exprSimSendTheory.compile_expr_call] >>
      drule reason_compile_call >> simp[reason_result_shape_def])
QED

Theorem ctor_private_snapshot_actual_mods:
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  compile_snapshot_vv ce T (ext_call_arg_value (lowered_value_type ce e) vv) sm = (saved,sb) /\
  expr_body_pre_mods mods ce cx env e es /\ ~is_word_type (lowered_value_type ce e) /\
  eval_expr cx e (es with gas_obs := gs) = (INL raw,ee) /\
  read_result cx raw ee = (INL v,ee) /\
  local_ptrs_reserved ce sa /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx e es sa sm s0 ee raw vv s /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee raw vv s /\
  ptr_vv_ok cx (post_value_type ce e) raw vv ee G tn s /\
  (!tag op. vv = StackValue tag op ==> ptr_buf_ok ce e op G s) /\
  (!tag q. vv = LocatedValue tag q /\ q.ptr_location = LocMemory ==>
    ptr_buf_ok ce e q.ptr_operand G s) /\
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?val. read_result cx raw ee = (INL val,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
        eval_operand (vv_operand vv) s = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory rt val (w2n w) mem)) /\
  ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\ return_buf_frame d ce sa s0 /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  RTC (\u r. (u.vs_current_bb,u.vs_inst_idx) <>
                (sb.cs_current_bb,LENGTH sb.cs_current_insts) /\
       ?i ms. ctor_segment_fetch func u = SOME i /\
              sm.cs_next_id <= i.inst_id /\ i.inst_id < sb.cs_next_id /\
              gas_origin_edge F explicit ctx func u ms (OK r)) s t /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ctor_segment_fetch func t = SOME last /\ last.inst_opcode <> PHI /\
  sb.cs_next_id <= last.inst_id ==>
  ?p w tv Gt tt.
    saved = LocatedValue (lowered_value_type ce e) (mk_ptr (Var p) LocMemory) /\
    evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
    value_has_type tv v /\ val_wf tv v /\
    lookup_var p t = SOME w /\ not_fresh_at sb p /\
    FLOOKUP t.vs_allocas sm.cs_next_id = SOME (w2n w,type_memory_size tv) /\
    sm.cs_next_id < sb.cs_next_id /\ w2n w + type_memory_size tv <= t.vs_alloca_next /\
    val_in_memory tv v (w2n w) t.vs_memory /\
    ptr_val_ok cx (lowered_value_type ce e) v (Var p) Gt tt t /\
    ptr_buf_ok ce e (Var p) Gt t /\
    (!n b len. local_region ce ee.scopes t n b len ==>
      regions_disjoint (w2n w) (type_memory_size tv) b len) /\
    !H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gt,tt) /\
      !xs. extcall_positional_post_mods mods T DF lo d ctx func ce cx env xs [e] [saved]
        sa sb es s0 G0 tn0 H (INL [v]) ee Gt tt t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qabbrev_tac `input = ext_call_arg_value (lowered_value_type ce e) vv` >>
  `vv_type input = lowered_value_type ce e` by
    (simp[Abbr `input`] >> drule_all extcall_operand_snapshot_type_mods >> simp[]) >>
  `?dst. compile_materialize_vv ce (lowered_value_type ce e) input sm = (dst,sb) /\
    saved = LocatedValue (lowered_value_type ce e) (mk_ptr dst LocMemory)` by
    (qpat_x_assum `compile_snapshot_vv ce T input sm = _` mp_tac >>
     Cases_on `compile_materialize_vv ce (lowered_value_type ce e) input sm` >>
     simp[compile_snapshot_vv_def,comp_bind_def,comp_return_def]) >>
  `ci_mono sa sm /\ ci_mono sm sb` by
    metis_tac[ci_mono_compile_expr_sa,ci_mono_compile_snapshot_vv,pairTheory.SND] >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by
    fs[storage_trace_domain_def,Abbr `H0`] >>
  `stmt_state_rel H0 ctx func ce cx ee s /\
   (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x s = SOME w)` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
     fs[bodyFullPostsModsTheory.vv_post_mods_def]) >>
  `expr_body_pre_mods mods ce cx env e (es with gas_obs := gs)` by simp[] >>
  `vyperState$bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee)` by
    simp[bind_def] >>
  `~is_word_type (expr_type e)` by
    (`is_word_type (lowered_value_type ce e) <=> is_word_type (expr_type e)` by
       metis_tac[ctor_snapshot_word_types_mods] >>
     metis_tac[]) >>
  drule_all (REWRITE_RULE [ETA_AX] abi_args_success_ready) >> simp[] >> strip_tac >>
  `local_ptrs_reserved ce sm /\ return_buf_frame d ce sm s` by
    (fs[ci_mono_def] >> conj_tac
     >- (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[])
     >> irule return_buf_frame_frame >> qexistsl_tac [`ce`,`s0`,`sa`] >> simp[]) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    metis_tac[cj 1 compiler_compile_var] >>
  suspend "source"
QED

Resume ctor_private_snapshot_actual_mods[source]:
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx e (es with gas_obs := gs) sa sm s0 ee raw vv s /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s` by
    simp[vv_post_initial_gas] >>
  `ghost_kept_at lo ce (es with gas_obs := gs) sa G0 tn0 s0 G tn` by
    (simp[ghost_kept_at_def] >> fs[ghost_kept_at_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    fs[ci_mono_def] >>
  `type_memory_bytes ce (lowered_value_type ce e) + 64 < dimword (:256)` by simp[] >>
  `MAP FDOM (es with gas_obs := gs).scopes = MAP FDOM ee.scopes` by simp[] >>
  qunabbrev_tac `input` >>
  drule_all ctor_materialize_source_arrival_mods >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`buf`,`mid`,`su`,`src`,`p`,`dw`,`rt`,`sw`,`z`,`Gz`,`tz`,`inst`]
      (MAP_EVERY assume_tac o CONJUNCTS))) >>
  suspend "store"
QED

Resume ctor_private_snapshot_actual_mods[store]:
  qabbrev_tac `HP = \H. valid_horizon cx st0 H ee.storage_trace` >>
  qabbrev_tac `n = if is_bytestring_type (lowered_value_type ce e) then val_store_size rt v
                    else type_memory_size rt` >>
  `HP H0` by simp[Abbr `HP`] >>
  `!H. HP H ==> stmt_state_rel H ctx func ce cx ee z /\
                ghost_inv_at_mods (DF H) lo d ce cx ee Gz tz z` by simp[Abbr `HP`] >>
  `(0 < n ==> w2n sw + n <= z.vs_alloca_next /\
              ?x. src = Var x /\ ptr_covers Gz tz x z n)` by suspend "coverage" >>
  `!name b len. local_region ce ee.scopes z name b len ==>
      w2n dw + type_memory_size rt <= b \/ b + len <= w2n dw` by
    (qpat_assum `!name b len. local_region ce ee.scopes z name b len ==> regions_disjoint _ _ _ _`
       (ACCEPT_TAC o REWRITE_RULE [loweringStateRelDefsTheory.regions_disjoint_def])) >>
  `!name b len. local_region ce es.scopes s0 name b len ==>
      w2n dw + type_memory_size rt <= b \/ b + len <= w2n dw` by
    (qpat_assum `!name b len. local_region ce (es with gas_obs := gs).scopes s0 name b len ==> _`
       (mp_tac o REWRITE_RULE [loweringStateRelDefsTheory.regions_disjoint_def]) >> simp[]) >>
  `wb_frame ce es ee sa s0 z /\ ghost_kept_at lo ce es sa G0 tn0 s0 Gz tz /\
   (~expr_has_effect e ==> pure_frame ce func es sa s0 z)` by suspend "gas_frame" >>
  qunabbrev_tac `n` >>
  drule_all (SIMP_RULE bool_ss [] (Q.INST
    [`n` |-> `if is_bytestring_type (lowered_value_type ce e) then val_store_size tv v
              else type_memory_size tv`] ctor_materialize_store_arrival_mods)) >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`u`,`Gu`,`tu`] (MAP_EVERY assume_tac o CONJUNCTS))) >>
  suspend "arrival"
QED

Resume ctor_private_snapshot_actual_mods[coverage]:
  `n <= type_memory_size rt` by (simp[Abbr `n`] >> rw[] >> simp[val_store_size_le]) >>
  strip_tac >>
  `0 < type_memory_size rt` by decide_tac >>
  qpat_assum `0 < type_memory_size rt ==> _` (drule_then strip_assume_tac) >>
  conj_tac >- decide_tac >>
  qexists_tac `x` >> simp[] >>
  fs[ptr_covers_def] >> metis_tac[LESS_EQ_TRANS,LESS_EQ_MONO_ADD_EQ]
QED

Resume ctor_private_snapshot_actual_mods[gas_frame]:
  conj_tac
  >- (qpat_assum `wb_frame ce (es with gas_obs := gs) ee sa s0 z` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> simp[wb_frame_def,locals_kept_def,popped_kept_def] >>
      metis_tac[]) >>
  conj_tac
  >- (qpat_assum `ghost_kept_at lo ce (es with gas_obs := gs) sa G0 tn0 s0 Gz tz` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> simp[ghost_kept_at_def] >> metis_tac[]) >>
  strip_tac >>
  qpat_assum `~expr_has_effect e ==> pure_frame ce func (es with gas_obs := gs) sa s0 z`
    (drule_then (ACCEPT_TAC o REWRITE_RULE [pure_frame_gas_obs]))
QED

Resume ctor_private_snapshot_actual_mods[arrival]:
  `ci_mono mid su /\ ci_mono su sb` by
    metis_tac[ci_mono_unwrap_value,ci_mono_compile_store_memory,pairTheory.SND] >>
  `sm.cs_next_id < mid.cs_next_id` by (drule compile_alloc_buffer_code >> simp[]) >>
  `sm.cs_next_id < sb.cs_next_id /\ sm.cs_next_id <= su.cs_next_id /\ su.cs_next_id <= sb.cs_next_id /\
   su.cs_next_var <= sb.cs_next_var /\ sa.cs_next_var <= sb.cs_next_var` by
    (fs[ci_mono_def] >> decide_tac) >>
  qabbrev_tac `cut = (sb.cs_current_bb,LENGTH sb.cs_current_insts)` >>
  qabbrev_tac `C = \a b. ?i. ctor_segment_fetch func a = SOME i /\
       sm.cs_next_id <= i.inst_id /\ i.inst_id < sb.cs_next_id /\
       i.inst_opcode <> INVOKE /\ ctor_segment_next func a i = SOME b` >>
  `RTC C s u` by suspend "band" >>
  `!a b. C a b ==> (a.vs_current_bb,a.vs_inst_idx) <> cut /\
        ?i. ctor_segment_fetch func a = SOME i /\
           i.inst_opcode <> INVOKE /\ ctor_segment_next func a i = SOME b` by suspend "exclude" >>
  `t = u` by suspend "compare" >>
  pop_assum SUBST_ALL_TAC >>
  suspend "pack"
QED

Resume ctor_private_snapshot_actual_mods[band]:
  irule RTC_TRANS >> qexists_tac `z` >> conj_tac
  >- (irule RTC_MONOTONE >> goal_assum (drule_at Any) >>
      simp[Abbr `C`] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  irule RTC_MONOTONE >> goal_assum (drule_at Any) >>
  simp[Abbr `C`] >> metis_tac[LESS_EQ_TRANS]
QED

Resume ctor_private_snapshot_actual_mods[exclude]:
  simp[Abbr `C`] >> rpt gen_tac >> strip_tac >> conj_tac
  >- (strip_tac >>
      `a.vs_current_bb = t.vs_current_bb /\ a.vs_inst_idx = t.vs_inst_idx` by
        fs[Abbr `cut`] >>
      `ctor_segment_fetch func a = ctor_segment_fetch func t` by
        (pure_rewrite_tac[ctor_segment_fetch_def] >> gvs[]) >>
      `i = last` by metis_tac[optionTheory.SOME_11] >> gvs[] >> decide_tac) >>
  qexists_tac `i` >> simp[]
QED

Resume ctor_private_snapshot_actual_mods[compare]:
  irule ctor_same_func_first_arrival >>
  qpat_assum `RTC (\a b. _ /\ ?i ms. _) s t` (irule_at Any) >>
  qexistsl_tac [`last`,`func`,`explicit`,`cut`,`ctx`,`C`] >>
  simp[Abbr `cut`] >> metis_tac[]
QED

Resume ctor_private_snapshot_actual_mods[pack]:
  `not_fresh_at sb p` by metis_tac[not_fresh_at_mono] >>
  `w2n dw + type_memory_size rt <= u.vs_alloca_next` by simp[] >>
  `alloca_history func u` by suspend "history" >>
  `s0.vs_alloca_next <= u.vs_alloca_next` by (simp[] >> metis_tac[LESS_EQ_TRANS]) >>
  `return_buf_frame d ce sb u` by
    (irule return_buf_frame_frame >> qexistsl_tac [`ce`,`s0`,`sa`] >>
     fs[wb_frame_def]) >>
  `!n b len. local_region ce ee.scopes u n b len ==>
    regions_disjoint (w2n dw) (type_memory_size rt) b len` by
    (rewrite_tac[loweringStateRelDefsTheory.regions_disjoint_def] >> first_assum ACCEPT_TAC) >>
  `vv_operand saved = Var p` by simp[vv_operand_def,mk_ptr_def] >>
  `val_footprint rt v <= type_memory_size rt` by simp[val_footprint_le] >>
  `wb_frame ce ee ee sb u u /\ ghost_kept_at lo ce ee sb Gu tu u Gu tu` by
    simp[wb_frame_refl,ghost_kept_at_refl] >>
  `saved = LocatedValue (lowered_value_type ce e) (mk_ptr (Var p) LocMemory) /\
    lookup_var p u = SOME dw /\
    FLOOKUP u.vs_allocas sm.cs_next_id = SOME (w2n dw,type_memory_size rt) /\
    (!n b len. local_region ce ee.scopes u n b len ==>
       w2n dw + type_memory_size rt <= b \/ b + len <= w2n dw) /\
    read_result cx (Value v) ee = (INL v,ee) /\
    vv_holds ce cx (lowered_value_type ce e) (Value v) saved ee u /\
    vv_at ce cx (lowered_value_type ce e) sb ee (Value v) saved u /\
    ptr_vv_ok cx (lowered_value_type ce e) (Value v) saved ee Gu tu u /\
    vv_store_bound cx (lowered_value_type ce e) (lowered_value_type ce e) ee (Value v) saved u /\
    ptr_buf_ok ce e (Var p) Gu u` by suspend "representation" >>
  suspend "result"
QED

Resume ctor_private_snapshot_actual_mods[history]:
  `alloca_inv z` by
    (qpat_assum `!H. HP H ==> stmt_state_rel H ctx func ce cx ee z /\ _`
       (drule_then strip_assume_tac) >> drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  irule body_full_path_alloca_history >> simp[] >>
  qpat_assum `!D. gas_origin_ptr_path _ (z,Gz,tz) [] (OK u,Gu,tu)`
    (qspec_then `DF H0` (irule_at Any)) >> simp[]
QED

Resume ctor_private_snapshot_actual_mods[representation]:
  irule materialized_operand_endpoint >>
  qpat_assum `compile_snapshot_vv _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `ptr_val_ok cx (lowered_value_type ce e) v (Var p) Gu tu u` (irule_at Any) >>
  qexistsl_tac [`rt`,`ee`,`lo`,`sb`] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> first_x_assum drule >>
      simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  metis_tac[]
QED

Resume ctor_private_snapshot_actual_mods[result]:
  qexistsl_tac [`p`,`dw`,`rt`,`Gu`,`tu`] >>
  simp[] >> conj_tac
  >- first_assum ACCEPT_TAC >>
  gen_tac >> strip_tac >> conj_tac
  >- (irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gz`,`z`,`tz`] >>
      qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> gas_origin_ptr_path _ _ _ _ _ _ _`
        (qspec_then `H` mp_tac) >> fs[Abbr `HP`]) >>
  gen_tac >>
  `storage_well_formed_on cx ee (FST H)` by
    (qpat_assum `!h. valid_horizon cx st0 h ee.storage_trace ==>
       vv_post_mods h ctx func ce cx e es sa sm s0 ee raw vv s /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- fs[Abbr `HP`]) >>
     disch_then (ACCEPT_TAC o cj 2 o REWRITE_RULE [bodyFullPostsModsTheory.vv_post_mods_def] o cj 1)) >>
  qpat_assum `!h. HP h ==> stmt_state_rel h ctx func ce cx ee u /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  simp[extcall_positional_post_mods_def,vv_location_def,vv_operand_def,mk_ptr_def,eval_operand_def] >>
  conj_tac >-
    (qexistsl_tac [`sa`,`sm`,`sb`,`vv`,`Value v`,`T`] >>
     gvs[mk_ptr_def,ci_mono_def] >> first_assum ACCEPT_TAC) >>
  fs[wb_frame_def]
QED
Finalise ctor_private_snapshot_actual_mods
