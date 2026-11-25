(* The copied raw singleton at the actual snapshot exit. *)
Theory createBlueprintRawCopyMods
Ancestors
  createBlueprintRawCopy createExprSizeExitDefsMods
  createBlueprintRawCopyLayoutMods createCtorMaterializeAllocFrameMods createBlueprintRawUnwrapMods
  createBlueprintRawBytesStoreMods createCtorMaterializeSourceMods createCtorSegmentArrival
  abiEncodeMaterialize abiBufferAllocationCode exprSimAlloc exprSimHyps
  exprLoweringProps fragExec fragGasOriginPtr loweringPosts loweringStateRelDefs
  stateRelProj bodyMemoryDefs bodyPtrDefs freshWrites ptrDiscipline
  vyperStorageFootprint valueEncodingDefs valueCopyBytes vyperTyping
  venomState venomInst finite_map relation words
  compileEnv exprLowering vyperState valueEncodingTyping bodyFullHashKeccakFixed
  createCtorStraightBand bodyFullAllocaFresh allocationPathGrowth allocationGrowth
  bodyFullPostsMods bodyFullShadowBodyInv allocLimits list rich_list exprSimHypsDefs
Libs horizonTypeLib

Theorem create_blueprint_raw_copy_at_cut_mods:
  expr_type e = BaseT (BytesT (Dynamic k)) /\
  expr_body_pre_mods mods ce cx env e es /\
  compile_expr ce (expr_type e) e sa = (vv,cm) /\
  compile_snapshot_vv ce T vv cm = (saved,cs) /\
  eval_expr cx e es = (INL pv,ee) /\
  read_result cx pv ee = (INL (BytesV bytes),ee) /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce cm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= cm.cs_next_var /\ sa.cs_next_id <= cm.cs_next_id /\
  fn_has_code cm cs func /\ fn_inst_ids_distinct func /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at cm x) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx e es sa cm s0 ee pv vv s /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee pv vv s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = cm.cs_current_bb /\
  s.vs_inst_idx = LENGTH cm.cs_current_insts /\
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
  ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\ return_buf_frame d ce cm s /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. old = Var x ==> not_fresh_at cm x) /\ eval_operand old s = SOME ow /\
  RTC R s u /\
  (!x y. R x y ==>
    (x.vs_current_bb <> cs.cs_current_bb \/ x.vs_inst_idx <> LENGTH cs.cs_current_insts) /\
    ?ms. gas_origin_edge F explicit ctx func x ms (OK y)) /\
  u.vs_current_bb = cs.cs_current_bb /\ u.vs_inst_idx = LENGTH cs.cs_current_insts /\
  ctor_segment_fetch func u = SOME next /\ next.inst_opcode = MLOAD /\
  cs.cs_next_id <= next.inst_id ==>
  ?p w Gu tnu.
    saved = LocatedValue (vv_type vv) (mk_ptr (Var p) LocMemory) /\
    lookup_var p u = SOME w /\ not_fresh_at cs p /\
    expr_val_rel cx (BaseT (BytesT (Dynamic k))) (BytesV bytes) (Var p) u /\
    eval_operand old u = SOME ow /\ (!x. old = Var x ==> not_fresh_at cs x) /\
    ~u.vs_halted /\ alloca_history func u /\ s.vs_alloca_next <= u.vs_alloca_next /\
    s0.vs_alloca_next <= u.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    return_buf_frame d ce cs u /\ wb_frame ce es ee sa s0 u /\
    ghost_kept_at lo ce es sa G0 tn0 s0 Gu tnu /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tnu) /\
      stmt_state_rel H ctx func ce cx ee u /\
      immutable_frame_mods func ce cx ee u /\ ghost_inv_at_mods (DF H) lo d ce cx ee Gu tnu u)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `bind (eval_expr cx e) (read_result cx) es = (INL (BytesV bytes),ee)` by
    simp[vyperStateTheory.bind_def] >>
  drule_all create_blueprint_raw_copy_layout_mods >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
    (qx_choosel_then [`kp`,`kq`] (map_every assume_tac o CONJUNCTS)))) >>
  `~is_word_type (vv_type vv) /\ ~is_word_type (expr_type e) /\
   is_bytestring_type (expr_type e) /\ is_bytestring_type (vv_type vv) /\
   is_bytestring_type (lowered_value_type ce e)` by simp[is_word_type_def,is_bytestring_type_def] >>
  `post_value_type ce e = expr_type e` by simp[] >>
  `val_wf (BaseTV (BytesT (Dynamic k))) (BytesV bytes)` by metis_tac[value_has_type_val_wf] >>
  `?dst. compile_materialize_vv ce (vv_type vv) vv cm = (dst,cs) /\
         saved = LocatedValue (vv_type vv) (mk_ptr dst LocMemory)` by
    (qpat_x_assum `compile_snapshot_vv _ _ _ _ = _` mp_tac >>
     qpat_x_assum `vv_type vv = _` kall_tac >>
     Cases_on `compile_materialize_vv ce (vv_type vv) vv cm` >>
     simp[compile_snapshot_vv_def,comp_bind_def,comp_return_def]) >>
  pop_assum strip_assume_tac >>
  drule materialize_compile_trace >>
  disch_then (qx_choosel_then [`buf`,`mid`,`src`,`su`] (map_every assume_tac o CONJUNCTS)) >>
  `ci_mono cm mid /\ ci_mono mid su /\ ci_mono su cs` by
    metis_tac[ci_mono_compile_alloc_buffer,ci_mono_unwrap_value,
              ci_mono_compile_store_memory,pairTheory.SND] >>
  `fn_has_code cm mid func /\ fn_has_code mid su func /\ fn_has_code su cs func` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans,fn_has_code_split]) >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by fs[storage_trace_domain_def,Abbr `H0`] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ ghost_inv_at_mods _ _ _ _ _ _ G tn s`
    (qspec_then `H0` (drule_then strip_assume_tac)) >>
  `stmt_state_rel H0 ctx func ce cx ee s` by fs[vv_post_mods_def] >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp s)` by
    (drule stmt_state_rel_allocas_below_fmp >> simp[]) >>
  `type_memory_bytes ce (vv_type vv) < dimword (:256)` by decide_tac >>
  suspend "allocate"
QED

Resume create_blueprint_raw_copy_at_cut_mods[allocate]:
  drule_all (horizonTypeLib.at_horizon alloc_buffer_origin_ptr_path_with_raw_endpoint) >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`]
    (qx_choosel_then [`p`,`dw`,`a`,`Ga`,`ta`,`r`] (map_every assume_tac o CONJUNCTS))) >>
  `allocation_growth s a` by
    (qpat_assum `a = r with vs_inst_idx := _` SUBST1_TAC >>
     simp[allocation_growth_index] >> drule run_inst_seq_allocation_growth >> simp[]) >>
  `!aid b sz. FLOOKUP a.vs_allocas aid = SOME (b,sz) /\
      FLOOKUP s.vs_allocas aid = NONE ==> s.vs_alloca_next <= b` by
    (drule allocation_growth_new >> simp[]) >>
  drule compile_alloc_buffer_code >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts cm mid) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_assum `fn_has_code cm mid func` (strip_assume_tac o REWRITE_RULE[fn_has_code_def]) >>
     qexists_tac `bb` >> gvs[rich_listTheory.IS_PREFIX_APPEND] >> simp[DROP_APPEND]) >>
  `LENGTH mid.cs_current_insts = s.vs_inst_idx + LENGTH (emitted_insts cm mid)` by simp[] >>
  `RTC (\x y. ?i. ctor_segment_fetch func x = SOME i /\
        cm.cs_next_id <= i.inst_id /\ i.inst_id < mid.cs_next_id /\
        i.inst_opcode <> INVOKE /\ ctor_segment_next func x i = SOME y) s a` by
    (qpat_assum `a = r with vs_inst_idx := _` SUBST1_TAC >>
     qpat_assum `LENGTH mid.cs_current_insts = _` SUBST1_TAC >>
     irule ctor_straight_band_run >> reverse (rpt conj_tac)
     >- (qexists_tac `bb` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     simp[mk_inst_def,is_terminator_def]) >>
  suspend "frame_alloc"
QED

Resume create_blueprint_raw_copy_at_cut_mods[frame_alloc]:
  `~is_word_type (post_value_type ce e) /\ is_bytestring_type (post_value_type ce e) /\
   evaluate_type (get_tenv cx) (post_value_type ce e) = SOME (BaseTV (BytesT (Dynamic k))) /\
   type_memory_bytes ce (post_value_type ce e) = type_memory_size (BaseTV (BytesT (Dynamic k)))` by
    (simp[is_word_type_def,is_bytestring_type_def] >>
     irule typeLayoutPropsTheory.type_memory_bytes_base_evaluated >>
     qexists_tac `get_tenv cx` >> simp[]) >>
  `type_memory_size (BaseTV (BytesT (Dynamic k))) < 2 ** 64` by
    (`type_alloc_ok ce (expr_type e)` by
       metis_tac[expr_body_pre_mods_def, alloc_limits_expr_type_alloc_ok] >>
     pop_assum mp_tac >>
     simp[type_alloc_ok_def,is_word_type_def,compileEnvTheory.type_memory_bytes_def,
          valueEncodingTheory.type_memory_size_def,vfmConstantsTheory.word_size_def]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ ghost_inv_at_mods _ _ _ _ _ _ G tn s`
    (mp_then Any (drule_at_then (Pat `compile_alloc_buffer _ _ = _`) drule_all)
      (horizonTypeLib.at_horizon ctor_materialize_alloc_vv_frame_mods)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `Ga = step_prov _ _ _ r` kall_tac >>
  qpat_x_assum `ta = step_taint _ _ r _` kall_tac >>
  qpat_x_assum `a = r with vs_inst_idx := _` kall_tac >>
  qpat_x_assum `eval_operand (vv_operand vv) a = eval_operand (vv_operand vv) s` kall_tac >>
  suspend "unwrap"
QED

Resume create_blueprint_raw_copy_at_cut_mods[unwrap]:
  `cm.cs_next_var <= mid.cs_next_var /\ cm.cs_next_id < mid.cs_next_id` by simp[] >>
  `mid.cs_next_var <= su.cs_next_var /\ mid.cs_next_id <= su.cs_next_id /\
    su.cs_next_id <= cs.cs_next_id` by fs[ci_mono_def] >>
  `!bb. lookup_block su.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0` by metis_tac[venomExecProofsTheory.lookup_block_MEM] >>
  `ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
     !w. eval_operand (vv_operand vv) a = SOME w ==>
       w2n w + type_memory_size (BaseTV (BytesT (Dynamic k))) <= lo /\
       (!mem. mem_agree_outside ta.t_mem a.vs_memory mem ==>
         val_in_memory (BaseTV (BytesT (Dynamic k))) (BytesV bytes) (w2n w) mem)` by
    (strip_tac >> qpat_assum `ce.ce_is_ctor /\ _ ==> ?val. _ /\ !rt w. _ ==> _ /\
         !mem. mem_agree_outside ta.t_mem _ mem ==> _` mp_tac >>
     (impl_tac >- simp[]) >>
     disch_then (qx_choose_then `vread` (CONJUNCTS_THEN2 mp_tac assume_tac)) >>
     simp[] >> disch_then SUBST_ALL_TAC >>
     qpat_assum `!rt w. _ ==> _ /\ !mem. mem_agree_outside ta.t_mem _ mem ==> _`
       (qspec_then `BaseTV (BytesT (Dynamic k))` mp_tac) >> simp[]) >>
  qpat_assum `compile_expr _ _ _ _ = _`
    (mp_then Any mp_tac create_blueprint_raw_unwrap_store_entry_mods) >>
  disch_then (fn th => qpat_assum `ghost_kept_at lo ce es sa G0 tn0 s0 Ga ta`
    (mp_then Any mp_tac th)) >>
  disch_then (mp_tac o Q.INST [`aid` |-> `cm.cs_next_id`,
    `N` |-> `type_memory_bytes ce (vv_type vv)`,
    `rty` |-> `BaseTV (BytesT (Dynamic k))`, `tv` |-> `BaseTV (BytesT (Dynamic kp))`] o SPEC_ALL) >>
  impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[])) >>
  disch_then (qx_choosel_then [`z`,`Gz`,`tz`,`q`,`sw`] (map_every assume_tac o CONJUNCTS)) >>
  suspend "store"
QED

Resume create_blueprint_raw_copy_at_cut_mods[store]:
  `z.vs_labels = s.vs_labels` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ (a,Ga,ta) [] _ /\ _`
       (qspec_then `H0` (drule_then strip_assume_tac)) >>
     drule gasOriginPtrLabelsTheory.gas_origin_ptr_path_preserves_labels >> strip_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] _`
       (qspec_then `DF H0` (mp_then Any assume_tac gasOriginPtrLabelsTheory.gas_origin_ptr_path_preserves_labels)) >>
     simp[]) >>
  `eval_operand old z = SOME ow` by
    (`eval_operand old z = eval_operand old s` suffices_by simp[] >>
     irule stmtSimReturnTheory.eval_operand_old_vars >> simp[] >> qexists_tac `cm` >> simp[] >>
     rpt strip_tac >> `not_fresh_at mid x` by
       (irule not_fresh_at_mono >> qexists_tac `cm` >> simp[]) >> simp[]) >>
  `cm.cs_next_var <= su.cs_next_var /\ sa.cs_next_var <= su.cs_next_var` by decide_tac >>
  `!x. old = Var x ==> not_fresh_at su x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `cm` >> simp[]) >>
  drule_all buffer_alloc_code >> strip_tac >>
  qmatch_asmsub_abbrev_tac `MEM ai (fn_insts func)` >>
  `ai.inst_opcode = ALLOCA /\ ai.inst_id = cm.cs_next_id` by simp[Abbr `ai`,mk_inst_def] >>
  `compile_store_memory ce (Var q) (Var p) (vv_type vv) (vv_type vv) su = ((),cs)` by
    (qpat_assum `src = Var q` (SUBST1_TAC o SYM) >>
     qpat_assum `buf.buf_operand = Var p` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `N = type_memory_bytes ce (vv_type vv)` >>
  qabbrev_tac `m = val_store_size (BaseTV (BytesT (Dynamic kp))) (BytesV bytes)` >>
  qabbrev_tac `HP = \H. valid_horizon cx st0 H ee.storage_trace` >>
  drule_at (Pat `compile_store_memory _ (Var q) _ _ _ _ = _`)
    (Q.INST [`tv` |-> `BaseTV (BytesT (Dynamic kq))`,
             `phys` |-> `lowered_value_type ce e`, `pv` |-> `BaseTV (BytesT (Dynamic kp))`,
             `inst` |-> `ai`]
      (horizonTypeLib.at_horizon_named "H" create_blueprint_raw_bytes_store_arrival_mods)) >>
  disch_then (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ G tn`)) >>
  disch_then (mp_tac o SPEC_ALL) >>
  impl_tac >- suspend "store_inputs" >>
  disch_then (qx_choosel_then [`t`,`Gcopy`,`tnt`] (map_every assume_tac o CONJUNCTS)) >>
  suspend "arrival"
QED

Resume create_blueprint_raw_copy_at_cut_mods[store_inputs]:
  rpt conj_tac >>
  pure_rewrite_tac[GSYM loweringStateRelDefsTheory.regions_disjoint_def] >>
  (first_assum ACCEPT_TAC ORELSE
   simp[Abbr `N`,Abbr `m`,Abbr `HP`]) >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ (a,Ga,ta) [] _ /\ _`
    (drule_then strip_assume_tac) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume create_blueprint_raw_copy_at_cut_mods[arrival]:
  qabbrev_tac `B = \x y. ?i. ctor_segment_fetch func x = SOME i /\
    cm.cs_next_id <= i.inst_id /\ i.inst_id < cs.cs_next_id /\
    i.inst_opcode <> INVOKE /\ ctor_segment_next func x i = SOME y` >>
  `RTC B s t` by suspend "band" >>
  `u = t` by suspend "first_arrival" >>
  qpat_x_assum `u = t` SUBST_ALL_TAC >>
  `expr_val_rel cx (BaseT (BytesT (Dynamic k))) (BytesV bytes) (Var p) t` by
    (simp[expr_val_rel_def,is_word_type_def,eval_operand_def] >> fs[val_in_memory_def]) >>
  `s.vs_alloca_next <= t.vs_alloca_next /\ s0.vs_alloca_next <= t.vs_alloca_next` by
    (simp[] >> decide_tac) >>
  `saved = LocatedValue (vv_type vv) (mk_ptr (Var p) LocMemory)` by
    (qpat_assum `buf.buf_operand = Var p` (SUBST1_TAC o SYM) >>
     qpat_assum `dst = buf.buf_operand` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`p`,`dw`,`Gcopy`,`tnt`] >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE suspend "path")
QED

Resume create_blueprint_raw_copy_at_cut_mods[band]:
  irule RTC_TRANS >> qexists_tac `a` >> conj_tac
  >- (irule RTC_MONOTONE >> qpat_assum `RTC _ s a` (irule_at Any) >>
      simp[Abbr `B`] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  irule RTC_TRANS >> qexists_tac `z` >> conj_tac
  >- (irule RTC_MONOTONE >> qpat_assum `RTC _ a z` (irule_at Any) >>
      simp[Abbr `B`] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS,
        arithmeticTheory.LESS_EQ_TRANS,arithmeticTheory.LESS_IMP_LESS_OR_EQ]) >>
  irule RTC_MONOTONE >> qpat_assum `RTC _ z t` (irule_at Any) >>
  simp[Abbr `B`] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS,arithmeticTheory.LESS_IMP_LESS_OR_EQ]
QED

Resume create_blueprint_raw_copy_at_cut_mods[first_arrival]:
  irule ctor_same_func_first_arrival >>
  qexistsl_tac [`R`,`B`,`ctx`,`(cs.cs_current_bb,LENGTH cs.cs_current_insts)`,
    `explicit`,`func`,`next`,`s`] >>
  simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >> qpat_assum `!x y. R x y ==> _` (drule_then strip_assume_tac) >>
      metis_tac[]) >>
  simp[Abbr `B`] >> rpt gen_tac >> strip_tac >>
  reverse conj_tac >- (qexists_tac `i` >> simp[]) >>
  rpt strip_tac >> gvs[ctor_segment_fetch_def,AllCaseEqs()] >> decide_tac
QED

Resume create_blueprint_raw_copy_at_cut_mods[path]:
  rpt gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ (a,Ga,ta) [] _ /\ _`
    (drule_then strip_assume_tac) >>
  qunabbrev_tac `HP` >>
  qpat_x_assum `!H. _ ==> stmt_state_rel _ _ _ _ _ _ t /\ _`
    (qspec_then `H` (drule_then strip_assume_tac o BETA_RULE)) >>
  reverse conj_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] (OK a,Ga,ta)`
    (qspec_then `DF H` (mp_then Any mp_tac gas_origin_ptr_path_append)) >>
  simp[] >> disch_then irule >>
  qpat_assum `gas_origin_ptr_path _ (a,Ga,ta) [] (OK z,Gz,tz)`
    (mp_then Any mp_tac gas_origin_ptr_path_append) >>
  simp[] >> disch_then irule >> simp[]
QED

Finalise create_blueprint_raw_copy_at_cut_mods
