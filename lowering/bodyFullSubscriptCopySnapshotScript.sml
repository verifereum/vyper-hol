(* The copied array base is materialized before evaluation of the index. *)
Theory bodyFullSubscriptCopySnapshot
Ancestors
  bodyFullExtCallDefaultPrefix bodyFullExtCallDefaultCopy
  bodyFullStructLitFrames bodyFullPathHistory placeStoreDynPrepare
  exprSimSubscriptArray exprSimSubscriptArraySource bodySimExprCases
  abiEncodeArgsCase abiEncodeMaterialize aggregateEvaluatedLayout
  gasShadowCompileConvert stateRelProj exprOperandVar exprSimProps
  freshWrites ptrDiscipline bodyPtrDefs typedMemoryCopy loweringPosts
  words venomState exprLoweringProps compileEnv fragExec
  exprSimSource exprSimHyps vyperStorageFootprint vyperStorageTrace
  gasShadowState bodyMemoryDefs

Theorem subscript_array_copy_snapshot_caller_frame:
  expr_body_pre ce cx env (Subscript ann obj idx) es /\
  expr_type obj = ArrayT et bd /\ ~array_slot_base ce obj /\
  eval_expr cx obj (es with gas_obs := gs) = (INL raw,mid) /\
  read_result cx raw mid = (INL saved,mid) /\
  compile_expr ce ty obj sa = (bvv,sm) /\
  compile_snapshot_vv ce T bvv sm = (cvv,sc) /\
  gas_shadow_state sm shadow_sm /\
  fn_has_code sm sc func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d ce sa s0 /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es s0) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    vv_post H ctx func ce cx obj es sa sm s0 mid raw bvv s /\
    ghost_inv_at (DF H) lo d ce cx mid G1 tn1 s) /\
  vv_store_bound cx (post_value_type ce obj) (lowered_value_type ce obj) mid raw bvv s /\
  ptr_vv_ok cx (post_value_type ce obj) raw bvv mid G1 tn1 s /\
  (!t op. bvv = StackValue t op ==> ptr_buf_ok ce obj op G1 s) /\
  (!t p. bvv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
         ptr_buf_ok ce obj p.ptr_operand G1 s) /\
  (ce.ce_is_ctor /\ vv_location bvv = SOME LocCode ==>
    ?v. read_result cx raw mid = (INL v,mid) /\
        !rt w. evaluate_type (get_tenv cx) (post_value_type ce obj) = SOME rt /\
               eval_operand (vv_operand bvv) s = SOME w ==>
               w2n w + type_memory_size rt <= lo /\
               (!m. mem_agree_outside tn1.t_mem s.vs_memory m ==>
                    val_in_memory rt v (w2n w) m)) /\
  ghost_kept_at lo ce es sa G0 tn0 s0 G1 tn1 /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?shadow_sc u Gc tnc q w atv.
    compile_snapshot_vv ce T bvv shadow_sm = (cvv,shadow_sc) /\
    gas_shadow_state sc shadow_sc /\
    cvv = LocatedValue (ArrayT et bd) (mk_ptr (Var q) LocMemory) /\
    evaluate_type (get_tenv cx) (ArrayT et bd) = SOME atv /\
    val_wf atv saved /\ value_has_type atv saved /\
    lookup_var q u = SOME w /\ not_fresh_at sc q /\
    ptr_covers Gc tnc q u (type_memory_size atv) /\
    (!m. mem_agree_outside tnc.t_mem u.vs_memory m ==>
         val_in_memory atv saved (w2n w) m) /\
    vv_own ce cx (ArrayT et bd) sm sc mid (Value saved) cvv u /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G1,tn1) [] (OK u,Gc,tnc) /\
      stmt_state_rel H ctx func ce cx mid u /\ storage_well_formed_on cx mid (FST H) /\
      ghost_inv_at (DF H) lo d ce cx mid Gc tnc u) /\
    ghost_kept_at lo ce es sa G0 tn0 s0 Gc tnc /\ return_buf_frame d ce sc u /\
    local_ptrs_reserved ce sc /\ alloca_history func u /\ allocas_from lo u /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    s.vs_alloca_next <= u.vs_alloca_next /\
    (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s /\
         FLOOKUP Gc x = FLOOKUP G1 x /\ op_taint tnc (Var x) = op_taint tn1 (Var x)) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
                 FLOOKUP u.vs_allocas aid = SOME entry) /\
    u.vs_labels = s.vs_labels /\ ~u.vs_halted /\
    u.vs_current_bb = sc.cs_current_bb /\ u.vs_inst_idx = LENGTH sc.cs_current_insts /\
    wb_frame ce es mid sa s0 u /\
    (~expr_has_effect obj ==> pure_frame ce func es sa s0 u)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `post_value_type ce obj = expr_type obj` by
    metis_tac[expr_body_pre_subscript_base_type] >>
  `expr_body_pre ce cx env obj (es with gas_obs := gs)` by
    metis_tac[expr_body_pre_array_subscript_base,expr_body_pre_gas_obs] >>
  `arg_type_fits (lowered_value_type ce obj) (expr_type obj)` by
    metis_tac[expr_body_pre_lowered_fits] >>
  `~is_word_type (expr_type obj) /\ ~is_bytestring_type (expr_type obj)` by
    simp[is_word_type_def,is_bytestring_type_def] >>
  `post_value_type ce obj = lowered_value_type ce obj` by
    metis_tac[materialize_post_lowered_classify] >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. _ ==> vv_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace`
      (drule_then (map_every assume_tac o CONJUNCTS))) >>
  `vv_type bvv = ArrayT et bd` by
    (drule_all compile_array_vv_type >> simp[]) >>
  `bind (eval_expr cx obj) (read_result cx) (es with gas_obs := gs) = (INL saved,mid)` by
    simp[vyperStateTheory.bind_def] >>
  drule_all (REWRITE_RULE [ETA_THM] abi_args_success_ready) >> simp[] >>
  disch_then (qx_choose_then `atv` mp_tac o cj 3) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "compile"
QED

Resume subscript_array_copy_snapshot_caller_frame[compile]:
  `ci_mono sa sm /\ ci_mono sm sc` by
    metis_tac[compile_expr_ci_mono,ci_mono_compile_snapshot_vv,pairTheory.SND] >>
  `local_ptrs_reserved ce sm /\ local_ptrs_reserved ce sc` by
    (fs[ci_mono_def] >> metis_tac[local_ptrs_reserved_next_var]) >>
  `!x. vv_operand bvv = Var x ==> not_fresh_at sm x` by
    metis_tac[cj 1 compiler_compile_var] >>
  Cases_on `compile_snapshot_vv ce T bvv shadow_sm` >>
  rename1 `compile_snapshot_vv ce T bvv shadow_sm = (cvv',shadow_sc)` >>
  `cvv' = cvv /\ gas_shadow_state sc shadow_sc` by
    (qpat_assum `gas_shadow_state sm shadow_sm`
       (mp_then Any mp_tac (Q.INST [`cenv` |-> `ce`, `copy_flag` |-> `T`, `vv` |-> `bvv`]
         (REWRITE_RULE [gas_shadow_compiles_def] gas_shadow_compiles_snapshot_vv))) >>
     disch_then (qspecl_then [`ce`,`bvv`] mp_tac) >> simp[]) >>
  Cases_on `compile_alloc_buffer (type_memory_bytes ce (ArrayT et bd)) sm` >>
  rename1 `compile_alloc_buffer _ sm = (buf,sk)` >>
  Cases_on `unwrap_value ce bvv sk` >>
  rename1 `unwrap_value ce bvv sk = (src,sl)` >>
  Cases_on `compile_store_memory ce src buf.buf_operand (ArrayT et bd) (ArrayT et bd) sl` >>
  rename1 `compile_store_memory _ _ _ _ _ sl = (unit_result,st)` >>
  Cases_on `unit_result` >>
  `cvv = LocatedValue (ArrayT et bd) (mk_ptr buf.buf_operand LocMemory) /\ sc = st` by
    (qpat_x_assum `compile_snapshot_vv ce T bvv sm = (cvv,sc)` mp_tac >>
     simp[exprLoweringTheory.compile_snapshot_vv_def,is_word_type_def,
          exprLoweringTheory.compile_materialize_vv_def,comp_bind_def,
          comp_ignore_bind_def,comp_return_def]) >>
  qpat_x_assum `sc = st` (SUBST_ALL_TAC o SYM) >>
  `ci_mono sm sk /\ ci_mono sk sl /\ ci_mono sl sc` by
    metis_tac[ci_mono_compile_alloc_buffer,ci_mono_unwrap_value,
      ci_mono_compile_store_memory,pairTheory.SND] >>
  `fn_has_code sm sk func /\ fn_has_code sk sl func /\ fn_has_code sl sc func` by
    (`ci_mono sk sc` by metis_tac[ci_mono_trans] >>
     fs[ci_mono_def] >> metis_tac[fn_has_code_split]) >>
  suspend "alloc_unwrap"
QED

Resume subscript_array_copy_snapshot_caller_frame[alloc_unwrap]:
  `lowered_value_type ce obj = ArrayT et bd` by metis_tac[] >>
  `evaluate_type (get_tenv cx) (post_value_type ce obj) = SOME atv` by metis_tac[] >>
  `evaluate_type (get_tenv cx) (ArrayT et bd) = SOME atv /\
   type_memory_bytes ce (ArrayT et bd) = type_memory_size atv` by metis_tac[] >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    fs[ci_mono_def] >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >> simp[]) >>
  `storage_trace_domain cx st0 es.storage_trace` by
    (`?obs. mid.storage_trace = es.storage_trace ++ obs` by
       (qpat_assum `eval_expr cx obj _ = _`
         (mp_then Any mp_tac storage_trace_frame_prefix) >>
        simp[cj 5 evaluate_storage_trace_frame]) >>
     metis_tac[storage_trace_domain_prefix]) >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func ce cx es s0` by
    (qpat_assum `!H. _ ==> stmt_state_rel H _ _ _ _ es s0`
      (qspec_then `storage_trace_horizon es.storage_trace` mp_tac) >>
     fs[storage_trace_domain_def]) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `type_memory_size atv < dimword (:256)` by decide_tac >>
  `compile_alloc_buffer (type_memory_bytes ce (lowered_value_type ce obj)) sm = (buf,sk)` by
    metis_tac[] >>
  `!v. read_result cx raw mid = (INL v,mid) ==> value_has_type atv v` by simp[] >>
  let
    fun feed pat next rule = qpat_assum pat (mp_then Any next rule)
  in
    feed `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func ce cx es s0`
    (feed `compile_expr ce ty obj sa = (bvv,sm)`
    (feed `compile_alloc_buffer (type_memory_bytes ce (lowered_value_type ce obj)) sm = (buf,sk)`
    (feed `unwrap_value ce bvv sk = (src,sl)`
    (feed `!H. _ ==> vv_post H ctx func ce cx obj es sa sm s0 mid raw bvv s /\ _`
    (feed `ghost_kept_at lo ce es sa G0 tn0 s0 G1 tn1`
    (feed `evaluate_type (get_tenv cx) (post_value_type ce obj) = SOME atv`
    (feed `evaluate_type (get_tenv cx) (lowered_value_type ce obj) = SOME atv`
      mp_tac))))))) extcall_default_prefix_store_entry
  end >>
  disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[is_word_type_def]))) >>
  disch_then (foldr (uncurry qx_choose_then) (map_every assume_tac o CONJUNCTS)
    [`dst`,`dw`,`v`,`z`,`Gz`,`tz`,`sw`]) >>
  `v = saved` by metis_tac[sumTheory.INL_11,pairTheory.PAIR_EQ] >>
  qpat_x_assum `v = saved` SUBST_ALL_TAC >>
  suspend "copy"
QED

Resume subscript_array_copy_snapshot_caller_frame[copy]:
  `compile_store_memory ce src (Var dst) (ArrayT et bd) (ArrayT et bd) sl = ((),sc)` by
    (qpat_assum `compile_store_memory ce src buf.buf_operand _ _ sl = _` (mp_tac) >>
     qpat_assum `buf.buf_operand = Var dst` (fn th => REWRITE_TAC[th]) >> simp[]) >>
  `ptr_mem_ok cx (ArrayT et bd) saved src Gz tz z` by metis_tac[] >>
  `type_memory_size atv <> 0 ==>
     (?x. src = Var x /\ ptr_covers Gz tz x z (type_memory_size atv)) /\
     ptr_covers Gz tz dst z (type_memory_size atv) /\
     w2n sw + type_memory_size atv <= z.vs_alloca_next /\
     w2n dw + type_memory_size atv <= z.vs_alloca_next /\
     z.vs_alloca_next < dimword (:256)` by simp[] >>
  let
    fun feed pat next rule = qpat_assum pat (mp_then Any next rule)
  in
    feed `compile_store_memory ce src (Var dst) (ArrayT et bd) (ArrayT et bd) sl = _`
    (feed `ptr_mem_ok cx (ArrayT et bd) saved src Gz tz z`
    (feed `evaluate_type (get_tenv cx) (ArrayT et bd) = SOME atv`
    (feed `eval_operand src z = SOME sw`
    (feed `lookup_var dst z = SOME dw`
    (feed `allocas_from lo z`
    (feed `fn_has_code sl sc func` mp_tac)))))) extcall_default_copy_capacity_joint
  end >>
  disch_then (qspecl_then [`explicit`,`ctx`,`PG`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >>
    (first_assum ACCEPT_TAC ORELSE simp[is_word_type_def,is_bytestring_type_def]))) >>
  disch_then (foldr (uncurry qx_choose_then) (map_every assume_tac o CONJUNCTS) [`u`,`Gu`,`tu`]) >>
  suspend "frames"
QED

Resume subscript_array_copy_snapshot_caller_frame[frames]:
  qpat_assum `typed_copy_state_frame sl _ _ z u`
    (mp_tac o REWRITE_RULE [typed_copy_state_frame_def]) >>
  simp[venom_state_component_equality,typed_copy_frame_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!H. _ ==> gas_origin_ptr_path _ (s,G1,tn1) [] (OK z,Gz,tz) /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace`
      (drule_then (map_every assume_tac o CONJUNCTS))) >>
  qpat_assum `expr_post _ ctx func ce cx obj es sa sl s0 mid saved src z`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [expr_post_def]) >>
  `ci_mono sm sl /\ ci_mono sa sl` by metis_tac[ci_mono_trans] >>
  `local_ptrs_reserved ce sl` by
    (fs[ci_mono_def] >> metis_tac[local_ptrs_reserved_next_var]) >>
  `sa.cs_next_var <= sl.cs_next_var /\ sa.cs_next_var <= sc.cs_next_var /\
   sm.cs_next_var <= sl.cs_next_var /\ sl.cs_next_var <= sc.cs_next_var` by fs[ci_mono_def] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sl x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  `!x. not_fresh_at sm x ==> not_fresh_at sl x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists `sm` >> simp[]) >>
  `not_fresh_at sc dst` by
    (irule not_fresh_at_mono >> qexists `sl` >> simp[]) >>
  `ptr_covers Gu tu dst u (type_memory_size atv)` by
    (qpat_assum `ptr_covers Gz tz dst z _` (mp_tac o REWRITE_RULE [ptr_covers_def]) >>
     qpat_assum `!x. not_fresh_at sl x ==> _ /\ _ /\ _` (qspec_then `dst` mp_tac) >>
     simp[ptr_covers_def]) >>
  `alloca_inv z` by
    (qpat_assum `stmt_state_rel _ ctx func ce cx mid z`
       (mp_then Any mp_tac stmt_state_rel_local_ptrs_alloca) >> simp[]) >>
  `alloca_history func u` by
    (irule body_full_path_alloca_history >>
     qpat_assum `!D. gas_origin_ptr_path _ (z,Gz,tz) [] (OK u,Gu,tu)`
       (qspec_then `DF (storage_trace_horizon mid.storage_trace)` (irule_at Any)) >> simp[]) >>
  `allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u)` by
    (conj_tac
     >- (pure_rewrite_tac[allocas_from_def] >>
         qpat_assum `u.vs_allocas = z.vs_allocas` SUBST1_TAC >>
         qpat_assum `allocas_from lo z` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def]))
     >> qpat_assum `typed_copy_state_frame sl _ _ z u`
          (mp_then Any mp_tac typedCopyOriginPtrBaseTheory.typed_copy_state_frame_allocas_below_fmp) >>
        simp[]) >>
  `return_buf_frame d ce sc u` by
    (irule return_buf_frame_frame >>
     qpat_assum `return_buf_frame d ce sa s0` (irule_at Any) >>
     simp[] >> rpt strip_tac >> `not_fresh_at sl x` by simp[] >> metis_tac[]) >>
  suspend "ownership"
QED

Resume subscript_array_copy_snapshot_caller_frame[ownership]:
  `sm.cs_next_id < sk.cs_next_id` by
    (qpat_assum `compile_alloc_buffer _ sm = (buf,sk)`
       (mp_then Any mp_tac abiBuiltinAllocationTheory.abi_builtin_alloc_buffer_shape) >>
     simp[loweringShapeRulesTheory.emit_op_eq] >> strip_tac >> gvs[]) >>
  `sk.cs_next_id <= sc.cs_next_id` by
    (fs[ci_mono_def] >> decide_tac) >>
  `!name b sz. local_region ce mid.scopes u name b sz ==>
    regions_disjoint (w2n dw) (type_memory_size atv) b sz` by
    (rpt strip_tac >>
     `local_region ce mid.scopes z name b sz` by
       (qpat_assum `local_ptrs_reserved ce sl`
          (mp_then Any mp_tac exprSimCopyTheory.copy_buffer_local_region_frame) >>
        disch_then (qspecl_then [`z`,`u`] mp_tac) >>
        impl_tac >- (rpt strip_tac >> metis_tac[]) >>
        disch_then (qspecl_then [`mid.scopes`,`name`,`b`,`sz`] mp_tac) >> simp[]) >>
     qpat_assum `!name b len. local_region ce mid.scopes z name b len ==> _` irule >>
     metis_tac[]) >>
  `vv_own ce cx (ArrayT et bd) sm sc mid (Value saved)
       (LocatedValue (ArrayT et bd) (mk_ptr (Var dst) LocMemory)) u` by
    (simp[vv_own_def,contextTheory.mk_ptr_def,vyperStateTheory.read_result_def,
          vyperStateTheory.return_def,eval_operand_def] >>
     disj1_tac >> qexistsl [`sm.cs_next_id`,`w2n dw`,`type_memory_size atv`] >>
     `val_footprint atv saved <= type_memory_size atv` by simp[val_footprint_le] >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >>
     rpt strip_tac >>
     qpat_assum `!name b sz. local_region ce mid.scopes u name b sz ==> _`
       (qspecl_then [`n`,`lb`,`lsz`] mp_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  suspend "exterior"
QED

Resume subscript_array_copy_snapshot_caller_frame[exterior]:
  `lo <= w2n dw` by
    (qpat_assum `allocas_from lo z` (mp_tac o REWRITE_RULE [allocas_from_def]) >>
     disch_then (qspecl_then [`sm.cs_next_id`,`w2n dw`,`type_memory_size atv`] mp_tac) >> simp[]) >>
  `!name b sz. local_region ce es.scopes s0 name b sz ==>
     b+sz <= w2n dw \/ w2n dw + type_memory_size atv <= b` by
    (rpt strip_tac >>
     `local_region ce mid.scopes z name b sz` by
       (irule local_region_frame_fwd >>
        qpat_assum `local_region ce es.scopes s0 name b sz` (irule_at Any) >>
        qpat_assum `local_ptrs_reserved ce sa` (irule_at Any) >> simp[]) >>
     qpat_assum `!name b len. local_region ce mid.scopes z name b len ==> _`
       (qspecl_then [`name`,`b`,`sz`] mp_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def,DISJ_COMM]) >>
  `!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id ==>
    off+sz <= w2n dw \/ w2n dw + type_memory_size atv <= off` by
    (rpt strip_tac >>
     `FLOOKUP z.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
     `aid <> sm.cs_next_id` by decide_tac >>
     qpat_assum `alloca_inv z`
       (mp_tac o cj 1 o REWRITE_RULE [venomMemDefsTheory.alloca_inv_def]) >>
     pure_rewrite_tac [venomMemDefsTheory.allocas_non_overlapping_def] >>
     disch_then (qspecl_then [`aid`,`sm.cs_next_id`,`off`,`sz`,
                                `w2n dw`,`type_memory_size atv`] mp_tac) >> simp[]) >>
  `!name entry p sz w. lookup_scopes name mid.scopes = SOME entry /\
     FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) /\
     lookup_var p z = SOME w ==>
     val_wf entry.type entry.value /\
     (w2n w + val_footprint entry.type entry.value <= w2n dw \/
      w2n dw + type_memory_size atv <= w2n w)` by
    (rpt gen_tac >> strip_tac >>
     `local_region ce mid.scopes z name (w2n w) sz` by
       (simp[loweringStateRelDefsTheory.local_region_def] >> metis_tac[]) >>
     `type_memory_size entry.type <= sz /\ val_wf entry.type entry.value` by
       (qpat_assum `stmt_state_rel _ ctx func ce cx mid z`
         (mp_tac o cj 1 o MATCH_MP stmt_state_rel_local_ptrs_alloca) >>
        simp[loweringStateRelDefsTheory.local_ptrs_rel_def] >>
        disch_then (qspecl_then [`name`,`entry`,`p`,`sz`] mp_tac o cj 1) >> simp[]) >>
     simp[] >>
     `val_footprint entry.type entry.value <= sz` by
       (qpat_assum `val_wf entry.type entry.value`
         (mp_then Any mp_tac val_footprint_le) >> decide_tac) >>
     qpat_assum `!name b len. local_region ce mid.scopes z name b len ==> _`
       (qspecl_then [`name`,`w2n w`,`sz`] mp_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  suspend "caller_frame"
QED

Resume subscript_array_copy_snapshot_caller_frame[caller_frame]:
  `wb_frame ce es mid sa s0 z` by
    (qpat_assum `expr_post _ ctx func ce cx obj es sa sl s0 mid saved src z`
       (mp_then Any ACCEPT_TAC exprSimWordArgsTheory.expr_post_frame)) >>
  (* The destination is fresh at sa, but already present at the store
     entry sl. Transport the caller frame rather than framing from sl. *)
  `wb_frame ce es mid sa s0 u` by
    (qpat_assum `wb_frame ce es mid sa s0 z`
       (map_every assume_tac o CONJUNCTS o REWRITE_RULE [wb_frame_def]) >>
     rewrite_tac[wb_frame_def] >> rpt conj_tac
     >- (rpt strip_tac >> `not_fresh_at sl x` by simp[] >> metis_tac[])
     >- simp[]
     >- (rpt gen_tac >> strip_tac >>
         `off+sz <= w2n dw \/ w2n dw + type_memory_size atv <= off` by
           (qpat_assum `!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
                          aid < sa.cs_next_id ==> _`
              (qspecl_then [`aid`,`off`,`sz`] mp_tac) >> simp[]) >>
         `mem_bytes_at off sz u.vs_memory = mem_bytes_at off sz z.vs_memory` by
           (qpat_assum `!a n. _ ==> mem_bytes_at a n u.vs_memory = _`
              (qspecl_then [`off`,`sz`] mp_tac) >>
            simp[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >>
         qpat_assum `!aid off sz. _ ==> mem_bytes_at off sz z.vs_memory = _`
           (qspecl_then [`aid`,`off`,`sz`] mp_tac) >> simp[] >>
         (impl_tac >- first_assum ACCEPT_TAC) >> simp[]) >>
     irule exprSimCopyTheory.copy_buffer_locals_kept_frame >>
     qexistsl [`w2n dw`,`z`,`type_memory_size atv`] >>
     rpt conj_tac
     >- (rpt strip_tac >>
         qpat_assum `!n b sz. local_region ce es.scopes s0 n b sz ==> _`
           drule >> decide_tac)
     >- (rpt gen_tac >> disch_tac >>
         qpat_assum `!a n. _ ==> mem_bytes_at a n u.vs_memory = _`
           (qspecl_then [`off`,`len`] mp_tac) >>
         (impl_tac >- decide_tac) >> simp[]) >>
     first_assum ACCEPT_TAC) >>
  `~expr_has_effect obj ==> pure_frame ce func es sa s0 u` by
    (strip_tac >>
     `pure_frame ce func es sa s0 z` by
       (qpat_assum `expr_post _ ctx func ce cx obj es sa sl s0 mid saved src z`
         (mp_then Any mp_tac exprSimWordArgsTheory.expr_post_pure_frame) >> simp[]) >>
     irule pure_frame_buffer_tail >>
     qpat_assum `pure_frame ce func es sa s0 z` (irule_at Any) >>
     qpat_assum `MEM (mk_inst sm.cs_next_id ALLOCA _ _) _` (irule_at Any) >>
     qexistsl [`type_memory_size atv`,`w2n dw`] >>
     simp[venomInstTheory.mk_inst_def,loweringStateRelDefsTheory.regions_disjoint_def] >>
     conj_tac
     >- (rpt strip_tac >>
         qpat_assum `!n b sz. local_region ce es.scopes s0 n b sz ==> _`
           drule >> decide_tac) >>
     rpt gen_tac >> disch_tac >>
     qpat_assum `!a n. _ ==> mem_bytes_at a n u.vs_memory = _`
       (qspecl_then [`off`,`len`] mp_tac) >>
     (impl_tac >- decide_tac) >> simp[]) >>
  suspend "ghost"
QED

Resume subscript_array_copy_snapshot_caller_frame[ghost]:
  `!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sl x` by
    (rpt strip_tac >> `not_fresh_at sa x` by metis_tac[] >> simp[]) >>
  `!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sl x` by
    (rpt strip_tac >> `not_fresh_at sa x` by metis_tac[] >> simp[]) >>
  `!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sl x` by
    (qpat_assum `local_ptrs_reserved ce sl` (mp_tac o REWRITE_RULE
       [loweringStateRelDefsTheory.local_ptrs_reserved_def]) >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G1,tn1) [] (OK u,Gu,tu) /\
    stmt_state_rel H ctx func ce cx mid u /\ storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at (DF H) lo d ce cx mid Gu tu u /\
    ghost_kept_at lo ce es sa G0 tn0 s0 Gu tu` by
    (qx_gen_tac `H` >> strip_tac >>
     qpat_assum `!H. _ ==> gas_origin_ptr_path _ (s,G1,tn1) [] (OK z,Gz,tz) /\ _`
       (qspec_then `H` (drule_then (map_every assume_tac o CONJUNCTS))) >>
     qpat_assum `expr_post H ctx func ce cx obj es sa sl s0 mid saved src z`
       (map_every assume_tac o CONJUNCTS o REWRITE_RULE [expr_post_def]) >>
     conj_tac
     >- (qpat_assum `!D. gas_origin_ptr_path _ (z,Gz,tz) [] _`
           (qspec_then `DF H` assume_tac) >>
         qpat_assum `gas_origin_ptr_path (DF H,_,_,_,_,_) (s,G1,tn1) [] _`
           (mp_then Any mp_tac fragGasOriginPtrTheory.gas_origin_ptr_path_append) >> simp[]) >>
     conj_tac
     >- (irule place_typed_copy_alloca_state_frame >>
         qpat_assum `typed_copy_state_frame sl _ _ z u` (irule_at Any) >>
         qpat_assum `MEM (mk_inst sm.cs_next_id ALLOCA _ _) _` (irule_at Any) >>
         qexists `type_memory_size atv` >> simp[venomInstTheory.mk_inst_def] >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     irule structlit_store_ghost_frame >>
     qpat_assum `typed_copy_state_frame sl _ _ z u` (irule_at Any) >>
     qpat_assum `ghost_inv_at (DF H) lo d ce cx mid Gz tz z` (irule_at Any) >>
     rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[])) >>
  qpat_assum `!H. _ ==> gas_origin_ptr_path _ (s,G1,tn1) [] (OK u,Gu,tu) /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace`
      (drule_then (map_every assume_tac o CONJUNCTS))) >>
  `sl.cs_current_bb = sc.cs_current_bb` by
    (qpat_assum `u.vs_current_bb = sc.cs_current_bb` mp_tac >> simp[]) >>
  qexistsl [`u`,`Gu`,`tu`,`dst`,`dw`] >> simp[]
QED

Finalise subscript_array_copy_snapshot_caller_frame

(* The original interface forgets only the two caller-frame facts. *)
Theorem subscript_array_copy_snapshot_joint:
  expr_body_pre ce cx env (Subscript ann obj idx) es /\
  expr_type obj = ArrayT et bd /\ ~array_slot_base ce obj /\
  eval_expr cx obj (es with gas_obs := gs) = (INL raw,mid) /\
  read_result cx raw mid = (INL saved,mid) /\
  compile_expr ce ty obj sa = (bvv,sm) /\
  compile_snapshot_vv ce T bvv sm = (cvv,sc) /\
  gas_shadow_state sm shadow_sm /\
  fn_has_code sm sc func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d ce sa s0 /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es s0) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    vv_post H ctx func ce cx obj es sa sm s0 mid raw bvv s /\
    ghost_inv_at (DF H) lo d ce cx mid G1 tn1 s) /\
  vv_store_bound cx (post_value_type ce obj) (lowered_value_type ce obj) mid raw bvv s /\
  ptr_vv_ok cx (post_value_type ce obj) raw bvv mid G1 tn1 s /\
  (!t op. bvv = StackValue t op ==> ptr_buf_ok ce obj op G1 s) /\
  (!t p. bvv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
         ptr_buf_ok ce obj p.ptr_operand G1 s) /\
  (ce.ce_is_ctor /\ vv_location bvv = SOME LocCode ==>
    ?v. read_result cx raw mid = (INL v,mid) /\
        !rt w. evaluate_type (get_tenv cx) (post_value_type ce obj) = SOME rt /\
               eval_operand (vv_operand bvv) s = SOME w ==>
               w2n w + type_memory_size rt <= lo /\
               (!m. mem_agree_outside tn1.t_mem s.vs_memory m ==>
                    val_in_memory rt v (w2n w) m)) /\
  ghost_kept_at lo ce es sa G0 tn0 s0 G1 tn1 /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?shadow_sc u Gc tnc q w atv.
    compile_snapshot_vv ce T bvv shadow_sm = (cvv,shadow_sc) /\
    gas_shadow_state sc shadow_sc /\
    cvv = LocatedValue (ArrayT et bd) (mk_ptr (Var q) LocMemory) /\
    evaluate_type (get_tenv cx) (ArrayT et bd) = SOME atv /\
    val_wf atv saved /\ value_has_type atv saved /\
    lookup_var q u = SOME w /\ not_fresh_at sc q /\
    ptr_covers Gc tnc q u (type_memory_size atv) /\
    (!m. mem_agree_outside tnc.t_mem u.vs_memory m ==>
         val_in_memory atv saved (w2n w) m) /\
    vv_own ce cx (ArrayT et bd) sm sc mid (Value saved) cvv u /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G1,tn1) [] (OK u,Gc,tnc) /\
      stmt_state_rel H ctx func ce cx mid u /\ storage_well_formed_on cx mid (FST H) /\
      ghost_inv_at (DF H) lo d ce cx mid Gc tnc u) /\
    ghost_kept_at lo ce es sa G0 tn0 s0 Gc tnc /\ return_buf_frame d ce sc u /\
    local_ptrs_reserved ce sc /\ alloca_history func u /\ allocas_from lo u /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    s.vs_alloca_next <= u.vs_alloca_next /\
    (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s /\
         FLOOKUP Gc x = FLOOKUP G1 x /\ op_taint tnc (Var x) = op_taint tn1 (Var x)) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
                 FLOOKUP u.vs_allocas aid = SOME entry) /\
    u.vs_labels = s.vs_labels /\ ~u.vs_halted /\
    u.vs_current_bb = sc.cs_current_bb /\ u.vs_inst_idx = LENGTH sc.cs_current_insts
Proof
  disch_then (mp_tac o MATCH_MP subscript_array_copy_snapshot_caller_frame) >>
  disch_then (foldr (uncurry qx_choose_then) (map_every assume_tac o CONJUNCTS)
    [`shadow_sc`,`u`,`Gc`,`tnc`,`q`,`w`,`atv`]) >>
  qexistsl [`shadow_sc`,`u`,`Gc`,`tnc`,`q`,`w`,`atv`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
