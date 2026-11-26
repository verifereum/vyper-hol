(* The materialized Create row starts at the successful open-value landing.
   The snapshot suffix has no source effects and contributes no gas marks. *)
Theory bodyCreateCtorSavedMods
Ancestors
  bodyQualifiedSnapshotStoreEntryMods bodyQualifiedSnapshotStoreEffectMods
  bodyQualifiedSnapshotFreshFrameMods bodyCopyReadPhysicalTypeMods
  exprReasonOperand exprNamedConstResult exprSimConcatResult
  exprSimSend[qualified,ignore_grammar] abiBuiltinDispatchCorrect
  exprBodyPreProps exprBodyPreTypingProps exprSimHypsDefs exprLoweringProps
  exprSimIfExpWidenedProvenance exprSimProps exprSimUnwrap rawCallBufferPtr
  bodyFullPostsMods bodyFullShadowBodyInv bodyFullIfExpReach
  bodyMemoryDefs bodyPtrDefs exprSimMemDefs loweringPosts
  typedCopyOriginPtrBase typedMemoryCopy stateRelProj loweringStateRelDefs
  fragGasOriginPtr fragExec gasSummary freshWrites context compileEnv
  exprLowering vyperAST vyperState vyperInterpreter vyperStorageFootprint
  vyperEvalExprPreservesScopesDom venomState venomInst words finite_map arithmetic
Libs monadsyntax pairLib

Theorem ctor_snapshot_input_mods[local]:
  expr_body_pre_mods mods ce cx env e es /\
  ~is_word_type (expr_type e) /\
  compile_expr ce (expr_type e) e sa = (vv,sm) ==>
  ext_call_arg_value (lowered_value_type ce e) vv =
    vv_with_type (lowered_value_type ce e) vv
Proof
  namedCases_on `vv` ["tag op", "tag p"] >> simp[ext_call_arg_value_def,vv_with_type_def] >>
  strip_tac >> Cases_on `lowered_value_type ce e = expr_type e`
  >- (`reason_uniform_shape compile_expr ce (expr_type e) e` by
       (irule compile_expr_reason_uniform >> qexists_tac `env` >>
        drule_then assume_tac expr_body_pre_mods_inv >>
        drule_then assume_tac expr_body_pre_mods_well_typed >> fs[expr_sim_inv_mods_def]) >>
      qpat_x_assum `reason_uniform_shape _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [reason_uniform_shape_def]) >>
      qpat_x_assum `!sa vv sb. _ ==> reason_result_shape _ _ _` (drule_then assume_tac) >>
      gvs[reason_result_shape_def]) >>
  suspend "changed_tag"
QED

Resume ctor_snapshot_input_mods[changed_tag]:
  `(?n st. e = Literal (BaseT (StringT n)) (StringL st)) \/
   (?n bs. e = Literal (BaseT (BytesT (Dynamic n))) (BytesL bs)) \/
   (?n bs. e = Literal (BaseT (BytesT (Dynamic n))) (HexBytesL bs)) \/
   (?ann n args. e = Builtin ann (Concat n) args) \/
   (?ann en method tys args. e = TypeBuiltin ann (AbiEncode en method) tys args) \/
   (?ann fid args dr. e = Call ann (IntCall fid) args dr)` by
    (qpat_x_assum `lowered_value_type ce e <> expr_type e` mp_tac >>
     Cases_on `e` >> simp[lowered_value_type_def]
     >~ [`Literal ty lit`]
     >- (Cases_on `ty` >> simp[lowered_value_type_def] >>
         rename1 `BaseT bt` >> Cases_on `bt` >> Cases_on `lit` >> simp[lowered_value_type_def] >>
         rename1 `BytesT bound` >> Cases_on `bound` >> simp[lowered_value_type_def])
     >~ [`Builtin ann bt args`]
     >- (Cases_on `bt = NamedConst` >> gvs[lowered_value_type_def]
         >- (`~is_word_type ann` by fs[expr_type_def] >>
             drule_all named_const_nonword_compile_shape >> simp[]) >>
         Cases_on `bt` >> gvs[lowered_value_type_def])
     >~ [`TypeBuiltin ann tb tys args`]
     >- (Cases_on `tb` >> simp[lowered_value_type_def]) >>
     rename1 `Call ann tgt args dr` >> Cases_on `tgt` >> simp[lowered_value_type_def]) >>
  pop_assum mp_tac >> strip_tac
  >- (gvs[Once compile_expr_raw_def,compile_expr_body_def,expr_type_def,
           compile_literal_vv_def,comp_bind_def,comp_return_def] >> pairarg_tac >> gvs[])
  >- (gvs[Once compile_expr_raw_def,compile_expr_body_def,expr_type_def,
           compile_literal_vv_def,comp_bind_def,comp_return_def] >> pairarg_tac >> gvs[])
  >- (gvs[Once compile_expr_raw_def,compile_expr_body_def,expr_type_def,
           compile_literal_vv_def,comp_bind_def,comp_return_def] >> pairarg_tac >> gvs[])
  >- (gvs[] >> drule concat_compile_shape >> simp[])
  >- (qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
      simp[Once compile_expr_component_eq] >>
      simp[Once compile_expr_raw_def,compile_type_builtin_dispatch_body_def] >>
      rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
      rpt (pairarg_tac >> gvs[]) >>
      Cases_on `LENGTH args = 1 /\ ~en` >> Cases_on `is_word_type (expr_type (HD args))` >>
      gvs[] >> drule as_ptr_val_result >> simp[]) >>
  gvs[exprSimSendTheory.compile_expr_call] >> drule reason_compile_call >> simp[reason_result_shape_def]
QED

Finalise ctor_snapshot_input_mods

Theorem ctor_snapshot_row_mods[local]:
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
  ~is_word_type (lowered_value_type ce e) /\ val_wf rt v /\
  type_memory_bytes ce (lowered_value_type ce e) = type_memory_size rt /\
  val_store_size rt v <= type_memory_size rt /\
  lookup_var p u = SOME dw /\
  ptr_covers Gu tu p u (type_memory_size rt) /\
  (!m. mem_agree_outside tu.t_mem u.vs_memory m ==> val_in_memory rt v (w2n dw) m) /\
  FLOOKUP u.vs_allocas sm.cs_next_id = SOME (w2n dw,type_memory_size rt) /\
  sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id < ss.cs_next_id /\
  w2n dw + type_memory_size rt <= u.vs_alloca_next /\
  (!name b len. local_region ce ee.scopes u name b len ==>
    regions_disjoint (w2n dw) (type_memory_size rt) b len) ==>
  let ty = lowered_value_type ce e in
  let sv = LocatedValue ty (mk_ptr (Var p) LocMemory) in
    vv_holds_mods ce cx ty (Value v) sv ee u /\
    vv_at ce cx ty sa ss ee (Value v) sv u /\
    ptr_vv_ok cx ty (Value v) sv ee Gu tu u /\
    vv_store_bound cx ty ty ee (Value v) sv u /\
    vv_storage_live H cx sv ee u /\ ptr_buf_ok ce e (vv_operand sv) Gu u
Proof
  strip_tac >> simp[] >>
  `val_in_memory rt v (w2n dw) u.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  rpt conj_tac
  >- simp[vv_holds_mods_def,vv_holds_def,mk_ptr_def,eval_operand_def,read_result_def,return_def]
  >- (irule allocated_vv_at >> simp[eval_operand_def,read_result_def,return_def] >>
      qexistsl_tac [`type_memory_size rt`,`sm.cs_next_id`,`w2n dw`] >> simp[] >>
      conj_tac
      >- (rpt gen_tac >> disch_tac >> first_x_assum drule >> simp[regions_disjoint_def]) >>
      `val_footprint rt v <= type_memory_size rt` by simp[val_footprint_le] >>
      decide_tac)
  >- (qpat_x_assum `ptr_covers Gu tu p u _` mp_tac >> simp[ptr_covers_def] >> strip_tac >>
      simp[ptr_vv_ok_def,ptr_mem_ok_def,mk_ptr_def,eval_operand_def,read_result_def,return_def] >>
      strip_tac >> qexistsl_tac [`b`,`sz'`] >> simp[] >> decide_tac)
  >- (simp[vv_store_bound_def,mk_ptr_def,eval_operand_def,read_result_def,return_def] >> decide_tac)
  >- simp[vv_storage_live_def,vv_location_def,mk_ptr_def] >>
  simp[vv_operand_def,mk_ptr_def] >> irule ptr_buf_ok_from_covers >>
  qexistsl_tac [`type_memory_size rt`,`tu`] >> simp[]
QED

Theorem ctor_snapshot_preserve_pure[local]:
  pure_frame ce func es sa s0 z /\
  typed_copy_state_frame su b n z u /\ n <= cap /\
  MEM (mk_inst aid ALLOCA [Lit (n2w cap)] [p]) (fn_insts func) /\
  sa.cs_next_id <= aid /\ FLOOKUP z.vs_allocas aid = SOME (b,cap) /\
  (!name off len. local_region ce es.scopes s0 name off len ==>
    regions_disjoint b cap off len) ==>
  pure_frame ce func es sa s0 u
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `u.vs_allocas = z.vs_allocas` by
    (qpat_assum `typed_copy_state_frame _ _ _ _ _`
       (mp_tac o AP_TERM ``\s. s.vs_allocas`` o CONJUNCT1 o
        REWRITE_RULE [typed_copy_state_frame_def]) >> simp[]) >>
  irule pure_frame_buffer_tail >>
  qexistsl_tac [`b`,`cap`,`mk_inst aid ALLOCA [Lit (n2w cap)] [p]`,`z`] >>
  simp[mk_inst_def] >> conj_tac
  >- (rpt strip_tac >> first_x_assum drule >> simp[regions_disjoint_def]) >>
  rpt strip_tac >>
  qpat_assum `typed_copy_state_frame _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [typed_copy_state_frame_def,typed_copy_frame_def]) >>
  first_x_assum irule >> fs[regions_disjoint_def] >> decide_tac
QED

Theorem create_ctor_materialized_head_mods:
  expr_body_pre_mods mods ce cx env e es /\ ~is_word_type (expr_type e) /\
  ~is_word_type (lowered_value_type ce e) /\
  type_memory_bytes ce (lowered_value_type ce e) < dimword (:256) /\
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  compile_snapshot_vv ce T (ext_call_arg_value (lowered_value_type ce e) vv) sm = (sv,ss) /\
  fn_has_code sm ss func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d ce sa s0 /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx es s0) /\
  eval_expr cx e (es with gas_obs := gs) = (INL raw,ee) /\
  read_result cx raw ee = (INL v,ee) /\ storage_trace_domain cx st0 ee.storage_trace /\
  (!fn inst z. frag_reachable ctx func s fn inst z ==> dalloca_fmp_headroom inst z) /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx e es sa sm s0 ee raw vv s /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee raw vv s /\
  ptr_vv_ok cx (post_value_type ce e) raw vv ee G tn s /\
  (!tag op. vv = StackValue tag op /\ ~is_word_type (post_value_type ce e) ==>
    ptr_buf_ok ce e op G s) /\
  (!tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand G s) /\
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?val. read_result cx raw ee = (INL val,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
        eval_operand (vv_operand vv) s = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory rt val (w2n w) mem)) /\
  ghost_kept_at lo ce es sa G0 tn0 s0 G tn ==>
  ?u Gu tu p dw rt.
    sv = LocatedValue (lowered_value_type ce e) (mk_ptr (Var p) LocMemory) /\
    eval_operand (vv_operand sv) u = SOME dw /\
    evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\ val_wf rt v /\
    FLOOKUP u.vs_allocas sm.cs_next_id = SOME (w2n dw,type_memory_size rt) /\
    sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id < ss.cs_next_id /\
    not_fresh_at ss p /\ ptr_covers Gu tu p u (type_memory_size rt) /\
    lo <= w2n dw /\ w2n dw + type_memory_size rt <= u.vs_alloca_next /\
    (!aid b len. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
      regions_disjoint (w2n dw) (type_memory_size rt) b len) /\
    (!name b len. local_region ce ee.scopes u name b len ==>
      regions_disjoint (w2n dw) (type_memory_size rt) b len) /\
    read_result cx (Value v) ee = (INL v,ee) /\
    vv_holds_mods ce cx (lowered_value_type ce e) (Value v) sv ee u /\
    vv_at ce cx (lowered_value_type ce e) sa ss ee (Value v) sv u /\
    ptr_vv_ok cx (lowered_value_type ce e) (Value v) sv ee Gu tu u /\
    vv_store_bound cx (lowered_value_type ce e) (lowered_value_type ce e) ee (Value v) sv u /\
    ptr_buf_ok ce e (vv_operand sv) Gu u /\
    wb_frame ce es ee sa s0 u /\ MAP FDOM ee.scopes = MAP FDOM es.scopes /\
    (~expr_has_effect e ==> pure_frame ce func es sa s0 u) /\
    return_buf_frame d ce ss u /\ ghost_kept_at lo ce es sa G0 tn0 s0 Gu tu /\
    alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    s0.vs_alloca_next <= u.vs_alloca_next /\ ~u.vs_halted /\
    u.vs_current_bb = ss.cs_current_bb /\ u.vs_inst_idx = LENGTH ss.cs_current_insts /\
    (!fn inst z. frag_reachable ctx func u fn inst z ==> dalloca_fmp_headroom inst z) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tu) /\
      stmt_state_rel H ctx func ce cx ee u /\ immutable_frame_mods func ce cx ee u /\
      storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee Gu tu u /\
      vv_storage_live H cx sv ee u)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then (fn th => qpat_x_assum `compile_snapshot_vv _ _ _ _ = _`
    (assume_tac o PURE_REWRITE_RULE [th])) ctor_snapshot_input_mods >>
  drule_all qualified_snapshot_store_entry_pure_mods >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`p`,`dw`,`src`,`sw`,`su`,`z`,`Gz`,`tz`,`rt`]
      (map_every assume_tac o CONJUNCTS))) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ z /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `stmt_state_rel _ ctx func ce cx ee z`
    (mp_then Any (assume_tac o CONJUNCT2) stmt_state_rel_local_ptrs_alloca) >>
  `z.vs_alloca_next < dimword (:256)` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ _ z`
       (mp_then Any assume_tac stmt_state_rel_alloca_room) >>
     drule_then ACCEPT_TAC alloca_room_next_lt) >>
  `allocas_from lo z /\ lo <= z.vs_alloca_next` by
    (qpat_assum `ghost_inv_at_mods _ lo d ce cx ee Gz tz z`
       (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "store"
QED

Resume create_ctor_materialized_head_mods[store]:
  `0 < type_memory_size rt ==> ?x w. src = Var x /\ not_fresh_at su x /\
      lookup_var x z = SOME w /\ ptr_covers Gz tz x z (type_memory_size rt) /\
      w2n w + val_store_size rt v <= z.vs_alloca_next /\
      (!m. mem_agree_outside tz.t_mem z.vs_memory m ==> val_in_memory rt v (w2n w) m)` by
    (disch_tac >>
     qpat_assum `0 < type_memory_size rt ==> _` (drule_then strip_assume_tac) >>
     qexistsl_tac [`x`,`sw`] >>
     `val_store_size rt v <= type_memory_size rt` by simp[val_store_size_le] >>
     fs[eval_operand_def] >> decide_tac) >>
  `lookup_var p z = SOME (n2w (w2n dw))` by simp[] >>
  drule_all (SIMP_RULE bool_ss []
    (Q.INST [`cap` |-> `type_memory_size rt`] qualified_snapshot_same_type_store_mods)) >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`u`,`Gu`,`tu`] (map_every assume_tac o CONJUNCTS))) >>
  `!i. ~(w2n dw <= i /\ i < w2n dw + val_store_size rt v) ==>
     (i IN tu.t_mem <=> i IN tz.t_mem)` by
    (gen_tac >> disch_tac >> first_x_assum irule >> fs[DE_MORGAN_THM]) >>
  `sm.cs_next_id < ss.cs_next_id` by decide_tac >>
  `!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at su x` by
    (rpt strip_tac >> irule local_ptrs_reserved_imm_base >> qexists `ce` >> simp[]) >>
  `!x. not_fresh_at su x ==>
     FLOOKUP Gu x = FLOOKUP Gz x /\ op_taint tu (Var x) = op_taint tz (Var x)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!x. not_fresh_at su x ==> lookup_var x u = _ /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT2))) >>
  drule_all_then (map_every assume_tac o CONJUNCTS) qualified_snapshot_fresh_store_frame_mods >>
  suspend "finish"
QED

Resume create_ctor_materialized_head_mods[finish]:
  `u.vs_alloca_next = z.vs_alloca_next` by
    (qpat_assum `typed_copy_state_frame _ _ _ z u`
      (mp_tac o AP_TERM ``\s. s.vs_alloca_next`` o CONJUNCT1 o
       REWRITE_RULE [typed_copy_state_frame_def]) >> simp[]) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp u)` by
    (drule_then (fn th => simp[th]) typed_copy_state_frame_allocas_below_fmp) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tu)` by
    (qx_gen_tac `D` >>
     qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] _`
       (qspec_then `D` (mp_tac o MATCH_MP gas_origin_ptr_path_append)) >>
     simp[NoAsms] >> disch_then irule >>
     qpat_assum `!D. gas_origin_ptr_path _ (z,Gz,tz) [] _` (qspec_then `D` ACCEPT_TAC)) >>
  `!fn inst t. frag_reachable ctx func u fn inst t ==> dalloca_fmp_headroom inst t` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] (OK u,Gu,tu)`
       (qspec_then `DF (storage_trace_horizon ee.storage_trace)`
         (mp_then Any mp_tac gas_origin_ptr_path_dalloca_fmp_headroom)) >>
     disch_then (fn th => qx_genl_tac [`f`,`ins`,`t`] >> disch_tac >>
       qspecl_then [`f`,`ins`,`t`] match_mp_tac th) >>
     asm_rewrite_tac[]) >>
  `MAP FDOM ee.scopes = MAP FDOM es.scopes` by
    (drule_then mp_tac eval_expr_preserves_scopes_dom >> simp[]) >>
  `~expr_has_effect e ==> pure_frame ce func es sa s0 u` by
    (disch_tac >>
     qpat_assum `~expr_has_effect e ==> pure_frame _ _ _ _ _ z`
       (drule_then assume_tac) >>
     drule_all_then ACCEPT_TAC ctor_snapshot_preserve_pure) >>
  suspend "package"
QED

Resume create_ctor_materialized_head_mods[package]:
  `lookup_var p u = SOME dw` by
    (qpat_assum `lookup_var p u = SOME (n2w (w2n dw))` (mp_tac) >> simp[]) >>
  drule_all_then (strip_assume_tac o SIMP_RULE bool_ss [LET_THM]) ctor_snapshot_row_mods >>
  qexistsl_tac [`u`,`Gu`,`tu`,`p`,`dw`,`rt`] >>
  asm_rewrite_tac[] >>
  simp[vv_operand_def,mk_ptr_def,eval_operand_def,read_result_def,return_def] >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ u /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  simp[]
QED

Finalise create_ctor_materialized_head_mods
