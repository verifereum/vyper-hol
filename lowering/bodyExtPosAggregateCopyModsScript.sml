(* A copied ExtCall argument uses the exact allocation at its snapshot cut. *)
Theory bodyExtPosAggregateCopyMods
Ancestors
  bodyExtPosSavedRowMods bodyQualifiedSnapshotStoreEntryMods
  bodyQualifiedSnapshotStoreEffectMods bodyQualifiedSnapshotFreshFrameMods
  bodyFullPostsMods bodyFullShadowBodyInv bodyFullIfExpReach
  bodyCopyReadPhysicalTypeMods exprBodyPreProps exprBodyPreTypingProps
  exprSimHypsDefs exprReasonOperand exprLoweringProps exprLowering compileEnv
  exprNamedConstResult exprSimConcatResult abiBuiltinDispatchCorrect
  exprSimSend[qualified,ignore_grammar]
  vyperAST vyperState loweringPosts bodyPtrDefs exprSimMemDefs
  context freshWrites words arithmetic finite_map
  vyperStorageFootprint vyperEvalExprPreservesScopesDom
  fragGasOriginPtr gasSummary fragExec venomState typedMemoryCopy
  loweringStateRelDefs stateRelProj exprSimProps typedCopyOriginPtrBase
Libs monadsyntax

Theorem ext_pos_copy_snapshot_retag:
  expr_body_pre_mods mods ce cx env e es /\ ~is_word_type (expr_type e) /\
  compile_expr ce (expr_type e) e sa = (vv,sm) ==>
  ext_call_arg_value (lowered_value_type ce e) vv = vv_with_type (lowered_value_type ce e) vv
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

Resume ext_pos_copy_snapshot_retag[changed_tag]:
  `(?n st. e = Literal (BaseT (StringT n)) (StringL st)) \/
   (?n bs. e = Literal (BaseT (BytesT (Dynamic n))) (BytesL bs)) \/
   (?n bs. e = Literal (BaseT (BytesT (Dynamic n))) (HexBytesL bs)) \/
   (?ann n args. e = Builtin ann (Concat n) args) \/
   (?ann en method tys args. e = TypeBuiltin ann (AbiEncode en method) tys args) \/
   (?ann fid args dr. e = Call ann (IntCall fid) args dr)` by
    (qpat_x_assum `lowered_value_type ce e <> expr_type e` mp_tac >>
     Cases_on `e` >> simp[lowered_value_type_def] >>
     TRY (rename1 `Literal ty lit` >> Cases_on `ty` >> simp[lowered_value_type_def] >>
          rename1 `BaseT bt` >> Cases_on `bt` >> Cases_on `lit` >> simp[lowered_value_type_def] >>
          rename1 `BytesT bound` >> Cases_on `bound` >> simp[lowered_value_type_def] >> NO_TAC) >>
     TRY (rename1 `Builtin ann bt args` >> Cases_on `bt` >> simp[lowered_value_type_def] >>
          `~is_word_type ann` by fs[expr_type_def] >>
          drule_all named_const_nonword_compile_shape >> simp[] >> NO_TAC) >>
     TRY (rename1 `TypeBuiltin ann tb tys args` >> Cases_on `tb` >> simp[lowered_value_type_def] >> NO_TAC) >>
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
  gvs[exprSimSendTheory.compile_expr_call] >>
  drule reason_compile_call >> simp[reason_result_shape_def]
QED

Finalise ext_pos_copy_snapshot_retag

Theorem ext_pos_aggregate_copy_landing_mods:
  expr_body_pre_mods mods ce cx env e es /\ ~is_word_type (expr_type e) /\
  ~is_word_type (lowered_value_type ce e) /\
  type_memory_bytes ce (lowered_value_type ce e) < dimword (:256) /\
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  compile_snapshot_vv ce T (ext_call_arg_value (lowered_value_type ce e) vv) sm = (sv,ss) /\
  fn_has_code sm ss func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!fn inst z. frag_reachable ctx func s fn inst z ==> dalloca_fmp_headroom inst z) /\
  return_buf_frame d ce sa s0 /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func ce cx es s0) /\
  eval_expr cx e (es with gas_obs := gs) = (INL raw,ee) /\
  ee.gas_obs = [] /\ read_result cx raw ee = (INL v,ee) /\
  storage_trace_domain cx st0 ee.storage_trace /\ ~s.vs_halted /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx e es sa sm s0 ee raw vv s /\
    vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee raw vv s /\
    s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
    alloca_history func s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    s0.vs_alloca_next <= s.vs_alloca_next /\ ghost_inv_at_mods (DF H) lo d ce cx ee G tn s /\
    ptr_vv_ok cx (post_value_type ce e) raw vv ee G tn s /\
    (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
      ?val. read_result cx raw ee = (INL val,ee) /\
        !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
               eval_operand (vv_operand vv) s = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory rt val (w2n w) mem)) /\
    (!tag op. vv = StackValue tag op /\ ~is_word_type (post_value_type ce e) ==>
      ptr_buf_ok ce e op G s) /\
    (!tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok ce e p.ptr_operand G s) /\ ghost_kept_at lo ce es sa G0 tn0 s0 G tn) ==>
  ?u Gu tu. !H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tu) /\
    ext_pos_saved_row_mods lo ce cx (xs ++ kw_es) sa ss H e sv v ee Gu tu u /\
    stmt_state_rel H ctx func ce cx ee u /\ immutable_frame_mods func ce cx ee u /\
    storage_well_formed_on cx ee (FST H) /\ return_buf_frame d ce ss u /\
    ghost_inv_at_mods (DF H) lo d ce cx ee Gu tu u /\
    ghost_kept_at lo ce es sa G0 tn0 s0 Gu tu /\ alloca_history func u /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\ s0.vs_alloca_next <= u.vs_alloca_next /\
    (!fn inst z. frag_reachable ctx func u fn inst z ==> dalloca_fmp_headroom inst z) /\
    ~u.vs_halted /\ u.vs_current_bb = ss.cs_current_bb /\ u.vs_inst_idx = LENGTH ss.cs_current_insts /\
    wb_frame ce es ee sa s0 u /\ (~expr_has_effect e ==> pure_frame ce func es sa s0 u) /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then assume_tac ext_pos_copy_snapshot_retag >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _` (drule_then strip_assume_tac) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx es s0` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _` irule >>
     `valid_horizon cx st0 H (es with gas_obs := gs).storage_trace` suffices_by simp[] >>
     irule (INST_TYPE [alpha |-> ``:eval_result``] valid_horizon_frame) >>
     qexistsl_tac [`eval_expr cx e`,`INL raw`,`ee`] >>
     simp[vyperStorageTraceTheory.evaluate_storage_trace_frame]) >>
  `compile_snapshot_vv ce T (vv_with_type (lowered_value_type ce e) vv) sm = (sv,ss)` by
    (qpat_assum `ext_call_arg_value _ _ = _` (fn th => pure_rewrite_tac [GSYM th]) >>
     first_assum ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx e es sa sm s0 ee raw vv s /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >> simp[]) >>
  drule_all qualified_snapshot_store_entry_pure_mods >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`p`,`dw`,`src`,`sw`,`su`,`z`,`Gz`,`tz`,`rt`]
      (map_every assume_tac o CONJUNCTS))) >>
  suspend "store"
QED

Resume ext_pos_aggregate_copy_landing_mods[store]:
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ z /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `stmt_state_rel _ ctx func ce cx ee z`
    (mp_then Any (assume_tac o cj 2) stmt_state_rel_local_ptrs_alloca) >>
  `z.vs_alloca_next < dimword (:256)` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ _ z`
       (mp_then Any assume_tac stmt_state_rel_alloca_room) >>
     drule_then ACCEPT_TAC alloca_room_next_lt) >>
  `allocas_from lo z /\ lo <= z.vs_alloca_next` by
    (qpat_assum `ghost_inv_at_mods _ lo d ce cx ee Gz tz z`
       (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
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
  suspend "frame"
QED

Resume ext_pos_aggregate_copy_landing_mods[frame]:
  `sm.cs_next_id < ss.cs_next_id` by decide_tac >>
  `!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at su x` by
    (rpt strip_tac >> irule local_ptrs_reserved_imm_base >> qexists `ce` >> simp[]) >>
  `!x. not_fresh_at su x ==>
     FLOOKUP Gu x = FLOOKUP Gz x /\ op_taint tu (Var x) = op_taint tz (Var x)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!x. not_fresh_at su x ==> lookup_var x u = _ /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT2))) >>
  `!i. ~(w2n dw <= i /\ i < w2n dw + val_store_size rt v) ==>
     (i IN tu.t_mem <=> i IN tz.t_mem)` by
    (gen_tac >> disch_tac >> first_x_assum irule >> fs[DE_MORGAN_THM]) >>
  drule_all_then (map_every assume_tac o CONJUNCTS) qualified_snapshot_fresh_store_frame_mods >>
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
     qpat_assum `!D. gas_origin_ptr_path _ (z,Gz,tz) [] _`
       (qspec_then `D` ACCEPT_TAC)) >>
  `!fn inst t. frag_reachable ctx func u fn inst t ==> dalloca_fmp_headroom inst t` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] (OK u,Gu,tu)`
       (qspec_then `DF (storage_trace_horizon ee.storage_trace)` assume_tac) >>
     metis_tac[gas_origin_ptr_path_dalloca_fmp_headroom]) >>
  suspend "package"
QED

Resume ext_pos_aggregate_copy_landing_mods[package]:
  qexistsl_tac [`u`,`Gu`,`tu`] >> qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ u /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] (OK u,Gu,tu)`
    (qspec_then `DF H` assume_tac) >>
  `s0.vs_alloca_next <= u.vs_alloca_next` by simp[] >>
  qpat_assum `wb_frame _ _ _ _ _ u` (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE all_tac)
  >~ [`ext_pos_saved_row_mods _ _ _ _ _ _ _ _ _ _ _ _ _`] >- suspend "row" >>
  suspend "pure"
QED

Resume ext_pos_aggregate_copy_landing_mods[row]:
  drule_then strip_assume_tac exprSimUnwrapTheory.compile_expr_extends >>
  qpat_assum `compile_snapshot_vv ce T (ext_call_arg_value _ _) sm = _`
    (fn th => mp_tac (Q.SPECL [`ce`,`T`,`ext_call_arg_value (lowered_value_type ce e) vv`,`sm`]
      ci_mono_compile_snapshot_vv) >> simp[th,ci_mono_def] >> strip_tac) >>
  rewrite_tac[ext_pos_saved_row_mods_def] >> conj_tac
  >- (qexistsl_tac [`sa`,`sm`,`ss`,`vv`,`Value v`,`T`] >>
      asm_rewrite_tac[] >> suspend "owned") >>
  suspend "live"
QED

Resume ext_pos_aggregate_copy_landing_mods[owned]:
  conj_tac
  >- (qexistsl_tac [`p`,`dw`,`rt`] >>
      simp[vv_location_def,vv_operand_def,mk_ptr_def,eval_operand_def] >> first_assum ACCEPT_TAC) >>
  simp[vv_location_def,vv_operand_def,mk_ptr_def,read_result_def,return_def] >>
  `val_in_memory rt v (w2n dw) u.vs_memory` by
    (qpat_assum `!m. mem_agree_outside tu.t_mem u.vs_memory m ==> _` irule >>
     simp[mem_agree_outside_def]) >>
  rpt conj_tac
  >~ [`vv_holds_mods _ _ _ _ _ _ _`]
  >- simp[vv_holds_mods_def,vv_holds_def,mk_ptr_def,eval_operand_def,read_result_def,return_def] 
  >~ [`vv_at _ _ _ _ _ _ _ _ _`]
  >- (irule (REWRITE_RULE [mk_ptr_def] exprSimIfExpWidenedProvenanceTheory.allocated_vv_at) >>
      simp[eval_operand_def,read_result_def,return_def] >>
      qexistsl_tac [`type_memory_size rt`,`sm.cs_next_id`,`w2n dw`] >>
      simp[] >> conj_tac
      >- (rpt gen_tac >> disch_tac >>
          qpat_assum `!n b l. loweringStateRelDefs$local_region ce _ u n b l ==>
            loweringStateRelDefs$regions_disjoint _ _ b l` (drule_then mp_tac) >>
          rewrite_tac[loweringStateRelDefsTheory.regions_disjoint_def] >>
          simp[AC ADD_ASSOC ADD_COMM]) >>
      `val_footprint rt v <= type_memory_size rt` by simp[val_footprint_le] >>
      simp[AC ADD_ASSOC ADD_COMM])
  >~ [`ptr_vv_ok _ _ _ _ _ _ _ _`] >- suspend "ptr" >>
  simp[vv_store_bound_def,mk_ptr_def,eval_operand_def,read_result_def,return_def] >>
  decide_tac
QED

Resume ext_pos_aggregate_copy_landing_mods[ptr]:
  qpat_x_assum `ptr_covers Gu tu p u _` mp_tac >>
  simp[ptr_covers_def] >> strip_tac >>
  simp[ptr_vv_ok_def,ptr_mem_ok_def,mk_ptr_def,eval_operand_def,read_result_def,return_def] >>
  strip_tac >> qexistsl_tac [`b`,`sz'`] >> simp[] >> decide_tac
QED

Resume ext_pos_aggregate_copy_landing_mods[live]:
  simp[vv_storage_live_def,vv_location_def,mk_ptr_def] >>
  qpat_x_assum `ptr_covers Gu tu p u _` mp_tac >>
  simp[ptr_covers_def] >> strip_tac >>
  simp[ptr_buf_ok_def,eval_operand_def] >> strip_tac >>
  qexistsl_tac [`b`,`sz'`] >> simp[]
QED

Resume ext_pos_aggregate_copy_landing_mods[pure]:
  strip_tac >>
  qpat_assum `~expr_has_effect e ==> pure_frame ce func es sa s0 z`
    (drule_then assume_tac) >>
  irule pure_frame_buffer_tail >>
  qpat_assum `pure_frame ce func es sa s0 z` (irule_at Any) >>
  qpat_assum `MEM (mk_inst sm.cs_next_id ALLOCA _ _) _` (irule_at Any) >>
  `u.vs_allocas = z.vs_allocas` by
    (qpat_assum `typed_copy_state_frame _ _ _ z u`
       (mp_tac o REWRITE_RULE [typed_copy_state_frame_def]) >>
     simp[venom_state_component_equality]) >>
  qpat_assum `typed_copy_state_frame _ _ _ z u`
    (strip_assume_tac o REWRITE_RULE [typed_copy_state_frame_def]) >>
  qpat_assum `typed_copy_frame _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [typed_copy_frame_def]) >>
  qexistsl [`type_memory_size rt`,`w2n dw`] >>
  simp[venomInstTheory.mk_inst_def,loweringStateRelDefsTheory.regions_disjoint_def] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!name b len. local_region ce es.scopes s0 name b len ==> _`
        drule >> simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  rpt gen_tac >> disch_tac >>
  qpat_assum `!a n. _ ==> mem_bytes_at a n u.vs_memory = _`
    (qspecl_then [`off`,`len`] mp_tac) >>
  (impl_tac >-
   (qpat_x_assum `len + off ≤ w2n dw \/ type_memory_size rt + w2n dw ≤ off`
      mp_tac >>
    qpat_x_assum `val_store_size rt v ≤ type_memory_size rt` mp_tac >>
    simp[] >> decide_tac)) >> simp[]
QED

Finalise ext_pos_aggregate_copy_landing_mods
