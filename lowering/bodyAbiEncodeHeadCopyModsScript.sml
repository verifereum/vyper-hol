(* Execute the private copy selected by the ABI positional snapshot. *)
Theory bodyAbiEncodeHeadCopyMods
Ancestors
  bodyAbiEncodePackedPostMods bodyQualifiedSnapshotStoreEntryMods
  bodyQualifiedSnapshotStoreEffectMods bodyQualifiedSnapshotFreshFrameMods
  bodyWriteSubscriptSourceMods bodyFullIfExpReach forPtrAllocationFrame
  typedCopyOriginPtrBase fragGasOriginPtrLoop exprSimUnwrap exprSimProps
  stateRelProj loweringStateRelDefs valueCopyBytes allocLimits words
  bodyFullPostsMods bodyFullShadowBodyInv bodyFullPredsMods bodyPtrDefs
  exprSimMemDefs loweringPosts context compileEnv exprLowering exprLoweringProps
  venomState vyperInterpreter vyperState vyperStorageTrace vyperStorageFootprint
  vyperEvalExprPreservesScopesDom freshWrites fragGasOriginPtr typedMemoryCopy
  bodyMemoryDefs finite_map arithmetic

Theorem abi_encode_copied_row[local]:
  compile_expr ce (expr_type e) e si = (vv,sm) /\
  compile_snapshot_vv ce T (ext_call_arg_value (lowered_value_type ce e) vv) sm = (sv,ss) /\
  ~is_word_type (lowered_value_type ce e) /\
  sv = LocatedValue (lowered_value_type ce e) (mk_ptr (Var p) LocMemory) /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
  type_memory_bytes ce (lowered_value_type ce e) = type_memory_size rt /\ val_wf rt v /\
  FLOOKUP u.vs_allocas sm.cs_next_id = SOME (w2n w,type_memory_size rt) /\
  lookup_var p u = SOME w /\ ptr_covers Gu tu p u (type_memory_size rt) /\
  w2n w + type_memory_size rt <= u.vs_alloca_next /\
  (!m. mem_agree_outside tu.t_mem u.vs_memory m ==> val_in_memory rt v (w2n w) m) /\
  (!n b sz. local_region ce ee.scopes u n b sz ==>
     loweringStateRelDefs$regions_disjoint (w2n w) (type_memory_size rt) b sz) /\
  sm.cs_next_id < ss.cs_next_id /\ sm.cs_next_var <= ss.cs_next_var /\
  local_ptrs_reserved ce si /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) ==>
  abi_encode_saved_row_mods lo ce cx si ss e sv v si sm ss vv T H ee Gu tu u
Proof
  strip_tac >>
  drule_then strip_assume_tac compile_expr_extends >>
  `val_in_memory rt v (w2n w) u.vs_memory` by fs[mem_agree_outside_def] >>
  `val_footprint rt v <= type_memory_size rt /\ val_store_size rt v <= type_memory_size rt`
    by simp[val_footprint_le,val_store_size_le] >>
  qpat_assum `ptr_covers _ _ _ _ _` (strip_assume_tac o REWRITE_RULE [ptr_covers_def]) >>
  gvs[abi_encode_saved_row_mods_def,vv_location_def,vv_operand_def,mk_ptr_def,eval_operand_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac
  >- (simp[ptr_buf_ok_def,eval_operand_def] >> strip_tac >>
      qexistsl_tac [`b`,`sz'`] >> simp[]) >>
  qexists_tac `Value v` >>
  simp[vv_holds_mods_def,vv_holds_def,vv_at_def,ptr_vv_ok_def,ptr_mem_ok_def,
       vv_store_bound_def,eval_operand_def,read_result_def,return_def] >>
  rpt conj_tac
  >- (disj1_tac >> qexists_tac `sm.cs_next_id` >>
      simp[GSYM loweringStateRelDefsTheory.regions_disjoint_def] >> first_assum ACCEPT_TAC)
QED

Theorem abi_encode_head_copy_mods:
  expr_body_pre_mods mods ce cx env e es /\
  body_const_cells_agree_mods mods cx env es /\
  ~is_word_type (expr_type e) /\ ~is_word_type (lowered_value_type ce e) /\
  type_alloc_ok ce (lowered_value_type ce e) /\
  eval_expr cx e (es with gas_obs := gs) = (INL raw,ee) /\
  read_result cx raw ee = (INL v,ee) /\
  compile_expr ce (expr_type e) e si = (vv,sm) /\
  compile_snapshot_vv ce T (ext_call_arg_value (lowered_value_type ce e) vv) sm = (sv,ss) /\
  vv_type (ext_call_arg_value (lowered_value_type ce e) vv) = lowered_value_type ce e /\
  fn_has_code sm ss func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce si /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  return_buf_frame d ce si s0 /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx es s0) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post_mods H ctx func ce cx e es si sm s0 ee raw vv s /\
     ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee raw vv s /\
  ptr_vv_ok cx (post_value_type ce e) raw vv ee G tn s /\
  (!tag op. vv = StackValue tag op /\ ~is_word_type (post_value_type ce e) ==> ptr_buf_ok ce e op G s) /\
  (!tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory ==> ptr_buf_ok ce e p.ptr_operand G s) /\
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
     ?v'. read_result cx raw ee = (INL v',ee) /\
          !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
                 eval_operand (vv_operand vv) s = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory rt v' (w2n w) m)) /\
  ghost_kept_at lo ce es si G0 tn0 s0 G tn /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u Gu tu.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tu)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      abi_encode_saved_row_mods lo ce cx si ss e sv v si sm ss vv T H ee Gu tu u /\
      stmt_state_rel H ctx func ce cx ee u /\ immutable_frame_mods func ce cx ee u /\
      storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee Gu tu u) /\
    (!x. vv_operand sv = Var x ==> not_fresh_at ss x) /\
    ~u.vs_halted /\ u.vs_current_bb = ss.cs_current_bb /\ u.vs_inst_idx = LENGTH ss.cs_current_insts /\
    alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    s0.vs_alloca_next <= u.vs_alloca_next /\ return_buf_frame d ce ss u /\
    wb_frame ce es ee si s0 u /\ ghost_kept_at lo ce es si G0 tn0 s0 Gu tu /\
    MAP FDOM ee.scopes = MAP FDOM es.scopes /\
    expr_sim_inv_mods mods ce cx env ee /\ body_const_cells_agree_mods mods cx env ee /\
    (!x w. not_fresh_at si x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
    ?z Gz tz su w rt.
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gz,tz)) /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (z,Gz,tz) [] (OK u,Gu,tu)) /\
      eval_operand (vv_operand sv) u = SOME w /\
      evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
      typed_copy_state_frame su (w2n w) (val_store_size rt v) z u /\
      (!i. ~(w2n w <= i /\ i < w2n w + val_store_size rt v) ==>
        (i IN tu.t_mem <=> i IN tz.t_mem)) /\
      tu.t_stor = tz.t_stor /\ tu.t_trans = tz.t_trans /\ tu.t_imm = tz.t_imm
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ext_call_arg_value (lowered_value_type ce e) vv =
   vv_with_type (lowered_value_type ce e) vv` by
    (Cases_on `vv` >> gvs[ext_call_arg_value_def,vv_with_type_def,vv_type_def]) >>
  `compile_snapshot_vv ce T (vv_with_type (lowered_value_type ce e) vv) sm = (sv,ss)` by fs[] >>
  `type_memory_bytes ce (lowered_value_type ce e) < dimword (:256)` by
    (qpat_x_assum `type_alloc_ok _ _` mp_tac >> simp[type_alloc_ok_def,dimword_def] >> decide_tac) >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee)` by
    simp[Once bind_def] >>
  `expr_body_pre_mods mods ce cx env e (es with gas_obs := gs) /\
   body_const_cells_agree_mods mods cx env (es with gas_obs := gs)` by simp[] >>
  drule_all_then strip_assume_tac write_index_read_source_mods >>
  `MAP FDOM ee.scopes = MAP FDOM es.scopes` by
    (drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >> simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  drule_all qualified_snapshot_store_entry_mods >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`p`,`dw`,`src`,`sw`,`su`,`z`,`Gz`,`tz`,`rt`]
      (map_every assume_tac o CONJUNCTS))) >>
  suspend "store"
QED

Resume abi_encode_head_copy_mods[store]:
  qpat_assum `!H. valid_horizon _ _ _ _ ==> stmt_state_rel _ _ _ _ _ _ z /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `stmt_state_rel _ _ _ _ _ _ z`
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

Resume abi_encode_head_copy_mods[frame]:
  `sm.cs_next_id < ss.cs_next_id` by decide_tac >>
  `sm.cs_next_var <= ss.cs_next_var` by
    (qspecl_then [`ce`,`T`,`vv_with_type (lowered_value_type ce e) vv`,`sm`]
       mp_tac ci_mono_compile_snapshot_vv >>
     simp[ci_mono_def]) >>
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
  `lookup_var p u = SOME dw` by fs[] >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tu)` by
    (gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gz`,`z`,`tz`] >> simp[]) >>
  suspend "post"
QED

Resume abi_encode_head_copy_mods[post]:
  `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ _ _ ==> vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ s /\ _`
       (drule_then (strip_assume_tac o REWRITE_RULE [vv_post_mods_def])) >>
     `FLOOKUP s.vs_allocas aid = SOME b` by simp[] >>
     qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] (OK u,Gu,tu)` (qspec_then `DF (storage_trace_horizon ee.storage_trace)` mp_tac) >>
     disch_then (assume_tac o CONJUNCT2 o MATCH_MP gas_origin_ptr_path_projections) >>
     drule_then irule gas_path_ptr_old_allocations >> simp[]) >>
  qexistsl_tac [`u`,`Gu`,`tu`] >>
  simp[vv_operand_def,mk_ptr_def] >> rpt conj_tac
  >- (qx_gen_tac `h` >> strip_tac >> conj_tac
      >- (qpat_assum `sv = LocatedValue _ _`
            (fn th => once_rewrite_tac [GSYM (REWRITE_RULE [mk_ptr_def] th)]) >>
          irule abi_encode_copied_row >>
          qpat_assum `lookup_var p u = SOME dw` (irule_at Any) >>
          simp[] >> first_assum ACCEPT_TAC) >>
      qpat_assum `!H. valid_horizon _ _ _ _ ==> stmt_state_rel _ _ _ _ _ _ u /\ _`
        (qspec_then `h` (drule_then (ACCEPT_TAC o cj 2))))
  >- (rpt strip_tac >> drule_all_then ACCEPT_TAC exprSimWordArgsTheory.wb_frame_vars) >>
  qexistsl_tac [`z`,`Gz`,`tz`,`su`,`dw`] >> simp[eval_operand_def]
QED

Finalise abi_encode_head_copy_mods
