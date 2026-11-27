(* Initialize the allocation at the returned VV tag, independently of the
   source's physical bytes capacity. *)
Theory bodyCreateBlueprintRawCopyStoreMods
Ancestors
  bodyFullExtCallDefaultBytesStore bodyQualifiedSnapshotFreshFrameMods
  bodyFullPathHistory rawCallBufferPtr representationCleanPtr
  valueEncodingProps valueEncodingDefs abiBuiltinAllocation exprLoweringProps
  stateRelProj typedCopyOriginPtrBase reasonCopySourcePtr
  bodyFullPostsMods gasOutcomeFullMods bodyMemoryDefs loweringStateRelDefs
  bodyPtrDefs typedMemoryCopy fragGasOriginPtr
  compileEnv context venomState venomInst freshWrites finite_map words
  valueEncoding loweringPosts vyperStorageFootprint ptrDiscipline

Theorem blueprint_raw_copy_store_mods:
  compile_store_memory ce (Var src) (Var dst) dt dt sc = ((),sb) /\
  dt = BaseT (BytesT (Dynamic cap)) /\ tv = BaseTV (BytesT (Dynamic cap)) /\
  evaluate_type (get_tenv cx) dt = SOME tv /\ value_has_type tv (BytesV bs) /\
  is_bytestring_type sty /\ evaluate_type (get_tenv cx) sty = SOME stv /\
  value_has_type stv (BytesV bs) /\ val_wf stv (BytesV bs) /\ LENGTH bs <= cap /\
  type_memory_bytes ce dt = type_memory_size tv /\ type_memory_size tv < 2**64 /\
  not_fresh_at sc src /\ not_fresh_at sc dst /\
  lookup_var src s = SOME sw /\ lookup_var dst s = SOME dw /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory stv (BytesV bs) (w2n sw) mem) /\
  ptr_covers G tn src s (type_memory_size stv) /\ ptr_covers G tn dst s (type_memory_size tv) /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  w2n dw + type_memory_size tv <= s.vs_alloca_next /\ s.vs_alloca_next < dimword (:256) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ lo <= w2n dw /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sc sb func /\ fn_inst_ids_distinct func /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sc.cs_current_bb /\ s.vs_inst_idx = LENGTH sc.cs_current_insts /\
  FLOOKUP s.vs_allocas aid = SOME (w2n dw,type_memory_size tv) /\
  FLOOKUP G dst = SOME (w2n dw,type_memory_size tv) /\
  MEM (mk_inst aid ALLOCA [Lit (n2w (type_memory_size tv))] [dst]) (fn_insts func) /\
  sa.cs_next_id <= aid /\ aid < sc.cs_next_id /\ sa.cs_next_var <= sc.cs_next_var /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sc /\
  (!name b len. local_region ce ee.scopes s name b len ==>
     regions_disjoint (w2n dw) (type_memory_size tv) b len) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  return_buf_frame d ce sc s /\ wb_frame ce es ee sa s0 s /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  ghost_kept_at lo ce es sa Gi ti s0 G tn /\ storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func ce cx ee s /\ immutable_frame_mods func ce cx ee s /\
      storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) ==>
  ?u Gf tm.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gf,tm)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
        stmt_state_rel H ctx func ce cx ee u /\ immutable_frame_mods func ce cx ee u /\
        storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee Gf tm u) /\
    ghost_kept_at lo ce es sa Gi ti s0 Gf tm /\ wb_frame ce es ee sa s0 u /\
    return_buf_frame d ce sb u /\ alloca_history func u /\ allocas_from lo u /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
    u.vs_labels = s.vs_labels /\ ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sc x ==> lookup_var x u = lookup_var x s /\
          FLOOKUP Gf x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x)) /\
    aid < sb.cs_next_id /\ not_fresh_at sb dst /\ lookup_var dst u = SOME dw /\
    FLOOKUP u.vs_allocas aid = SOME (w2n dw,type_memory_size tv) /\
    FLOOKUP Gf dst = SOME (w2n dw,type_memory_size tv) /\
    (!name b len. local_region ce ee.scopes u name b len ==>
       regions_disjoint (w2n dw) (type_memory_size tv) b len) /\
    ptr_covers Gf tm dst u (type_memory_size tv) /\
    ptr_val_ok cx dt (BytesV bs) (Var dst) Gf tm u /\ val_wf tv (BytesV bs) /\
    val_footprint tv (BytesV bs) <= type_memory_size tv /\
    eval_operand (Var dst) u = SOME dw /\ mload (w2n dw) u = n2w (LENGTH bs) /\
    ptr_covers Gf tm dst u (32 + LENGTH bs) /\ w2n dw + 32 < dimword (:256) /\
    w2n dw + 32 + LENGTH bs <= u.vs_alloca_next /\
    mem_bytes_at (w2n dw + 32) (LENGTH bs) u.vs_memory = bs /\
    (!i. w2n dw <= i /\ i < w2n dw + 32 + LENGTH bs ==> i NOTIN tm.t_mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `is_bytestring_type dt /\ ~is_word_type dt` by simp[is_bytestring_type_def,is_word_type_def] >>
  `32 + LENGTH bs <= type_memory_size tv` by
    (mp_tac (Q.SPEC `cap` abi_builtin_word_size_capacity) >>
     simp[type_memory_size_def] >> decide_tac) >>
  `val_wf tv (BytesV bs) /\ val_footprint tv (BytesV bs) <= type_memory_size tv` by
    (gvs[val_wf_def,val_footprint_def] >> decide_tac) >>
  `type_memory_size tv + 64 < dimword (:256)` by
    (irule vyperArithTheory.lt_dimword_256 >> qexists `65` >>
     qpat_assum `type_memory_size tv < 2**64` mp_tac >> simp[NoAsms] >> decide_tac) >>
  `compile_store_memory ce (Var src) (Var dst) dt sty sc = ((),sb)` by
    (qpat_assum `compile_store_memory _ _ _ dt dt _ = _` mp_tac >>
     gvs[compile_store_memory_def,is_bytestring_type_def,is_word_type_def]) >>
  drule_all extcall_default_bytes_store_capacity_joint >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`u`,`Gf`,`tm`] (map_every assume_tac o CONJUNCTS))) >>
  suspend "frame"
QED

Resume blueprint_raw_copy_store_mods[frame]:
  `typed_copy_state_frame sc (w2n dw) (type_memory_size tv) s u` by
    (simp[typed_copy_state_frame_def,typed_copy_frame_def] >>
     conj_tac >- gvs[venom_state_component_equality] >>
     rpt gen_tac >> disch_tac >>
     qpat_assum `!off k. _ ==> mem_bytes_at off k u.vs_memory = _` irule >>
     gvs[] >> intLib.COOPER_TAC) >>
  `u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
   u.vs_labels = s.vs_labels` by gvs[venom_state_component_equality] >>
  `ci_mono sc sb` by
    (mp_tac (Q.SPECL [`ce`,`Var src`,`Var dst`,`dt`,`dt`,`sc`]
       ci_mono_compile_store_memory) >> simp[]) >>
  `alloca_inv s` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> _`
       (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
     (impl_tac >- fs[storage_trace_domain_def]) >>
     strip_tac >> drule_then (ACCEPT_TAC o CONJUNCT2) stmt_state_rel_local_ptrs_alloca) >>
  suspend "linked"
QED

Resume blueprint_raw_copy_store_mods[linked]:
  `sc.cs_next_var <= sb.cs_next_var /\ aid < sb.cs_next_id` by
    (fs[ci_mono_def] >> decide_tac) >>
  `w2n dw + type_memory_size tv < dimword (:256)` by decide_tac >>
  `!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sc x` by
    fs[local_ptrs_reserved_def] >>
  `lookup_var dst s = SOME (n2w (w2n dw))` by simp[] >>
  `!x. not_fresh_at sc x ==>
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!x. not_fresh_at sc x ==> lookup_var x u = _ /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT2))) >>
  `!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size tv) ==>
      (i IN tm.t_mem <=> i IN tn.t_mem)` by
    (gen_tac >> disch_tac >> first_x_assum irule >> decide_tac) >>
  `w2n dw + type_memory_size tv <= s.vs_alloca_next` by decide_tac >>
  drule_all_then (map_every assume_tac o CONJUNCTS)
    (REWRITE_RULE [arithmeticTheory.LESS_EQ_REFL] (Q.INST [`n` |-> `cap`]
      qualified_snapshot_fresh_store_frame_mods)) >>
  suspend "package"
QED

Resume blueprint_raw_copy_store_mods[package]:
  `alloca_history func u` by
    (irule body_full_path_alloca_history >>
     qpat_assum `!D. gas_origin_ptr_path _ _ [] (OK u,Gf,tm)`
       (qspec_then `DF (storage_trace_horizon ee.storage_trace)` (irule_at Any)) >> simp[]) >>
  `allocas_from lo u` by
    (qpat_assum `u.vs_allocas = s.vs_allocas` (fn th => rewrite_tac[allocas_from_def,th]) >>
     qpat_assum `allocas_from lo s` (ACCEPT_TAC o REWRITE_RULE[allocas_from_def])) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp u)` by
    (drule_then (fn th => simp[th]) typed_copy_state_frame_allocas_below_fmp) >>
  `FLOOKUP Gf dst = SOME (w2n dw,type_memory_size tv)` by simp[] >>
  `ptr_val_ok cx dt (BytesV bs) (Var dst) Gf tm u` by
    (irule ptr_val_ok_from_type_covers >> conj_tac >- first_assum ACCEPT_TAC >>
     qexists `tv` >> asm_rewrite_tac[] >> rpt strip_tac >> gvs[]) >>
  `ptr_covers Gf tm dst u (32 + LENGTH bs)` by
    (irule ptr_covers_mono >> qexists `type_memory_size tv` >> simp[]) >>
  `w2n dw + 32 < dimword (:256) /\ w2n dw + 32 + LENGTH bs <= u.vs_alloca_next` by
    (fs[] >> decide_tac) >>
  `mload (w2n dw) u = n2w (LENGTH bs) /\
   mem_bytes_at (w2n dw + 32) (LENGTH bs) u.vs_memory = bs /\
   (!i. w2n dw <= i /\ i < w2n dw + 32 + LENGTH bs ==> i NOTIN tm.t_mem)` by
    suspend "header" >>
  qexistsl_tac [`u`,`Gf`,`tm`] >> asm_rewrite_tac[eval_operand_def,n2w_w2n]
QED

Resume blueprint_raw_copy_store_mods[header]:
  `val_in_memory tv (BytesV bs) (w2n dw) u.vs_memory` by
    (qpat_assum `!m. mem_agree_outside tm.t_mem _ m ==> _` irule >> simp[mem_agree_outside_def]) >>
  drule representationCleanPtrTheory.robust_val_in_memory_bytes_clean >>
  gvs[val_in_memory_def,GSYM mem_word_at_eq_mload] >>
  strip_tac >> gen_tac >> strip_tac >> Cases_on `i < w2n dw + 32`
  >- (qpat_assum `!k. w2n dw <= k /\ k < w2n dw + 32 ==> _`
        (qspec_then `i` mp_tac) >> simp[]) >>
  `w2n dw + 32 <= i` by decide_tac >>
  qpat_assum `!k. w2n dw + 32 <= k /\ _ ==> _`
    (qspec_then `i` mp_tac) >> simp[]
QED

Finalise blueprint_raw_copy_store_mods
