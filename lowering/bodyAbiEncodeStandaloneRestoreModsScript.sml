(* Restore the singleton saved operand at its actual compiler cut.
   Identity reads use the saved interval; copies use the unwrap interval. *)
Theory bodyAbiEncodeStandaloneRestoreMods
Ancestors
  bodyAbiEncodeSavedMemoryMods bodyAbiEncodeSavedSlotMods bodyAbiEncodeSavedCodeMods
  bodyFullPostsMods bodyFullShadowBodyInv exprSimUnwrap fragExec
  exprLowering loweringPosts context bodyPtrDefs memoryReadProps compileEnv
  abiEncodeValuesPhases exprLoweringProps pred_set finite_map list
  bodyAbiEncodePackedPostMods vyperStorageFootprint

Theorem abi_encode_standalone_restore_mods:
  ~is_word_type (lowered_value_type ce e) /\
  unwrap_value ce saved ready = (src,st) /\ fn_has_code ready st func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = ready.cs_current_bb /\
  s.vs_inst_idx = LENGTH ready.cs_current_insts /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
  value_has_type rt v /\ type_memory_bytes ce (lowered_value_type ce e) = type_memory_size rt /\
  type_memory_size rt < 2**64 /\ return_buf_frame d ce ready s /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    abi_encode_saved_row_mods lo ce cx sa ready e saved v si sm ss vv copy H ee G tn s /\
    stmt_state_rel H ctx func ce cx ee s /\ immutable_frame_mods func ce cx ee s /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  (!x. vv_operand saved = Var x ==> not_fresh_at ready x) /\
  ss.cs_next_id <= aid /\ aid < ready.cs_next_id /\
  FLOOKUP s.vs_allocas aid = SOME (b,n) /\ 32+k <= n /\
  read_memory (b+32) k s = prefix /\
  (!i. b+32 <= i /\ i < b+32+k ==> i NOTIN tn.t_mem) ==>
  ?z Gz tz first last.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gz,tz)) /\
    ~z.vs_halted /\ z.vs_current_bb = st.cs_current_bb /\
    z.vs_inst_idx = LENGTH st.cs_current_insts /\ alloca_history func z /\
    s.vs_alloca_next <= z.vs_alloca_next /\
    expr_val_rel cx (lowered_value_type ce e) v src z /\
    expr_val_at ce cx (lowered_value_type ce e) first last ee v src z /\
    ptr_val_ok cx (lowered_value_type ce e) v src Gz tz z /\
    expr_store_bound cx (lowered_value_type ce e) v src z /\
    (!x. src = Var x ==> not_fresh_at st x) /\
    (aid < first.cs_next_id \/ last.cs_next_id <= aid) /\ last.cs_next_id <= st.cs_next_id /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func ce cx ee z /\ immutable_frame_mods func ce cx ee z /\
      storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee Gz tz z) /\
    return_buf_frame d ce st z /\ pure_frame ce func ee ready s z /\
    wb_frame ce ee ee ready s z /\ ghost_kept_at lo ce ee ready G tn s Gz tz /\
    (!x. not_fresh_at ready x ==> lookup_var x z = lookup_var x s /\
      FLOOKUP Gz x = FLOOKUP G x /\ op_taint tz (Var x) = op_taint tn (Var x)) /\
    (!x cap. not_fresh_at ready x /\ ptr_covers G tn x s cap ==> ptr_covers Gz tz x z cap) /\
    (!id row. FLOOKUP s.vs_allocas id = SOME row ==> FLOOKUP z.vs_allocas id = SOME row) /\
    read_memory (b+32) k z = prefix /\
    (!i. b+32 <= i /\ i < b+32+k ==> i NOTIN tz.t_mem)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qabbrev_tac `hz = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 hz ee.storage_trace` by fs[Abbr `hz`,storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  qhdtm_assum `abi_encode_saved_row_mods`
    (MAP_EVERY assume_tac o CONJUNCTS o REWRITE_RULE [abi_encode_saved_row_mods_def]) >>
  qpat_x_assum `(?tag op. saved = StackValue tag op) \/ _` mp_tac >>
  simp_tac bool_ss [DISJ_ASSOC] >>
  disch_then (DISJ_CASES_THEN2 assume_tac strip_assume_tac)
  >- (qpat_x_assum `?raw. read_result cx raw ee = _ /\ _` strip_assume_tac >>
      `!x. src = Var x ==> not_fresh_at ready x` by
        (`src = vv_operand saved` suffices_by simp[] >>
         qpat_x_assum `(?tag op. saved = StackValue tag op) \/ _` strip_assume_tac >>
         gvs[unwrap_value_def,comp_return_def,vv_operand_def]) >>
      drule_all (REWRITE_RULE [REFL_CLAUSE]
        (Q.INST [`ty` |-> `lowered_value_type ce e`] abi_encode_saved_memory_restore_mods)) >>
      disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
      qexistsl_tac [`s`,`G`,`tn`,`si`,`ss`] >>
      gvs[exprSimWordArgsTheory.wb_frame_refl,wordArgsPtrTheory.ghost_kept_at_refl]) >>
  Cases_on `p.ptr_location = LocCode`
  >- (drule_all abi_encode_saved_code_restore_mods >>
      disch_then (qspecl_then [`explicit`,`PG`]
        (qx_choosel_then [`z`,`Gz`,`tz`,`root`,`w`]
          (MAP_EVERY assume_tac o CONJUNCTS))) >>
      qexistsl_tac [`z`,`Gz`,`tz`,`ready`,`st`] >> asm_rewrite_tac[] >>
      simp[] >> metis_tac[]) >>
  (Q.SUBGOAL_THEN `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient` assume_tac
   >- (qpat_x_assum `?raw. read_result cx raw ee = _ /\ _` strip_assume_tac >>
       Cases_on `p.ptr_location` >> gvs[bodyFullPostsModsTheory.vv_holds_mods_def,vv_holds_def])) >>
  drule_all abi_encode_saved_slot_restore_mods >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`z`,`Gz`,`tz`,`w`,`root`]
      (MAP_EVERY assume_tac o CONJUNCTS))) >>
  `mem_bytes_at b n z.vs_memory = mem_bytes_at b n s.vs_memory /\
   (!j. b <= j /\ j < b+n /\ j IN tz.t_mem ==> j IN tn.t_mem)` by
    (qpat_assum `!aid b len. _ ==> regions_disjoint _ _ b len /\ _`
       (drule_all_then strip_assume_tac) >> asm_rewrite_tac[]) >>
  `read_memory (b+32) k z = prefix` by
    (qpat_x_assum `read_memory _ _ s = _` (SUBST1_TAC o SYM) >>
     pure_rewrite_tac[read_memory_eq_mem_bytes_at] >>
     `!mem. TAKE k (DROP 32 (mem_bytes_at b n mem)) = mem_bytes_at (b+32) k mem` by
       simp[abiCanonicalHeadSizeTheory.mem_bytes_at_window] >>
     pop_assum (fn th => REWRITE_TAC [GSYM th]) >> asm_rewrite_tac[]) >>
  qexistsl_tac [`z`,`Gz`,`tz`,`ready`,`st`] >> asm_rewrite_tac[] >>
  simp[] >> rpt strip_tac >>
  `b <= i /\ i < b+n` by decide_tac >>
  qpat_assum `!j. b <= j /\ _ ==> j IN tn.t_mem` (qspec_then `i` mp_tac) >>
  simp[] >>
  qpat_assum `!j. b+32 <= j /\ _ ==> j NOTIN tn.t_mem` (qspec_then `i` mp_tac) >>
  simp[]
QED
