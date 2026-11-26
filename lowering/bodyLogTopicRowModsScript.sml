(* Restore one saved indexed argument, then encode it without changing its
   protected memory or allocating a second copy of the operand. *)
Theory bodyLogTopicRowMods
Ancestors
  bodyLogTopicNoncodeRestoreMods bodyLogTopicEncodeLandingMods
  bodyAbiEncodeSavedCodeMods eventLoweringStructure exprSimProps
  fragGasOriginPtrLoop exprSimWordArgs wordArgsPtr venomState
  bodyAbiEncodePackedPostMods vyperStorageFootprint context exprSafeOperand
  loweringStateRelDefs exprLoweringProps fragExec bodyMemoryDefs loweringPosts
  freshWrites bodyFullHashKeccakFixed

(* Only storage liveness in a saved row refers to the horizon. Keep the
   compile witnesses from a reached row, without equating two compile cuts. *)
Theorem log_topic_row_compile_witnesses[local]:
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    ?si sm ss vv copy. abi_encode_saved_row_mods lo ce cx origin a
      e saved v si sm ss vv copy H ee G tn s) ==>
  ?si sm ss vv copy. !H. valid_horizon cx st0 H ee.storage_trace ==>
    abi_encode_saved_row_mods lo ce cx origin a e saved v si sm ss vv copy H ee G tn s
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then (qx_choosel_then [`si`,`sm`,`ss`,`vv`,`copy`] assume_tac)) >>
  qexistsl [`si`,`sm`,`ss`,`vv`,`copy`] >> gen_tac >> disch_tac >>
  `vv_storage_live H cx saved ee s` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> _` (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (qx_choosel_then [`i`,`m`,`b`,`w`,`c`] mp_tac) >>
     simp[abi_encode_saved_row_mods_def]) >>
  qhdtm_x_assum `abi_encode_saved_row_mods`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [abi_encode_saved_row_mods_def]) >>
  asm_rewrite_tac[abi_encode_saved_row_mods_def]
QED

Theorem log_topic_restore_mods[local]:
  expr_body_pre_mods mods ce cx env e entry /\
  unwrap_value ce saved a = (src,m) /\ fn_has_code a m func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
  value_has_type rt v /\
  type_memory_bytes ce (lowered_value_type ce e) = type_memory_size rt /\
  type_memory_size rt < 2**64 /\ return_buf_frame d ce a s /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    abi_encode_saved_row_mods lo ce cx origin a e saved v si sm ss vv copy H ee G tn s /\
    stmt_state_rel H ctx func ce cx ee s /\ immutable_frame_mods func ce cx ee s /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) ==>
  ?z Gz tz.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gz,tz)) /\
    ~z.vs_halted /\ z.vs_current_bb = m.cs_current_bb /\
    z.vs_inst_idx = LENGTH m.cs_current_insts /\ alloca_history func z /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    s.vs_alloca_next <= z.vs_alloca_next /\ safe_operand m src /\
    expr_val_rel cx (lowered_value_type ce e) v src z /\
    expr_val_at ce cx (lowered_value_type ce e) origin m ee v src z /\
    ptr_val_ok cx (lowered_value_type ce e) v src Gz tz z /\
    expr_store_bound cx (lowered_value_type ce e) v src z /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func ce cx ee z /\ immutable_frame_mods func ce cx ee z /\
      storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee Gz tz z) /\
    return_buf_frame d ce m z /\ pure_frame ce func ee a s z /\
    wb_frame ce ee ee a s z /\ ghost_kept_at lo ce ee a G tn s Gz tz /\
    (!x. not_fresh_at a x ==> lookup_var x z = lookup_var x s /\
      FLOOKUP Gz x = FLOOKUP G x /\ op_taint tz (Var x) = op_taint tn (Var x)) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP z.vs_allocas aid = SOME b) /\
    (!aid b len. aid < a.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
      mem_bytes_at b len z.vs_memory = mem_bytes_at b len s.vs_memory /\
      (!j. b <= j /\ j < b+len /\ j IN tz.t_mem ==> j IN tn.t_mem)) /\
    mem_bytes_at 0 lo z.vs_memory = mem_bytes_at 0 lo s.vs_memory /\
    (!j. j < lo /\ j IN tz.t_mem ==> j IN tn.t_mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then (assume_tac o CONJUNCT1)) >>
  qhdtm_x_assum `abi_encode_saved_row_mods`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [abi_encode_saved_row_mods_def]) >>
  Cases_on `vv_location saved = SOME LocCode`
  >- suspend "code" >> suspend "noncode"
QED

Resume log_topic_restore_mods[code]:
  `?p. saved = LocatedValue (lowered_value_type ce e) p /\ p.ptr_location = LocCode` by
    (qpat_assum `(?tag op0. saved = StackValue _ _) \/ _` mp_tac >>
     strip_tac >> gvs[vv_location_def]) >>
  drule_all abi_encode_saved_code_restore_core_mods >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`z`,`Gz`,`tz`,`root`,`w`] (map_every assume_tac o CONJUNCTS))) >>
  `safe_operand m src` by simp[safe_operand_def] >>
  `expr_val_at ce cx (lowered_value_type ce e) origin m ee v src z` by
    (irule expr_val_at_start_mono >> qexists `a` >> asm_rewrite_tac[] >>
     drule_then (map_every assume_tac o CONJUNCTS) (cj 1 compile_expr_grows) >> decide_tac) >>
  qexistsl [`z`,`Gz`,`tz`] >> asm_rewrite_tac[] >>
  `mem_bytes_at 0 lo z.vs_memory = mem_bytes_at 0 lo s.vs_memory` by
    (qpat_assum `!off len. _ ==> mem_bytes_at off len _ = _` irule >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!aid b len. _ ==> regions_disjoint _ _ b len`
        (drule_all_then (assume_tac o REWRITE_RULE [regions_disjoint_def])) >>
      conj_tac
      >- (qpat_assum `!off len. _ ==> mem_bytes_at off len _ = _` irule >> simp[]) >>
      rpt strip_tac >> qpat_assum `!j. _ \/ _ ==> j IN tz.t_mem ==> _`
        (qspec_then `j` mp_tac) >> (impl_tac >- decide_tac) >> simp[]) >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  qpat_assum `!j. _ \/ _ ==> j IN tz.t_mem ==> _`
    (qspec_then `j` mp_tac) >> (impl_tac >- decide_tac) >> simp[]
QED

Resume log_topic_restore_mods[noncode]:
  `!l. vv_operand saved <> Label l` by
    (drule_all_then ACCEPT_TAC log_topic_saved_not_label_mods) >>
  drule_all log_topic_noncode_restore_mods >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`z`,`Gz`,`tz`] (map_every assume_tac o CONJUNCTS))) >>
  qexistsl [`z`,`Gz`,`tz`] >> asm_rewrite_tac[]
QED

Finalise log_topic_restore_mods

Theorem log_topic_row_mods:
  ty = lowered_value_type ce e /\ hashed = is_bytestring_type ty /\
  expr_body_pre_mods mods ce cx env e entry /\ expr_sim_inv_mods mods ce cx env ee /\
  supported_event_leaf_type ty /\ evaluate_type (get_tenv cx) ty = SOME rt /\
  value_has_type rt v /\ type_memory_bytes ce ty = type_memory_size rt /\
  type_memory_size rt < 2**64 /\ encode_event_topic ty v = SOME topic /\
  compile_log_saved_topics ce [(saved,hashed)] a = ([op],b) /\ fn_has_code a b func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  return_buf_frame d ce a s /\ local_ptrs_reserved ce a /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    ?si sm ss vv copy. abi_encode_saved_row_mods lo ce cx origin a
      e saved v si sm ss vv copy H ee G tn s) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee s /\ immutable_frame_mods func ce cx ee s /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tf)) /\
    ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ s.vs_alloca_next <= t.vs_alloca_next /\
    safe_operand b op /\ eval_operand op t = SOME topic /\ op_taint tf op = {} /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func ce cx ee t /\ immutable_frame_mods func ce cx ee t /\
      storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee Gf tf t) /\
    return_buf_frame d ce b t /\ pure_frame ce func ee a s t /\
    wb_frame ce ee ee a s t /\ ghost_kept_at lo ce ee a G tn s Gf tf /\
    (!x. not_fresh_at a x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid base len. aid < a.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (base,len) ==>
      mem_bytes_at base len t.vs_memory = mem_bytes_at base len s.vs_memory /\
      (!j. base <= j /\ j < base+len /\ j IN tf.t_mem ==> j IN tn.t_mem)) /\
    mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory /\
    (!j. j < lo /\ j IN tf.t_mem ==> j IN tn.t_mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all log_topic_row_compile_witnesses >>
  disch_then (qx_choosel_then [`si`,`sm`,`ss`,`vv`,`copy`] assume_tac) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==>
      abi_encode_saved_row_mods lo ce cx origin a e saved v si sm ss vv copy H ee G tn s`
    (drule_then assume_tac) >>
  qpat_x_assum `compile_log_saved_topics _ _ _ = _`
    (qx_choosel_then [`src`,`m`] strip_assume_tac o REWRITE_RULE [compile_log_saved_topic_cut]) >>
  `ci_mono a m` by (qspecl_then [`ce`,`saved`,`a`] mp_tac ci_mono_unwrap_value >> simp[]) >>
  `ci_mono m b` by (qspecl_then [`src`,`hashed`,`m`] mp_tac compile_encode_log_topic_ci_mono >> simp[]) >>
  ntac 2 (qpat_x_assum `ci_mono _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [ci_mono_def])) >>
  drule_all_then strip_assume_tac fn_has_code_split >>
  suspend "run"
QED

Resume log_topic_row_mods[run]:
  qpat_x_assum `hashed = _` SUBST_ALL_TAC >>
  qpat_x_assum `ty = _` SUBST_ALL_TAC >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    abi_encode_saved_row_mods lo ce cx origin a e saved v si sm ss vv copy H ee G tn s /\
    stmt_state_rel H ctx func ce cx ee s /\ immutable_frame_mods func ce cx ee s /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee G tn s` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >> asm_simp_tac bool_ss []) >>
  drule_all log_topic_restore_mods >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`z`,`Gz`,`tz`] (map_every assume_tac o CONJUNCTS))) >>
  qhdtm_x_assum `abi_encode_saved_row_mods`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [abi_encode_saved_row_mods_def]) >>
  `local_ptrs_reserved ce m` by
    (irule local_ptrs_reserved_next_var >> qexists `a` >> asm_simp_tac bool_ss []) >>
  `si.cs_next_var <= m.cs_next_var` by
    (drule_then (map_every assume_tac o CONJUNCTS) (cj 1 compile_expr_grows) >> decide_tac) >>
  `!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at m x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists `si` >>
     asm_simp_tac bool_ss [] >> first_assum (drule_then ACCEPT_TAC)) >>
  `!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at m x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists `si` >>
     asm_simp_tac bool_ss [] >> first_assum (drule_then ACCEPT_TAC)) >>
  Q.SUBGOAL_THEN `?H. valid_horizon cx st0 H ee.storage_trace` ASSUME_TAC
  >- (qexists `storage_trace_horizon ee.storage_trace` >> first_assum ACCEPT_TAC) >>
  drule_all log_topic_encode_landing_mods >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`t`,`Gf`,`tf`] (map_every assume_tac o CONJUNCTS))) >>
  suspend "frame"
QED

Resume log_topic_row_mods[frame]:
  qpat_assum `t with <|vs_vars := z.vs_vars; vs_inst_idx := z.vs_inst_idx|> = z`
    (map_every assume_tac o CONJUNCTS o SIMP_RULE (srw_ss()) [venom_state_component_equality]) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx ee s` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H ctx func ce cx ee s /\ _`
      (qspec_then `storage_trace_horizon ee.storage_trace`
        (drule_then (ACCEPT_TAC o CONJUNCT1)))) >>
  `wb_frame ce ee ee a s t` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ _ s` (mp_then Any irule wb_frame_trans) >>
     asm_rewrite_tac[] >> qexistsl [`ee`,`m`,`z`] >> asm_rewrite_tac[]) >>
  `ghost_kept_at lo ce ee a G tn s Gf tf` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ _ s`
       (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) irule ghost_kept_at_wb_trans) >>
     asm_rewrite_tac[] >> qexistsl [`Gz`,`ee`,`ee`,`z`,`m`,`tz`] >> asm_rewrite_tac[]) >>
  `return_buf_frame d ce b t` by
    (irule return_buf_frame_frame >> qexistsl [`ce`,`z`,`m`] >>
     simp[] >> rpt strip_tac >>
     irule wb_frame_vars >> qexistsl [`ce`,`ee`,`ee`,`z`,`m`] >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (drule_all_then (fn th => pure_once_rewrite_tac[th])
       allocasBelowFmpUpdatesPropsTheory.allocas_below_fmp_fields >> first_assum ACCEPT_TAC) >>
  `pure_frame ce func ee a s t` by
    (drule_all_then (fn th => pure_once_rewrite_tac[th]) pure_frame_state_cong >>
     first_assum ACCEPT_TAC) >>
  `!x. not_fresh_at a x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >>
     `not_fresh_at m x` by (irule freshWritesTheory.not_fresh_at_mono >> qexists `a` >> simp[]) >>
     qpat_assum `!x. not_fresh_at a x ==> _` (drule_then strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at m x ==> _` (drule_then strip_assume_tac) >> simp[]) >>
  qexistsl [`t`,`Gf`,`tf`] >> conj_tac
  >- (gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl [`Gz`,`z`,`tz`] >> simp[]) >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE asm_rewrite_tac[])
QED

Finalise log_topic_row_mods
