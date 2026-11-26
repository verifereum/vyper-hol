(* Restore a selected non-code Log operand at its actual topic cursor. *)
Theory bodyLogTopicNoncodeRestoreMods
Ancestors
  bodyAbiEncodeSavedSlotMods bodyAbiEncodeSavedMemoryMods bodyFullLogScalarTopics
  bodyFullExtCallSavedOperand exprReasonOperand exprBodyPreProps exprOperandVar
  abiBuiltinAllocation exprSafeOperand wordArgsPtr exprSimWordArgs
  exprSimHypsDefs exprLowering context compileEnv emitHelper
  bodyAbiEncodePackedPostMods bodyFullPostsMods bodyFullShadowBodyInv
  exprLoweringProps freshWrites fragGasOriginPtr fragExec vyperStorageFootprint
  bodyPtrDefs bodyMemoryDefs loweringPosts loweringStateRelDefs
  bodyFullHashKeccakFixed finite_map arithmetic
Libs pairLib

(* The compiler gives the label exclusion at the original child, before
   snapshots transport its operand to the current cursor. *)
Theorem log_topic_saved_not_label_mods:
  expr_body_pre_mods mods ce cx env e es /\
  compile_expr ce (expr_type e) e si = (vv,sm) /\
  compile_snapshot_vv ce copy (ext_call_arg_value (lowered_value_type ce e) vv) sm = (saved,ss) ==>
  !l. vv_operand saved <> Label l
Proof
  strip_tac >>
  `!l. vv_operand vv <> Label l` by
    (drule expr_body_pre_mods_well_typed >> strip_tac >>
     drule expr_body_pre_mods_inv >> simp[expr_sim_inv_mods_def] >> strip_tac >>
     drule_all compile_expr_reason_uniform >>
     disch_then (qspec_then `expr_type e` mp_tac) >>
     simp[reason_uniform_shape_def] >> strip_tac >>
     first_x_assum drule >> Cases_on `vv` >> simp[reason_result_shape_def,vv_operand_def]) >>
  `vv_operand (ext_call_arg_value (lowered_value_type ce e) vv) = vv_operand vv` by
    (Cases_on `vv` >> simp[ext_call_arg_value_def,vv_operand_def]) >>
  qpat_x_assum `compile_snapshot_vv _ _ _ _ = _` mp_tac >>
  simp[compile_snapshot_vv_def] >> IF_CASES_TAC
  >- (simp[comp_bind_def] >> pairarg_tac >> simp[comp_return_def] >>
      strip_tac >> gvs[vv_operand_def] >> drule unwrap_value_not_label >> simp[]) >>
  Cases_on `copy` >> simp[comp_bind_def,comp_return_def]
  >- (pairarg_tac >> simp[] >> strip_tac >> gvs[vv_operand_def,mk_ptr_def] >>
      qpat_x_assum `compile_materialize_vv _ _ _ _ = _` mp_tac >>
      simp[compile_materialize_vv_def,comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
      rpt (pairarg_tac >> simp[]) >> rpt strip_tac >> gvs[] >>
      drule abi_builtin_alloc_buffer_shape >> simp[loweringShapeRulesTheory.emit_op_eq]) >>
  strip_tac >> gvs[]
QED

Theorem log_topic_noncode_restore_mods:
  vv_location saved <> SOME LocCode /\
  (!l. vv_operand saved <> Label l) /\
  unwrap_value ce saved ready = (src,sc) /\ fn_has_code ready sc func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = ready.cs_current_bb /\
  s.vs_inst_idx = LENGTH ready.cs_current_insts /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
  type_memory_bytes ce (lowered_value_type ce e) = type_memory_size rt /\
  type_memory_size rt < 2**64 /\ return_buf_frame d ce ready s /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    abi_encode_saved_row_mods lo ce cx sa ready e saved v si sm ss vv copy H ee G tn s /\
    stmt_state_rel H ctx func ce cx ee s /\ immutable_frame_mods func ce cx ee s /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) ==>
  ?z Gz tz.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gz,tz)) /\
    ~z.vs_halted /\ z.vs_current_bb = sc.cs_current_bb /\
    z.vs_inst_idx = LENGTH sc.cs_current_insts /\ alloca_history func z /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    s.vs_alloca_next <= z.vs_alloca_next /\
    safe_operand sc src /\
    expr_val_rel cx (lowered_value_type ce e) v src z /\
    expr_val_at ce cx (lowered_value_type ce e) sa sc ee v src z /\
    ptr_val_ok cx (lowered_value_type ce e) v src Gz tz z /\
    expr_store_bound cx (lowered_value_type ce e) v src z /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func ce cx ee z /\ immutable_frame_mods func ce cx ee z /\
      storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee Gz tz z) /\
    return_buf_frame d ce sc z /\ pure_frame ce func ee ready s z /\
    wb_frame ce ee ee ready s z /\ ghost_kept_at lo ce ee ready G tn s Gz tz /\
    (!x. not_fresh_at ready x ==> lookup_var x z = lookup_var x s /\
      FLOOKUP Gz x = FLOOKUP G x /\ op_taint tz (Var x) = op_taint tn (Var x)) /\
    (!x cap. not_fresh_at ready x /\ ptr_covers G tn x s cap ==> ptr_covers Gz tz x z cap) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP z.vs_allocas aid = SOME b) /\
    (!aid b len. aid < ready.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
      mem_bytes_at b len z.vs_memory = mem_bytes_at b len s.vs_memory /\
      (!j. b <= j /\ j < b+len /\ j IN tz.t_mem ==> j IN tn.t_mem)) /\
    mem_bytes_at 0 lo z.vs_memory = mem_bytes_at 0 lo s.vs_memory /\
    (!j. j < lo /\ j IN tz.t_mem ==> j IN tn.t_mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  qhdtm_x_assum `abi_encode_saved_row_mods`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [abi_encode_saved_row_mods_def]) >>
  `ci_mono ready sc` by
    (qspecl_then [`ce`,`saved`,`ready`] mp_tac ci_mono_unwrap_value >> simp[]) >>
  `si.cs_next_id <= ready.cs_next_id /\ ss.cs_next_id <= sc.cs_next_id` by
    (drule_then strip_assume_tac (cj 1 compile_expr_grows) >> fs[ci_mono_def] >> decide_tac) >>
  `sa.cs_next_id <= ready.cs_next_id` by decide_tac >>
  `!x. vv_operand saved = Var x ==> not_fresh_at ready x` by
    (gen_tac >> disch_tac >> irule not_fresh_at_mono >> qexists `ss` >> simp[] >>
     irule extcall_saved_operand_not_fresh >>
     goal_assum (drule_at (Pat `compile_snapshot_vv _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >> simp[]) >>
  `safe_operand sc src` by
    (simp[safe_operand_def] >> conj_tac
     >- (drule compiler_unwrap_value_var >> Cases_on `saved` >> gvs[vv_operand_def]) >>
     drule_all_then ACCEPT_TAC unwrap_value_not_label) >>
  Cases_on `(?tag op. saved = StackValue tag op) \/
    (?p. saved = LocatedValue (lowered_value_type ce e) p /\
         ~is_word_type (lowered_value_type ce e) /\ p.ptr_location = LocMemory)`
  >- suspend "identity" >>
  suspend "materialize"
QED

Resume log_topic_noncode_restore_mods[identity]:
  qpat_x_assum `?raw. read_result cx raw ee = _ /\ _`
    (qx_choose_then `raw` (map_every assume_tac o CONJUNCTS)) >>
  `!x. src = Var x ==> not_fresh_at ready x` by
    (qpat_assum `(?tag op. saved = StackValue tag op) \/ _` strip_assume_tac >>
     gvs[unwrap_value_def,comp_return_def,vv_operand_def]) >>
  drule_all_then (map_every assume_tac o CONJUNCTS)
    (SIMP_RULE (srw_ss()) [] (Q.INST [`ty` |-> `lowered_value_type ce e`]
      (SPEC_ALL abi_encode_saved_memory_restore_mods))) >>
  qpat_x_assum `sc = ready` SUBST_ALL_TAC >>
  qpat_x_assum `src = vv_operand saved` kall_tac >>
  qexistsl [`s`,`G`,`tn`] >>
  simp[wb_frame_refl,ghost_kept_at_refl] >>
  rpt conj_tac
  >- (drule_then ACCEPT_TAC stmt_state_rel_allocas_below_fmp)
  >- (irule log_topic_physical_val_at >> qexistsl [`ready`,`si`,`ss`] >> simp[]) >>
  rpt strip_tac >> qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then strip_assume_tac) >> simp[]
QED

Resume log_topic_noncode_restore_mods[materialize]:
  qpat_x_assum `(?tag op0. saved = StackValue tag op0) \/ _` mp_tac >>
  disch_then (DISJ_CASES_THEN2 assume_tac
    (DISJ_CASES_THEN2 assume_tac (qx_choose_then `p` (map_every assume_tac o CONJUNCTS))))
  >- (qpat_x_assum `~((?tag op. saved = StackValue tag op) \/ _)` mp_tac >>
      pop_assum mp_tac >> rpt (pop_assum kall_tac) >> metis_tac[])
  >- (qpat_x_assum `~((?tag op. saved = StackValue tag op) \/ _)` mp_tac >>
      pop_assum mp_tac >> rpt (pop_assum kall_tac) >> metis_tac[]) >>
  Q.SUBGOAL_THEN `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient` ASSUME_TAC
  >- (qpat_assum `?raw. read_result cx raw ee = _ /\ _` mp_tac >>
      Cases_on `p.ptr_location` >>
      gvs[vv_location_def,vv_holds_mods_def,vv_holds_def]) >>
  drule_all abi_encode_saved_slot_restore_mods >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`z`,`Gz`,`tz`,`w`,`root`] (map_every assume_tac o CONJUNCTS))) >>
  qpat_x_assum `src = Var root` kall_tac >>
  qpat_x_assum `lowered_value_type ce e = expr_type e` kall_tac >>
  qexistsl [`z`,`Gz`,`tz`] >> asm_rewrite_tac[] >>
  conj_tac
  >- (irule exprSimPropsTheory.expr_val_at_start_mono >> qexists `ready` >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!aid b len. aid < ready.cs_next_id /\ _ ==> _` (drule_all_then strip_assume_tac) >>
  simp[]
QED

Finalise log_topic_noncode_restore_mods
