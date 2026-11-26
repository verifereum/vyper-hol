(* Re-use the selected argument's capture at the tuple row's unwrap entry. *)
Theory bodyAbiTupleCaptureMods
Ancestors
  bodyAbiTupleBufferStateMods bodyAbiEncodePackedPostMods
  bodyLogSavedValueFrameMods bodyLogSavedMemoryPtrFrameMods
  bodyFullExtCallSavedOperand logValueFramePtr exprSimSubscriptArrayFrame
  exprOperandVar exprSafeOperand
  valueTypingMemoryProps exprLoweringProps stateRelProj
  exprSimMemDefs bodyPtrDefs loweringPosts freshWrites ptrDiscipline
  bodyFullPostsMods bodyFullShadowBodyInv valueEncodingProofs
  compileEnv context venomState pred_set finite_map arithmetic

Theorem tuple_capture_operand_exists[local]:
  vv_holds_mods ce cx ty raw saved ee s ==>
  ?w. eval_operand (vv_operand saved) s = SOME w
Proof
  Cases_on `saved` >> simp[vv_operand_def,vv_holds_mods_def] >-
    (simp[vv_holds_def,expr_val_rel_def] >> metis_tac[]) >>
  IF_CASES_TAC >> simp[vv_holds_def] >> metis_tac[]
QED

Theorem tuple_capture_frame_cut[local]:
  ss.cs_next_var <= se.cs_next_var /\ ss.cs_next_id <= se.cs_next_id /\
  wb_frame ce ee ee se s u /\ ghost_kept_at lo ce ee se G tn s Gu tu ==>
  wb_frame ce ee ee ss s u /\ ghost_kept_at lo ce ee ss G tn s Gu tu
Proof
  simp[wb_frame_def,ghost_kept_at_def] >> strip_tac >>
  `!x. not_fresh_at ss x ==> not_fresh_at se x` by metis_tac[not_fresh_at_mono] >>
  `!aid. aid < ss.cs_next_id ==> aid < se.cs_next_id` by decide_tac >>
  conj_tac
  >- (conj_tac
      >- (rpt strip_tac >> first_x_assum irule >> simp[]) >>
      qx_genl_tac [`aid`,`off`,`sz`] >> strip_tac >>
      qpat_assum `!aid off sz. _ ==> mem_bytes_at _ _ _ = _`
        (qspecl_then [`aid`,`off`,`sz`] mp_tac) >>
      impl_tac >- (asm_rewrite_tac[] >> simp[]) >> simp[]) >>
  conj_tac
  >- (qx_gen_tac `x` >> disch_tac >>
      qpat_assum `!x. not_fresh_at se x ==> _` (qspec_then `x` mp_tac) >> simp[]) >>
  conj_tac
  >- (qx_genl_tac [`aid`,`off`,`sz`,`i`] >> strip_tac >>
      qpat_assum `!aid off sz i. FLOOKUP _ aid = _ /\ _ ==> i IN _`
        (qspecl_then [`aid`,`off`,`sz`,`i`] mp_tac) >>
      impl_tac >- (asm_rewrite_tac[] >> simp[]) >> simp[]) >>
  first_assum ACCEPT_TAC
QED

Theorem tuple_capture_nonmem_ptr[local]:
  p.ptr_location <> LocMemory /\
  ptr_vv_ok cx ty raw (LocatedValue tag p) ee G tn s /\
  eval_operand p.ptr_operand u = eval_operand p.ptr_operand s /\
  op_taint tu p.ptr_operand = op_taint tn p.ptr_operand /\
  op_prov Gu p.ptr_operand = op_prov G p.ptr_operand /\
  u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
  u.vs_call_ctx = s.vs_call_ctx /\ tu.t_stor = tn.t_stor /\ tu.t_trans = tn.t_trans ==>
  ptr_vv_ok cx ty raw (LocatedValue tag p) ee Gu tu u
Proof
  simp[ptr_vv_ok_def] >> strip_tac >> simp[]
QED

Theorem tuple_capture_ctor_memory[local]:
  val_wf rt v /\ w2n w + type_memory_size rt <= lo /\
  mem_bytes_at 0 lo u.vs_memory = mem_bytes_at 0 lo s.vs_memory /\
  (!i. i < lo /\ i IN tu.t_mem ==> i IN tn.t_mem) /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory rt v (w2n w) mem) ==>
  !mem. mem_agree_outside tu.t_mem u.vs_memory mem ==> val_in_memory rt v (w2n w) mem
Proof
  strip_tac >>
  `val_footprint rt v <= type_memory_size rt` by simp[exprSimPropsTheory.val_footprint_le] >>
  gen_tac >> disch_tac >> irule robust_val_in_memory_footprint_frame >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`s.vs_memory`,`u.vs_memory`,`tn.t_mem`,`tu.t_mem`] >> simp[] >>
  sym_tac >> qpat_assum `mem_bytes_at 0 lo _ = _`
    (strip_assume_tac o MATCH_MP mem_bytes_at_agree_window) >>
  first_x_assum irule >> simp[] >> decide_tac
QED

(* The output uses the real reached entry a of the given unwrap interval.
   The raw witness stays under the horizon in the saved-row predicate. *)
Theorem abi_tuple_saved_capture_transport_mods:
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    abi_encode_saved_row_mods lo ce cx origin se e saved v si sm ss vv copy H ee G tn s /\
    stmt_state_rel H ctx func ce cx ee s) /\
  abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix a u Gu tu /\
  (!l. vv_operand saved <> Label l) /\
  unwrap_value ce saved a = (src,c) /\ fn_has_code a c func ==>
  return_buf_frame d ce a u /\ alloca_history func u /\
  ~u.vs_halted /\ u.vs_current_bb = a.cs_current_bb /\
  u.vs_inst_idx = LENGTH a.cs_current_insts /\
  u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
  u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables /\
  u.vs_data_section = s.vs_data_section /\
  tu.t_stor = tn.t_stor /\ tu.t_trans = tn.t_trans /\ tu.t_imm = tn.t_imm /\
  mem_bytes_at 0 lo u.vs_memory = mem_bytes_at 0 lo s.vs_memory /\
  (!i. i < lo /\ i IN tu.t_mem ==> i IN tn.t_mem) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    abi_encode_saved_row_mods lo ce cx origin a e saved v si sm ss vv copy H ee Gu tu u /\
    stmt_state_rel H ctx func ce cx ee u /\ immutable_frame_mods func ce cx ee u /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee Gu tu u /\
    (!x. vv_operand saved = Var x ==> not_fresh_at a x) /\
    eval_operand (vv_operand saved) u = eval_operand (vv_operand saved) s /\
    op_taint tu (vv_operand saved) = op_taint tn (vv_operand saved) /\
    op_prov Gu (vv_operand saved) = op_prov G (vv_operand saved) /\
    safe_operand c src /\
    (vv_location saved = SOME LocCode ==>
      !rt. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt ==>
           value_has_type rt v))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qhdtm_x_assum `abi_tuple_buffer_state_mods`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [abi_tuple_buffer_state_mods_def]) >>
  `mem_bytes_at 0 lo u.vs_memory = mem_bytes_at 0 lo s.vs_memory /\
   (!i. i < lo /\ i IN tu.t_mem ==> i IN tn.t_mem)` by
    (qpat_assum `!b n. ((b = 0 /\ n = lo) \/ _) ==> _`
       (qspecl_then [`0`,`lo`] mp_tac) >> simp[]) >>
  asm_rewrite_tac[] >> qx_gen_tac `H` >> disch_tac >>
  ntac 2 (qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then (map_every assume_tac o CONJUNCTS))) >>
  qhdtm_x_assum `abi_encode_saved_row_mods`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [abi_encode_saved_row_mods_def]) >>
  qpat_x_assum `?raw. read_result _ raw _ = _ /\ _`
    (qx_choose_then `raw` (map_every assume_tac o CONJUNCTS)) >>
  `!x. vv_operand saved = Var x ==> not_fresh_at se x` by
    (gen_tac >> disch_tac >> irule not_fresh_at_mono >> qexists `ss` >> simp[] >>
     irule extcall_saved_operand_not_fresh >>
     goal_assum (drule_at (Pat `compile_snapshot_vv _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >> simp[]) >>
  `(!x. vv_operand saved = Var x ==> FLOOKUP Gu x = FLOOKUP G x) /\
   op_taint tu (vv_operand saved) = op_taint tn (vv_operand saved) /\
   op_prov Gu (vv_operand saved) = op_prov G (vv_operand saved)` by
    (qpat_assum `ghost_kept_at _ _ _ se _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
     Cases_on `vv_operand saved` >> fs[op_taint_def,op_prov_def]) >>
  `eval_operand (vv_operand saved) u = eval_operand (vv_operand saved) s` by
    (drule_then strip_assume_tac tuple_capture_operand_exists >>
     qpat_assum `wb_frame _ _ _ se s u` (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
     Cases_on `vv_operand saved` >> fs[eval_operand_def] >> metis_tac[]) >>
  `!x. vv_operand saved = Var x ==> not_fresh_at a x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists `se` >> simp[]) >>
  `safe_operand c src` by
    (simp[safe_operand_def] >> conj_tac
     >- (drule compiler_unwrap_value_var >> Cases_on `saved` >> fs[vv_operand_def]) >>
     drule_all_then ACCEPT_TAC unwrap_value_not_label) >>
  `(vv_location saved = SOME LocCode ==>
      !rt. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt ==>
           value_has_type rt v)` by
    (Cases_on `saved` >> simp[vv_location_def] >> rpt strip_tac >>
     gvs[vv_holds_mods_def,immutable_holds_mods_def,immutable_holds_def]) >>
  `ss.cs_next_id <= a.cs_next_id /\ sm.cs_next_id <= a.cs_next_id /\
   ss.cs_next_var <= a.cs_next_var /\ sm.cs_next_var <= a.cs_next_var` by decide_tac >>
  `local_ptrs_reserved ce se` by
    (irule local_ptrs_reserved_next_var >> qexists `si` >> simp[] >>
     drule_then strip_assume_tac (cj 1 compile_expr_grows) >> decide_tac) >>
  drule_all_then (map_every assume_tac o CONJUNCTS) log_saved_value_frame_mods >>
  `ptr_vv_ok cx (lowered_value_type ce e) raw saved ee Gu tu u` by suspend "pointer" >>
  `vv_store_bound cx (lowered_value_type ce e) (lowered_value_type ce e) ee raw saved u` by
    (drule_all_then ACCEPT_TAC vv_store_bound_frame_mem_src) >>
  pure_rewrite_tac[abi_encode_saved_row_mods_def] >> asm_rewrite_tac[] >>
  conj_tac >- suspend "copy" >>
  conj_tac >- (qexists `raw` >> asm_rewrite_tac[]) >>
  conj_tac >- suspend "stack_buffer" >>
  conj_tac >- suspend "located_buffer" >>
  suspend "ctor"
QED

Resume abi_tuple_saved_capture_transport_mods[pointer]:
  drule_all_then (map_every assume_tac o CONJUNCTS) tuple_capture_frame_cut >>
  Cases_on `vv_location saved = NONE \/ vv_location saved = SOME LocMemory`
  >- (irule log_saved_memory_ptr_frame >> asm_rewrite_tac[] >>
      conj_tac >- (qexists `v` >> REFL_TAC) >>
      conj_tac
      >- (qpat_x_assum `(?tag op0. saved = StackValue tag op0) \/ _` strip_assume_tac >>
          fs[vv_location_def]) >>
      qpat_assum `ptr_vv_ok _ _ _ _ _ G tn s` (irule_at Any) >>
      qpat_assum `vv_at _ _ _ _ _ _ _ _ s` (irule_at Any) >>
      qpat_assum `ghost_kept_at _ _ _ ss _ _ _ _ _` (irule_at Any) >> simp[]) >>
  Cases_on `saved` >> fs[vv_location_def,vv_operand_def] >>
  qpat_x_assum `LocatedValue _ _ = vv` (SUBST_ALL_TAC o SYM) >>
  gvs[] >> irule tuple_capture_nonmem_ptr >>
  qpat_assum `ptr_vv_ok _ _ _ _ _ G tn s` (irule_at Any) >> simp[]
QED

Resume abi_tuple_saved_capture_transport_mods[copy]:
  disch_tac >>
  qpat_x_assum `copy /\ _ ==> ?p w tv. _` mp_tac >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (qx_choosel_then [`p`,`w`,`tv`] (map_every assume_tac o CONJUNCTS)) >>
  qexistsl [`p`,`w`,`tv`] >> asm_rewrite_tac[] >>
  qpat_assum `wb_frame _ _ _ se s u` (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  `local_region ce ee.scopes s n b sz` suffices_by metis_tac[] >>
  `local_region ce ee.scopes u n b sz <=> local_region ce ee.scopes s n b sz` suffices_by simp[] >>
  irule exprSimSubscriptArrayFrameTheory.local_region_wb_frame >>
  qpat_assum `wb_frame _ _ _ se s u` (irule_at Any) >> simp[] >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >> qexists `func` >> simp[]
QED

Resume abi_tuple_saved_capture_transport_mods[stack_buffer]:
  rpt strip_tac >> irule ptr_buf_ok_frame >>
  qexistsl [`G`,`s`] >> fs[vv_operand_def]
QED

Resume abi_tuple_saved_capture_transport_mods[located_buffer]:
  rpt strip_tac >> irule ptr_buf_ok_frame >>
  qexistsl [`G`,`s`] >> fs[vv_operand_def]
QED

Resume abi_tuple_saved_capture_transport_mods[ctor]:
  disch_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `ce.ce_is_ctor /\ _ ==> _` mp_tac >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (qspecl_then [`rt`,`w`] mp_tac) >>
  asm_simp_tac bool_ss [] >> strip_tac >> asm_rewrite_tac[] >>
  `val_wf rt v` by
    (irule value_has_type_memory_wf >> fs[]) >>
  gen_tac >> disch_tac >> irule tuple_capture_ctor_memory >> asm_rewrite_tac[] >>
  qexistsl [`lo`,`s`,`tn`,`tu`,`u`] >> asm_rewrite_tac[]
QED

Finalise abi_tuple_saved_capture_transport_mods
