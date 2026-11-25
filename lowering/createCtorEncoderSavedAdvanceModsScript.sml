Theory createCtorEncoderSavedAdvanceMods
Ancestors
  createExprSizeExitDefsMods bodyFullExtCallSavedOperand targetPurePostTransport
  bodyFullLogArgs logValueFramePtr bodyPtrBopRepresentationFrame
  bodyPtrIfExpAllocSource bodyPtrBytestringBuiltinsWindowGhost
  exprPtrUnwrapStorageFacts stmtSimAssignStorageCopy accountsRelProps
  stateRelProj exprSimSubscriptArrayFrame exprSimProps exprSimMemDefs
  exprBopSimProps loweringPosts loweringStateRelDefs bodyPtrDefs freshWrites
  bodyFullPostsMods bodyFullShadowBodyInv valueTypingMemoryProps
  valueEncodingProofs valueEncodingDefs exprLoweringProps ptrDiscipline venomState
  vyperStorageBackend vyperStorageFootprint sourceUnitExecution vfmState
  compileEnv context finite_map pred_set words
Libs horizonTypeLib

Theorem saved_operand_frame[local]:
  wb_frame ce ee ee cut s u /\ ghost_kept_at lo ce ee cut G tn s Gu tu /\
  (!x. op = Var x ==> not_fresh_at cut x) /\ (!l. op <> Label l) /\
  (?w. eval_operand op s = SOME w) ==>
  eval_operand op u = eval_operand op s /\
  op_taint tu op = op_taint tn op /\ op_prov Gu op = op_prov G op /\
  (!x. op = Var x ==> FLOOKUP Gu x = FLOOKUP G x)
Proof
  Cases_on `op` >>
  gvs[wb_frame_def, ghost_kept_at_def, eval_operand_def, op_taint_def, op_prov_def] >>
  metis_tac[]
QED

(* The two frames can be restricted to the snapshot endpoint, independently
   of the current cut and the storage horizon. *)
Theorem saved_eval_exists[local]:
  vv_holds_mods ce cx ty raw saved ee s ==> ?w. eval_operand (vv_operand saved) s = SOME w
Proof
  Cases_on `saved` >> simp[vv_holds_mods_def,vv_operand_def]
  >- (simp[vv_holds_def,expr_val_rel_def] >> metis_tac[]) >>
  IF_CASES_TAC >> simp[vv_holds_def] >> metis_tac[]
QED

Theorem saved_snapshot_frames[local]:
  wb_frame ce ee ee se s u /\ ghost_kept_at lo ce ee se G tn s Gu tu /\
  ss.cs_next_id <= se.cs_next_id /\ ss.cs_next_var <= se.cs_next_var ==>
  wb_frame ce ee ee ss s u /\ ghost_kept_at lo ce ee ss G tn s Gu tu
Proof
  strip_tac >>
  `!x. not_fresh_at ss x ==> not_fresh_at se x` by metis_tac[not_fresh_at_mono] >>
  `!aid. aid < ss.cs_next_id ==> aid < se.cs_next_id` by decide_tac >>
  conj_tac
  >- (fs[wb_frame_def] >> rpt strip_tac >> first_assum irule >>
      conj_tac >- first_assum ACCEPT_TAC >> qexists_tac `aid` >> simp[]) >>
  fs[ghost_kept_at_def] >> rpt strip_tac
  >- (qpat_assum `!aid off sz i. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\ _ off sz aid i ==> i IN tn.t_mem`
        (qspecl_then [`aid`,`off`,`sz`,`i`] mp_tac) >>
      simp[] >> disch_then (drule_then ACCEPT_TAC)) >>
  qpat_assum `!n b sz i. local_region ce ee.scopes s n b sz /\ _ b sz i ==> i IN tn.t_mem`
    (drule_all_then ACCEPT_TAC)
QED

Theorem saved_footprint_frame[local]:
  expr_val_at ce cx ty si ss ee v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  eval_operand op s = SOME w /\ wb_frame ce ee ee ss s u /\
  ghost_kept_at lo ce ee ss G tn s Gu tu ==>
  val_wf tv v /\
  mem_bytes_at (w2n w) (val_footprint tv v) u.vs_memory =
    mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory /\
  (!i. w2n w <= i /\ i < w2n w + val_footprint tv v /\ i IN tu.t_mem ==>
    i IN tn.t_mem)
Proof
  strip_tac >> conj_tac >- fs[expr_val_at_def] >>
  reverse conj_tac
  >- (rpt strip_tac >> drule_all pure_argument_taint_kept >> simp[]) >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _`
    (qspec_then `tv` mp_tac o REWRITE_RULE [expr_val_at_def]) >>
  simp[] >> strip_tac >> gvs[]
  >- (`mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz s.vs_memory` by
        (qpat_x_assum `wb_frame _ _ _ _ _ _` mp_tac >>
         simp[wb_frame_def] >> strip_tac >>
         qpat_assum `!a p k. _ ==> mem_bytes_at p k _ = _`
           (qspecl_then [`aid`,`b`,`sz`] mp_tac) >> simp[] >> metis_tac[]) >>
      drule mem_bytes_at_agree_window >> simp[] >> metis_tac[])
  >- (`mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz s.vs_memory` by
        (qpat_x_assum `wb_frame _ _ _ _ _ _` mp_tac >>
         simp[wb_frame_def, locals_kept_def] >> metis_tac[]) >>
      drule mem_bytes_at_agree_window >> simp[] >> metis_tac[]) >>
  simp[mem_bytes_at_def]
QED

Theorem saved_stack_ptr[local]:
  read_result cx raw ee = (INL v,ee) /\
  vv_at ce cx ty si ss ee raw (StackValue tag op) s /\
  ptr_vv_ok cx ty raw (StackValue tag op) ee G tn s /\
  eval_operand op u = eval_operand op s /\
  (!x. op = Var x ==> FLOOKUP Gu x = FLOOKUP G x) /\
  op_taint tu op = op_taint tn op /\
  wb_frame ce ee ee ss s u /\ ghost_kept_at lo ce ee ss G tn s Gu tu ==>
  ptr_vv_ok cx ty raw (StackValue tag op) ee Gu tu u
Proof
  strip_tac >> gvs[ptr_vv_ok_def, vv_at_def] >>
  irule ptr_val_ok_footprint_frame >>
  goal_assum (drule_at (Pat `ptr_val_ok _ _ _ _ _ _ _`)) >> simp[] >>
  rpt gen_tac >> disch_tac >> metis_tac[saved_footprint_frame]
QED

Theorem saved_memory_ptr[local]:
  ~is_word_type ty /\ p.ptr_location = LocMemory /\
  read_result cx raw ee = (INL v,ee) /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  vv_at ce cx ty si ss ee raw (LocatedValue tag p) s /\
  ptr_vv_ok cx ty raw (LocatedValue tag p) ee G tn s /\
  eval_operand p.ptr_operand u = eval_operand p.ptr_operand s /\
  (!x. p.ptr_operand = Var x ==> FLOOKUP Gu x = FLOOKUP G x) /\
  op_taint tu p.ptr_operand = op_taint tn p.ptr_operand /\
  wb_frame ce ee ee ss s u /\ ghost_kept_at lo ce ee ss G tn s Gu tu ==>
  ptr_vv_ok cx ty raw (LocatedValue tag p) ee Gu tu u
Proof
  strip_tac >> drule_all_then assume_tac vv_at_memory_val_at >>
  gvs[ptr_vv_ok_def] >> irule bop_ptr_mem_ok_frame >>
  goal_assum (drule_at (Pat `ptr_mem_ok _ _ _ _ _ _ _`)) >> simp[] >>
  reverse conj_tac >- (fs[expr_val_at_def] >> metis_tac[]) >>
  rpt gen_tac >> disch_tac >> drule_all saved_footprint_frame >> simp[]
QED

(* Only the storage fields of the linked ghost and deadness contracts are
   needed for a delayed slot. Their immutable clauses are not interchangeable. *)
Theorem saved_storage_ptr[local]:
  p.ptr_location = (if tr then LocTransient else LocStorage) /\
  vv_holds ce cx ty raw (LocatedValue ty p) ee u /\
  vv_storage_live H cx (LocatedValue ty p) ee u /\
  stmt_state_rel H ctx func ce cx ee u /\ ghost_inv_at_mods D lo d ce cx ee Gu tu u /\
  dead_lo_ok_mods H D lo ce cx /\ op_taint tu p.ptr_operand = {} ==>
  ptr_vv_ok cx ty raw (LocatedValue ty p) ee Gu tu u
Proof
  strip_tac >>
  `!k b. (k,b) IN (if tr then tu.t_trans else tu.t_stor) ==>
    storage_dead H tr (if tr then contract_transient u else contract_storage u) (w2n k) b` by
    (Cases_on `tr` >>
     gvs[ghost_inv_at_mods_def, stor_taint_ok_at_def, dead_lo_ok_mods_def, cx_dead_def,
         SUBSET_DEF, contract_storage_def, contract_transient_def, lookup_account_def] >>
     rpt strip_tac >> first_x_assum drule >>
     Cases_on `u.vs_call_ctx.cc_address = cx.txn.target` >> simp[]) >>
  drule_then (qspec_then `tr` assume_tac) storage_copy_initial_agree >>
  `!w tv k b. eval_operand p.ptr_operand u = SOME w /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    w2n w <= w2n k /\ w2n k < w2n w + type_slot_size tv /\
    (k,b) IN (if tr then tu.t_trans else tu.t_stor) ==>
    dead_bytes (if tr then contract_transient u else contract_storage u) (w2n w) tv (w2n k) b` by
    (rpt gen_tac >> strip_tac >>
     `storage_range_agree (get_storage cx ee tr)
       (if tr then contract_transient u else contract_storage u) w tv /\
      storage_read_live H tr (get_storage cx ee tr) w tv` by
       (Cases_on `tr` >> gvs[vv_holds_def, storage_holds_def] >> metis_tac[]) >>
     drule storage_agree_storage_dead >> strip_tac >>
     drule storage_range_agree_dead_bytes >> strip_tac >>
     gvs[storage_read_live_def] >> metis_tac[]) >>
  Cases_on `tr` >>
  gvs[ptr_vv_ok_def, contract_storage_def, contract_transient_def, lookup_account_def] >>
  metis_tac[]
QED

Theorem saved_holds_frame[local]:
  vv_holds_mods ce cx ty raw saved ee s /\ vv_at ce cx ty si ss ee raw saved s /\
  wb_frame ce ee ee ss s u /\ eval_operand (vv_operand saved) u = eval_operand (vv_operand saved) s /\
  vv_storage_live (H:(bool # bytes32 # type_value) list # num list) cx saved ee s /\
  stmt_state_rel H ctx func ce cx ee u ==>
  vv_holds_mods ce cx ty raw saved ee u
Proof
  strip_tac >> Cases_on `vv_location saved = SOME LocCode`
  >- (Cases_on `saved` >>
      gvs[vv_location_def, vv_operand_def, vv_holds_mods_def,
          immutable_holds_mods_def, immutable_holds_def] >>
      qexistsl_tac [`src`,`tops`] >> simp[] >>
      qexistsl_tac [`name`,`off`,`itv`,`iv`,`k`] >> simp[]) >>
  `storage_rel H cx.txn.target ee u /\ transient_rel H cx.txn.target ee u` by
    (drule_then (qspec_then `F` assume_tac) storage_copy_initial_agree >>
     drule_then (qspec_then `T` assume_tac) storage_copy_initial_agree >>
     fs[storage_rel_def, transient_rel_def, get_storage_def, lookup_account_def]) >>
  `vv_holds ce cx ty raw saved ee s` by (Cases_on `saved` >> gvs[vv_holds_mods_def,vv_location_def]) >>
  `vv_holds ce cx ty raw saved ee u` by
    (irule (horizonTypeLib.at_horizon_named "H" target_saved_holds_frame) >> qexistsl_tac [`H`,`s`,`si`,`ss`] >> simp[]) >>
  Cases_on `saved` >> gvs[vv_holds_mods_def,vv_location_def]
QED

Theorem saved_ptr_frame[local]:
  ptr_vv_ok cx ty raw saved ee G tn s /\
  vv_at ce cx ty si ss ee raw saved s /\ vv_holds_mods ce cx ty raw saved ee u /\
  read_result cx raw ee = (INL v,ee) /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  (vv_location saved = SOME LocMemory ==> ~is_word_type ty) /\
  (!tag p. saved = LocatedValue tag p ==> tag = ty) /\
  eval_operand (vv_operand saved) u = eval_operand (vv_operand saved) s /\
  op_taint tu (vv_operand saved) = op_taint tn (vv_operand saved) /\
  op_prov Gu (vv_operand saved) = op_prov G (vv_operand saved) /\
  (!x. vv_operand saved = Var x ==> FLOOKUP Gu x = FLOOKUP G x) /\
  wb_frame ce ee ee ss s u /\ ghost_kept_at lo ce ee ss G tn s Gu tu /\
  stmt_state_rel H ctx func ce cx ee u /\ vv_storage_live H cx saved ee u /\
  ghost_inv_at_mods D lo d ce cx ee Gu tu u /\ dead_lo_ok_mods H D lo ce cx ==>
  ptr_vv_ok cx ty raw saved ee Gu tu u
Proof
  strip_tac >> Cases_on `saved` >> fs[vv_operand_def, vv_location_def]
  >- (drule_all saved_stack_ptr >> simp[]) >>
  Cases_on `p.ptr_location` >> gvs[vv_holds_mods_def]
  >- (drule_all saved_memory_ptr >> simp[])
  >- (irule (Q.INST [`tr` |-> `F`] saved_storage_ptr) >> fs[ptr_vv_ok_def] >>
      qexistsl_tac [`D`,`H`,`ce`,`ctx`,`d`,`func`,`lo`] >> fs[ptr_vv_ok_def])
  >- (irule (Q.INST [`tr` |-> `T`] saved_storage_ptr) >> fs[ptr_vv_ok_def] >>
      qexistsl_tac [`D`,`H`,`ce`,`ctx`,`d`,`func`,`lo`] >> fs[ptr_vv_ok_def]) >>
  gvs[ptr_vv_ok_def]
QED

Theorem saved_ctor_read_frame[local]:
  val_wf tv v /\ b + type_memory_size tv <= lo /\
  mem_bytes_at 0 lo u.vs_memory = mem_bytes_at 0 lo s.vs_memory /\
  (!i. i < lo /\ i IN tu.t_mem ==> i IN tn.t_mem) /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv v b mem) /\
  mem_agree_outside tu.t_mem u.vs_memory mem ==>
  val_in_memory tv v b mem
Proof
  strip_tac >>
  `mem_bytes_at b (type_memory_size tv) u.vs_memory =
   mem_bytes_at b (type_memory_size tv) s.vs_memory` by
    (drule mem_bytes_at_agree_window >> simp[]) >>
  `!i. b <= i /\ i < b + type_memory_size tv /\ i IN tu.t_mem ==> i IN tn.t_mem` by
    (rpt strip_tac >> `i < lo` by decide_tac >> simp[]) >>
  `val_footprint tv v <= type_memory_size tv` by simp[val_footprint_le] >>
  mp_tac (Q.INST [`len` |-> `type_memory_size tv`, `mem` |-> `s.vs_memory`,
    `mem'` |-> `u.vs_memory`, `dirty` |-> `tn.t_mem`, `dirty'` |-> `tu.t_mem`]
    robust_val_in_memory_window_transport) >> simp[]
QED

(* Advance the same saved value and the same allocation interval. Only the
   constructor-code arm inspects the preserved low memory window. *)
Theorem ctor_encoder_saved_advance_mods:
  compile_expr ce (expr_type e) e si = (vv,sm) /\
  compile_snapshot_vv ce copy (ext_call_arg_value ty vv) sm = (saved,ss) /\
  local_ptrs_reserved ce si /\ local_ptrs_reserved ce se /\
  ss.cs_next_var <= se.cs_next_var /\ ss.cs_next_id <= se.cs_next_id /\
  (!l. vv_operand saved <> Label l) /\
  (vv_location saved = SOME LocMemory ==> ~is_word_type ty) /\
  (!tag p. saved = LocatedValue tag p ==> tag = ty) /\
  read_result cx raw ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  vv_holds_mods ce cx ty raw saved ee s /\ vv_at ce cx ty si ss ee raw saved s /\
  ptr_vv_ok cx ty raw saved ee G tn s /\ vv_store_bound cx ty ty ee raw saved s /\
  ((case saved of StackValue tag op => ~is_word_type ty
      | LocatedValue tag p => p.ptr_location = LocMemory) ==>
    ptr_buf_ok ce e (vv_operand saved) G s) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee s /\ vv_storage_live H cx saved ee s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. dead_lo_ok_mods H (DF H) lo ce cx) /\
  abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix su u Gu tu /\
  (ce.ce_is_ctor /\ vv_location saved = SOME LocCode ==>
    mem_bytes_at 0 lo u.vs_memory = mem_bytes_at 0 lo s.vs_memory /\
    (!i. i < lo /\ i IN tu.t_mem ==> i IN tn.t_mem) /\
    !w. eval_operand (vv_operand saved) s = SOME w ==>
      w2n w + type_memory_size tv <= lo /\
      (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
        val_in_memory tv v (w2n w) mem)) ==>
  vv_holds_mods ce cx ty raw saved ee u /\ vv_at ce cx ty si ss ee raw saved u /\
  ptr_vv_ok cx ty raw saved ee Gu tu u /\ vv_store_bound cx ty ty ee raw saved u /\
  ((case saved of StackValue tag op => ~is_word_type ty
      | LocatedValue tag p => p.ptr_location = LocMemory) ==>
    ptr_buf_ok ce e (vv_operand saved) Gu u) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee u /\ immutable_frame_mods func ce cx ee u /\
    storage_well_formed_on cx ee (FST H) /\
    vv_storage_live H cx saved ee u /\ ghost_inv_at_mods (DF H) lo d ce cx ee Gu tu u) /\
  (!x. vv_operand saved = Var x ==> not_fresh_at su x) /\
  (ce.ce_is_ctor /\ vv_location saved = SOME LocCode ==>
    !w. eval_operand (vv_operand saved) u = SOME w ==>
      w2n w + type_memory_size tv <= lo /\
      (!mem. mem_agree_outside tu.t_mem u.vs_memory mem ==>
        val_in_memory tv v (w2n w) mem))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encode_saved_state_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encode_saved_state_mods_def]) >>
  qpat_x_assum `?H. valid_horizon cx st0 H ee.storage_trace`
    (qx_choose_then `hz` assume_tac) >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H _ _ _ _ _ s /\ _`
    (qspec_then `hz` (drule_then strip_assume_tac)) >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H _ _ _ _ _ u /\ _`
    (qspec_then `hz` (drule_then strip_assume_tac)) >>
  `!x. vv_operand saved = Var x ==> not_fresh_at ss x` by
    metis_tac[extcall_saved_operand_not_fresh] >>
  `!x. vv_operand saved = Var x ==> not_fresh_at se x` by metis_tac[not_fresh_at_mono] >>
  `!x. vv_operand saved = Var x ==> not_fresh_at su x` by metis_tac[not_fresh_at_mono] >>
  `?w. eval_operand (vv_operand saved) s = SOME w` by
    (drule_then ACCEPT_TAC saved_eval_exists) >>
  `eval_operand (vv_operand saved) u = eval_operand (vv_operand saved) s /\
   op_taint tu (vv_operand saved) = op_taint tn (vv_operand saved) /\
   op_prov Gu (vv_operand saved) = op_prov G (vv_operand saved) /\
   (!x. vv_operand saved = Var x ==> FLOOKUP Gu x = FLOOKUP G x)` by
    (irule saved_operand_frame >> simp[] >>
     qpat_assum `wb_frame ce ee ee se s u` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo ce ee se G tn s Gu tu` (irule_at Any) >> simp[]) >>
  `wb_frame ce ee ee ss s u /\ ghost_kept_at lo ce ee ss G tn s Gu tu` by
    (irule saved_snapshot_frames >> qexists_tac `se` >> simp[]) >>
  `vv_holds_mods ce cx ty raw saved ee u` by
    (irule saved_holds_frame >> qexistsl_tac [`hz`,`ctx`,`func`,`s`,`si`,`ss`] >> simp[]) >>
  `vv_at ce cx ty si ss ee raw saved u` by
    (qpat_assum `stmt_state_rel hz ctx func ce cx ee s`
       (mp_then Any strip_assume_tac stmt_state_rel_local_ptrs_alloca) >>
     irule vv_at_alloc_map_frame >> qexistsl_tac [`s`,`ss`] >> simp[] >>
     conj_tac >- metis_tac[local_region_wb_frame] >> fs[wb_frame_def]) >>
  `!H:(bool # bytes32 # type_value) list # num list.
     vv_storage_live H cx saved ee s ==> vv_storage_live H cx saved ee u` by
    (rpt strip_tac >> irule target_saved_storage_live_frame >> qexists_tac `s` >> simp[]) >>
  `dead_lo_ok_mods hz (DF hz) lo ce cx` by simp[] >>
  `vv_storage_live hz cx saved ee u` by simp[] >>
  `ptr_vv_ok cx ty raw saved ee Gu tu u` by
    (drule_all_then ACCEPT_TAC saved_ptr_frame) >>
  simp[] >> rpt conj_tac
  >- metis_tac[vv_store_bound_frame_mem_src]
  >- (disch_tac >> irule ptr_buf_ok_frame >> qexistsl_tac [`G`,`s`] >> simp[]) >>
  strip_tac >>
  qpat_assum `ce.ce_is_ctor /\ vv_location saved = SOME LocCode ==> _` mp_tac >>
  impl_tac >- simp[] >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (drule_then strip_assume_tac))) >>
  `val_wf tv v` by metis_tac[value_has_type_memory_wf] >>
  gen_tac >> disch_tac >> irule saved_ctor_read_frame >>
  qpat_assum `mem_agree_outside tu.t_mem u.vs_memory mem` (irule_at Any) >>
  qpat_assum `mem_bytes_at 0 lo u.vs_memory = _` (irule_at Any) >>
  qexists_tac `tn` >> simp[]
QED
