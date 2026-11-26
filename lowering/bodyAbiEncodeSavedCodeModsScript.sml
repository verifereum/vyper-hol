(* Restore a saved code operand at the reached ABI payload cursor. *)
Theory bodyAbiEncodeSavedCodeMods
Ancestors
  bodyAbiEncodePackedPostMods bodyCopyMaterializedRhsPostMods
  bodyCopyCtorRhsRunMods bodyCopyRuntimeRhsRunMods bodyLocalCopyPhysicalRhsMods
  exprOperandVar exprLoweringProps freshWrites exprSimProps stateRelProj
  bodyFullHashKeccakFixed[qualified,ignore_grammar] wordArgsPtr
  valueTypingMemoryProps valueEncodingProps valueEncodingDefs loweringPosts
  bodyPtrDefs bodyFullPostsMods bodyFullShadowBodyInv exprSimMemDefs
  exprSimCopy exprSimStorageCopy fragGasOriginPtr vyperInterpreter vyperStorageFootprint
  compileEnv context vyperState venomState venomInst ptrDiscipline
  loweringStateRelDefs memoryReadProps venomMemDefs[qualified]
  words finite_map arithmetic

(* Use the value of the current read, not the raw result of the earlier
   evaluation. In particular the code pointer need not denote a place. *)
Theorem saved_code_value_holds[local]:
  vv_holds_mods ce cx ty raw (LocatedValue ty p) ee s /\
  p.ptr_location = LocCode /\ read_result cx raw ee = (INL v,ee) ==>
  vv_holds_mods ce cx ty (Value v) (LocatedValue ty p) ee s
Proof
  simp[vv_holds_mods_def, immutable_holds_mods_def, immutable_holds_def] >>
  strip_tac >> gvs[] >>
  qexistsl [`src`,`tops`] >> conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`name`,`off`,`itv`,`iv`,`k`,`v`] >> simp[read_result_def,return_def]
QED

Theorem saved_code_row_at_cursor[local]:
  abi_encode_saved_row_mods lo ce cx origin ready e saved v si sm ss vv copy H ee G tn s /\
  saved = LocatedValue ty p /\ p.ptr_location = LocCode /\
  stmt_state_rel H ctx func ce cx ee s /\ immutable_frame_mods func ce cx ee s /\
  storage_well_formed_on cx ee (FST H) ==>
  ty = lowered_value_type ce e /\ ty = expr_type e /\
  post_value_type ce e = ty /\ ~is_word_type ty /\
  local_ptrs_reserved ce ready /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at ready x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at ready x) /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at ready x) /\
  ptr_vv_ok cx ty (Value v) saved ee G tn s /\
  vv_post_mods H ctx func ce cx e ee ready ready s ee (Value v) saved s /\
  (ce.ce_is_ctor ==> !rt w.
     evaluate_type (get_tenv cx) ty = SOME rt /\ eval_operand p.ptr_operand s = SOME w ==>
     w2n w + type_memory_size rt <= lo /\
     !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory rt v (w2n w) mem)
Proof
  strip_tac >>
  qpat_x_assum `abi_encode_saved_row_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encode_saved_row_mods_def]) >>
  gvs[] >>
  `post_value_type ce e = expr_type e` by simp[post_value_type_lowered] >>
  drule_then strip_assume_tac (cj 1 compile_expr_grows) >>
  `si.cs_next_var <= ready.cs_next_var` by decide_tac >>
  `local_ptrs_reserved ce ready` by
    (irule local_ptrs_reserved_next_var >> qexists `si` >> simp[]) >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at ready x` by
    (drule_at (Pat `compile_expr _ _ _ _ = _`) (cj 1 compiler_compile_var) >>
     simp[vv_operand_def] >> metis_tac[not_fresh_at_mono]) >>
  drule_all_then assume_tac saved_code_value_holds >>
  simp[vv_post_mods_def, vv_place_ptr_mods_def, vv_place_ptr_def, vv_at_def,
       ptr_vv_ok_def, vv_location_def, vv_operand_def, slot_loc_def] >>
  qhdtm_assum `ptr_vv_ok` (strip_assume_tac o REWRITE_RULE [ptr_vv_ok_def]) >> simp[] >>
  conj_tac >> rpt strip_tac >> irule not_fresh_at_mono >> qexists `si` >> simp[]
QED

Theorem saved_code_nonwrap[local]:
  immutable_holds ce cx ty raw w ee s /\ evaluate_type (get_tenv cx) ty = SOME rt ==>
  w2n w + type_memory_size rt < dimword (:256)
Proof
  rw[immutable_holds_def,sub_layout_def] >>
  `off + k < dimword (:256)` by decide_tac >>
  `rt = tvt` by fs[] >> simp[w2n_n2w,LESS_MOD] >> decide_tac
QED

(* Keep the allocation certificate from the same run for linked frame
   transport; a reused site need not be at the incoming frontier. *)
val code_copy_effects = ``
  src = Var root /\ eval_operand src z = SOME w /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gz,tz)) /\
  ~z.vs_halted /\ z.vs_current_bb = u.cs_current_bb /\
  z.vs_inst_idx = LENGTH u.cs_current_insts /\ alloca_history func z /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\ allocas_from lo z /\
  s.vs_alloca_next <= z.vs_alloca_next /\ lo <= w2n w /\
  w2n w + type_memory_size rt <= z.vs_alloca_next /\
  w2n w + type_memory_size rt < dimword (:256) /\
  ready.cs_next_id < u.cs_next_id /\ ready.cs_next_var < u.cs_next_var /\
  root = STRING #"%" (toString ready.cs_next_var) /\
  MEM (mk_inst ready.cs_next_id ALLOCA [Lit (n2w (type_memory_size rt))] [root]) (fn_insts func) /\
  exec_alloca (mk_inst ready.cs_next_id ALLOCA [Lit (n2w (type_memory_size rt))] [root])
    s (n2w (type_memory_size rt) : bytes32) = OK a /\
  FLOOKUP a.vs_allocas ready.cs_next_id = SOME (w2n w,type_memory_size rt) /\
  FLOOKUP z.vs_allocas ready.cs_next_id = SOME (w2n w,type_memory_size rt) /\
  copy_static z = copy_static a /\ LENGTH s.vs_memory <= LENGTH z.vs_memory /\
  (!x. not_fresh_at ready x ==> lookup_var x z = lookup_var x s /\
    FLOOKUP Gz x = FLOOKUP G x /\ op_taint tz (Var x) = op_taint tn (Var x)) /\
  (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP z.vs_allocas aid = SOME b) /\
  (!aid b len. aid < ready.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
     regions_disjoint (w2n w) (type_memory_size rt) b len) /\
  (!name b len. local_region ce ee.scopes s name b len ==>
     b+len <= w2n w \/ w2n w+type_memory_size rt <= b) /\
  (!off len. off+len <= w2n w \/ w2n w+type_memory_size rt <= off ==>
     mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
  (!j. j < w2n w \/ w2n w+type_memory_size rt <= j ==> j IN tz.t_mem ==> j IN tn.t_mem) /\
  z.vs_accounts = s.vs_accounts /\ z.vs_transient = s.vs_transient /\
  z.vs_call_ctx = s.vs_call_ctx /\ z.vs_immutables = s.vs_immutables /\
  z.vs_data_section = s.vs_data_section /\
  tz.t_stor = tn.t_stor /\ tz.t_trans = tn.t_trans /\ tz.t_imm = tn.t_imm /\
  ptr_covers Gz tz root z (type_memory_size rt) /\
  (!mem. mem_agree_outside tz.t_mem z.vs_memory mem ==> val_in_memory rt v (w2n w) mem)``;

Theorem saved_code_copy_run[local]:
  unwrap_value ce (LocatedValue ty p) ready = (src,u) /\ p.ptr_location = LocCode /\
  fn_has_code ready u func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce ready /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at ready x) /\
  ~is_word_type ty /\ type_memory_bytes ce ty = type_memory_size rt /\ val_wf rt v /\
  eval_operand p.ptr_operand s = SOME q /\ op_taint tn p.ptr_operand = {} /\
  op_prov G p.ptr_operand = NONE /\ w2n q + type_memory_size rt < dimword (:256) /\
  (ce.ce_is_ctor ==> w2n q + type_memory_size rt <= lo /\
     !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory rt v (w2n q) mem) /\
  (~ce.ce_is_ctor ==> val_in_memory rt v (w2n q) s.vs_data_section /\
     w2n q + type_memory_size rt <= LENGTH s.vs_data_section) /\
  stmt_state_rel H ctx func ce cx ee s /\ ghost_inv_at_mods DH lo d ce cx ee G tn s /\
  alloca_history func s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = ready.cs_current_bb /\
  s.vs_inst_idx = LENGTH ready.cs_current_insts ==>
  ?z Gz tz root w a. ^code_copy_effects
Proof
  strip_tac >> Cases_on `ce.ce_is_ctor`
  >- (
    `type_memory_size rt < dimword (:256)` by decide_tac >>
    qpat_assum `ce.ce_is_ctor ==> _` (drule_then strip_assume_tac) >>
    drule_all copy_ctor_rhs_endpoint_mods >>
    disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
    qexistsl [`z`,`Gf`,`tnf`,`root`,`dst`,`u'`] >> asm_rewrite_tac[] >>
    rpt strip_tac >>
    qpat_assum `!i. _ ==> (i IN tnf.t_mem <=> _)` (qspec_then `j` mp_tac) >> simp[]) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  qpat_assum `~ce.ce_is_ctor ==> _` (drule_then strip_assume_tac) >>
  drule_all copy_runtime_rhs_endpoint_mods >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`] strip_assume_tac) >>
  qexistsl [`z`,`Gf`,`tf`,`root`,`dst`,`u'`] >> asm_rewrite_tac[] >> simp[] >>
  rpt strip_tac >> qpat_assum `!nm b len. local_region _ _ s nm b len ==> _`
    (drule_then mp_tac) >> decide_tac
QED

Theorem saved_code_frame_at_horizon[local]:
  ^code_copy_effects /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce ready /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at ready x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at ready x) /\
  vv_post_mods H ctx func ce cx e ee ready ready s ee (Value v) saved s /\
  ghost_inv_at_mods DH lo d ce cx ee G tn s /\
  ~is_word_type ty /\ post_value_type ce e = ty /\ lowered_value_type ce e = ty /\
  evaluate_type (get_tenv cx) ty = SOME rt /\ val_wf rt v /\
  type_memory_bytes ce ty = type_memory_size rt ==>
  expr_post_mods H ctx func ce cx e ee ready u s ee v src z /\
  ghost_inv_at_mods DH lo d ce cx ee Gz tz z /\ ptr_val_ok cx ty v src Gz tz z /\
  ptr_buf_ok ce e src Gz z /\ expr_store_bound cx ty v src z /\
  not_fresh_at u root /\ wb_frame ce ee ee ready s z /\
  ghost_kept_at lo ce ee ready G tn s Gz tz /\
  (!x cap. not_fresh_at ready x /\ ptr_covers G tn x s cap ==> ptr_covers Gz tz x z cap)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `type_memory_size rt < dimword (:256)` by decide_tac >>
  `ghost_kept_at lo ce ee ready G tn s G tn` by simp[ghost_kept_at_refl] >>
  qpat_x_assum `src = Var root` SUBST_ALL_TAC >>
  drule_at (Pat `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    copy_materialized_rhs_post_mods >>
  disch_then (drule_at (Pat `exec_alloca _ _ _ = _`)) >>
  disch_then (drule_at (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  disch_then (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`v`,`u`,`rt`] mp_tac) >>
  asm_rewrite_tac[LESS_EQ_REFL] >> simp[]
QED

val code_restore_post = ``
  expr_post_mods (H:(bool # bytes32 # type_value) list # num list)
    ctx func ce cx e ee ready u s ee v src z /\
  ghost_inv_at_mods (DF H) lo d ce cx ee Gz tz z /\ ptr_val_ok cx ty v src Gz tz z /\
  ptr_buf_ok ce e src Gz z /\ expr_store_bound cx ty v src z /\
  not_fresh_at u root /\ wb_frame ce ee ee ready s z /\
  ghost_kept_at lo ce ee ready G tn s Gz tz /\
  (!x cap. not_fresh_at ready x /\ ptr_covers G tn x s cap ==> ptr_covers Gz tz x z cap)``;

Theorem saved_code_copy_pure[local]:
  ^code_copy_effects ==> pure_frame ce func ee ready s z
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rw[pure_frame_def] >>
  qpat_assum `!off len. _ ==> mem_bytes_at off len z.vs_memory = _` irule
  >- (qpat_assum `!nm b len. local_region _ _ s nm b len ==> _` (drule_then mp_tac) >>
      decide_tac) >>
  first_x_assum (drule_then mp_tac) >> simp[mk_inst_def,regions_disjoint_def]
QED

Theorem saved_code_copy_selector[local]:
  (!aid b n. aid < ready.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,n) ==>
     regions_disjoint (w2n w) (type_memory_size rt) b n) /\
  (!aid row. FLOOKUP s.vs_allocas aid = SOME row ==> FLOOKUP z.vs_allocas aid = SOME row) /\
  (!off len. off+len <= w2n w \/ w2n w+type_memory_size rt <= off ==>
     mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
  (!j. j < w2n w \/ w2n w+type_memory_size rt <= j ==> j IN tz.t_mem ==> j IN tn.t_mem) /\
  aid < ready.cs_next_id /\
  FLOOKUP s.vs_allocas aid = SOME (b,n) /\ 32+k <= n /\
  read_memory (b+32) k s = prefix /\
  (!i. b+32 <= i /\ i < b+32+k ==> i NOTIN tn.t_mem) ==>
  regions_disjoint (w2n w) (type_memory_size rt) b n /\
  FLOOKUP z.vs_allocas aid = SOME (b,n) /\
  read_memory (b+32) k z = prefix /\
  (!i. b+32 <= i /\ i < b+32+k ==> i NOTIN tz.t_mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `regions_disjoint (w2n w) (type_memory_size rt) b n` by
    (qpat_assum `!id b len. _ ==> regions_disjoint _ _ b len` (drule_all_then ACCEPT_TAC)) >>
  `b+n <= w2n w \/ w2n w + type_memory_size rt <= b` by fs[regions_disjoint_def] >>
  `mem_bytes_at (b+32) k z.vs_memory = mem_bytes_at (b+32) k s.vs_memory` by
    (qpat_assum `!off len. _ ==> mem_bytes_at off len z.vs_memory = _` irule >> decide_tac) >>
  `read_memory (b+32) k z = prefix` by
    (qpat_assum `read_memory _ _ s = _` mp_tac >>
     pure_rewrite_tac[read_memory_eq_mem_bytes_at] >> simp[]) >>
  `FLOOKUP z.vs_allocas aid = SOME (b,n)` by
    (qpat_assum `!id entry. FLOOKUP s.vs_allocas id = _ ==> _` (drule_then ACCEPT_TAC)) >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  `i < w2n w \/ w2n w+type_memory_size rt <= i` by decide_tac >>
  qpat_assum `!j. _ ==> j IN tz.t_mem ==> j IN tn.t_mem` (qspec_then `i` mp_tac) >>
  qpat_assum `!i. b+32 <= _ /\ _ ==> i NOTIN tn.t_mem` (qspec_then `i` mp_tac) >> simp[]
QED

(* The chosen run is independent of the storage horizon. Registering its
   actual copy allocation keeps the selector safe even on a reused site. *)

val code_restore_pre = ``
  saved = LocatedValue ty p /\ p.ptr_location = LocCode /\
  unwrap_value ce saved ready = (src,u) /\ fn_has_code ready u func /\
  fn_inst_ids_distinct func /\
  evaluate_type (get_tenv cx) ty = SOME rt /\ value_has_type rt v /\
  type_memory_bytes ce ty = type_memory_size rt /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    abi_encode_saved_row_mods lo ce cx origin ready e saved v si sm ss vv copy H ee G tn s /\
    stmt_state_rel H ctx func ce cx ee s /\ immutable_frame_mods func ce cx ee s /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  return_buf_frame d ce ready s /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = ready.cs_current_bb /\
  s.vs_inst_idx = LENGTH ready.cs_current_insts``;

val code_restore_core_result = ``
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gz,tz)) /\
    ~z.vs_halted /\ z.vs_current_bb = u.cs_current_bb /\
    z.vs_inst_idx = LENGTH u.cs_current_insts /\ alloca_history func z /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    allocas_from lo z /\ lo <= w2n w /\ s.vs_alloca_next <= z.vs_alloca_next /\
    w2n w + type_memory_size rt <= z.vs_alloca_next /\
    w2n w + type_memory_size rt < dimword (:256) /\
    src = Var root /\ eval_operand src z = SOME w /\ not_fresh_at u root /\
    ptr_covers Gz tz root z (type_memory_size rt) /\ op_taint tz src = {} /\
    FLOOKUP z.vs_allocas ready.cs_next_id = SOME (w2n w,type_memory_size rt) /\
    ready.cs_next_id < u.cs_next_id /\ ready.cs_next_var <= u.cs_next_var /\
    (!mem. mem_agree_outside tz.t_mem z.vs_memory mem ==>
      val_in_memory rt v (w2n w) mem) /\
    expr_val_rel cx ty v src z /\ expr_val_at ce cx ty ready u ee v src z /\
    ptr_val_ok cx ty v src Gz tz z /\ ptr_buf_ok ce e src Gz z /\
    expr_store_bound cx ty v src z /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func ce cx ee z /\ immutable_frame_mods func ce cx ee z /\
       storage_well_formed_on cx ee (FST H) /\
       ghost_inv_at_mods (DF H) lo d ce cx ee Gz tz z) /\
    pure_frame ce func ee ready s z /\ wb_frame ce ee ee ready s z /\
    return_buf_frame d ce u z /\ ghost_kept_at lo ce ee ready G tn s Gz tz /\
    (!x. not_fresh_at ready x ==> lookup_var x z = lookup_var x s /\
      FLOOKUP Gz x = FLOOKUP G x /\ op_taint tz (Var x) = op_taint tn (Var x)) /\
    (!x cap. not_fresh_at ready x /\ ptr_covers G tn x s cap ==>
      ptr_covers Gz tz x z cap) /\
    (!id a. FLOOKUP s.vs_allocas id = SOME a ==>
      FLOOKUP z.vs_allocas id = SOME a) /\
    (!aid b len. aid < ready.cs_next_id /\
      FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
      regions_disjoint (w2n w) (type_memory_size rt) b len) /\
    (!off len. off+len <= w2n w \/ w2n w+type_memory_size rt <= off ==>
      mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
    (!j. j < w2n w \/ w2n w+type_memory_size rt <= j ==>
      j IN tz.t_mem ==> j IN tn.t_mem) /\
    z.vs_accounts = s.vs_accounts /\ z.vs_transient = s.vs_transient /\
    z.vs_call_ctx = s.vs_call_ctx /\ z.vs_immutables = s.vs_immutables /\
    z.vs_data_section = s.vs_data_section /\
    tz.t_stor = tn.t_stor /\ tz.t_trans = tn.t_trans /\ tz.t_imm = tn.t_imm``;

Theorem abi_encode_saved_code_restore_packet_mods:
  ^code_restore_pre ==>
  ?z Gz tz root w a.
    ^code_restore_core_result /\
    ready.cs_next_var < u.cs_next_var /\
    root = STRING #"%" (toString ready.cs_next_var) /\
    MEM (mk_inst ready.cs_next_id ALLOCA [Lit (n2w (type_memory_size rt))] [root]) (fn_insts func) /\
    exec_alloca (mk_inst ready.cs_next_id ALLOCA [Lit (n2w (type_memory_size rt))] [root])
      s (n2w (type_memory_size rt) : bytes32) = OK a /\
    FLOOKUP a.vs_allocas ready.cs_next_id = SOME (w2n w,type_memory_size rt) /\
    copy_static z = copy_static a /\ LENGTH s.vs_memory <= LENGTH z.vs_memory /\
    (!name b len. local_region ce ee.scopes s name b len ==>
       b+len <= w2n w \/ w2n w+type_memory_size rt <= b)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by fs[Abbr `H0`,storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  qpat_assum `saved = LocatedValue _ _` SUBST_ALL_TAC >>
  drule_all saved_code_row_at_cursor >> strip_tac >>
  qpat_x_assum `ty = expr_type e` kall_tac >>
  qpat_x_assum `ty = lowered_value_type ce e` (assume_tac o SYM) >>
  `read_result cx (Value v) ee = (INL v,ee)` by simp[read_result_def,return_def] >>
  `ce.ce_is_ctor ==> ?val. read_result cx (Value v) ee = (INL val,ee) /\
    !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
      eval_operand p.ptr_operand s = SOME w ==>
      w2n w + type_memory_size rt <= lo /\
      !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
        val_in_memory rt val (w2n w) mem` by
    (strip_tac >> qexists `v` >>
     qpat_assum `ce.ce_is_ctor ==> !rt w. _` (drule_then mp_tac) >> asm_rewrite_tac[]) >>
  qhdtm_assum `vv_post_mods` (mp_then Any mp_tac local_copy_raw_code_source_mods) >>
  disch_then (qspecl_then [`v`,`tn`,`rt`,`lo`,`G`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[]])) >>
  disch_then (CONJUNCTS_THEN2 kall_tac (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac
      (qx_choosel_then [`owner`,`tops`,`q`] (map_every assume_tac o CONJUNCTS))))) >>
  drule_all_then assume_tac saved_code_nonwrap >>
  `val_wf rt v` by simp[value_has_type_memory_wf] >>
  drule_then assume_tac bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >>
  drule_all saved_code_copy_run >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`z`,`Gz`,`tz`,`root`,`w`,`a`] assume_tac)) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> ^code_restore_post` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
     drule_all saved_code_row_at_cursor >> strip_tac >>
     rpt (qpat_x_assum `ty = expr_type e` kall_tac) >>
     rpt (qpat_x_assum `ty = lowered_value_type ce e` kall_tac) >>
     qpat_x_assum `^code_copy_effects` (map_every assume_tac o CONJUNCTS) >>
     qpat_x_assum `root = STRING _ _` SUBST_ALL_TAC >>
     irule saved_code_frame_at_horizon >> asm_rewrite_tac[] >>
     conj_tac >- (qexistsl [`PG`,`explicit`] >> first_assum ACCEPT_TAC) >>
     conj_tac >- (qexistsl [`a`,`rt`,`w`] >> asm_rewrite_tac[]) >>
     goal_assum (drule_at Any)) >>
  `pure_frame ce func ee ready s z` by
    (qpat_assum `^code_copy_effects` (ACCEPT_TAC o MATCH_MP saved_code_copy_pure)) >>
  qpat_assum `^code_copy_effects` (map_every assume_tac o CONJUNCTS) >>
  `return_buf_frame d ce u z` by
    (Cases_on `d` >- fs[return_buf_frame_def] >>
     rename1 `return_buf_frame (SOME ret) ce ready s` >> PairCases_on `ret` >>
     fs[return_buf_frame_def] >>
     irule not_fresh_at_mono >> qexists `ready` >> simp[LESS_IMP_LESS_OR_EQ]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (qspec_then `H0` (drule_then strip_assume_tac)) >>
  qhdtm_x_assum `expr_post_mods` (strip_assume_tac o REWRITE_RULE [expr_post_mods_def,expr_post_def]) >>
  `op_taint tz src = {}` by
    (qpat_assum `src = Var root` SUBST1_TAC >> fs[ptr_covers_def]) >>
  qexistsl [`z`,`Gz`,`tz`,`root`,`w`,`a`] >> asm_rewrite_tac[LESS_IMP_LESS_OR_EQ] >>
  conj_tac >-
    (qpat_assum `ready.cs_next_var < u.cs_next_var` mp_tac >> simp[]) >>
  conj_tac >-
    (qpat_assum `expr_val_rel cx (post_value_type ce e) v src z`
       (fn th =>
          qpat_assum `post_value_type ce e = ty` (fn pty =>
            qpat_assum `src = Var root` (fn sr =>
              qpat_assum `root = _` (fn rr =>
                ACCEPT_TAC (REWRITE_RULE [pty,sr,rr] th))))) ) >>
  conj_tac >-
    (qpat_assum `expr_val_at ce cx (post_value_type ce e) ready u ee v src z`
       (fn th =>
          qpat_assum `post_value_type ce e = ty` (fn pty =>
            qpat_assum `src = Var root` (fn sr =>
              qpat_assum `root = _` (fn rr =>
                ACCEPT_TAC (REWRITE_RULE [pty,sr,rr] th))))) ) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  fs[expr_post_mods_def,expr_post_def]
QED

Theorem abi_encode_saved_code_restore_core_mods:
  ^code_restore_pre ==>
  ?z Gz tz root w. ^code_restore_core_result
Proof
  disch_then (qx_choosel_then [`z`,`Gz`,`tz`,`root`,`w`,`a`]
    (CONJUNCTS_THEN2 assume_tac kall_tac) o
    MATCH_MP abi_encode_saved_code_restore_packet_mods) >>
  qexistsl [`z`,`Gz`,`tz`,`root`,`w`] >> first_assum ACCEPT_TAC
QED

Theorem abi_encode_saved_code_restore_mods:
  saved = LocatedValue ty p /\ p.ptr_location = LocCode /\
  unwrap_value ce saved ready = (src,u) /\ fn_has_code ready u func /\
  fn_inst_ids_distinct func /\
  evaluate_type (get_tenv cx) ty = SOME rt /\ value_has_type rt v /\
  type_memory_bytes ce ty = type_memory_size rt /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    abi_encode_saved_row_mods lo ce cx origin ready e saved v si sm ss vv copy H ee G tn s /\
    stmt_state_rel H ctx func ce cx ee s /\ immutable_frame_mods func ce cx ee s /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  return_buf_frame d ce ready s /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = ready.cs_current_bb /\
  s.vs_inst_idx = LENGTH ready.cs_current_insts /\
  aid < ready.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,n) /\ 32+k <= n /\
  read_memory (b+32) k s = prefix /\
  (!i. b+32 <= i /\ i < b+32+k ==> i NOTIN tn.t_mem) ==>
  ?z Gz tz root w.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gz,tz)) /\
    ~z.vs_halted /\ z.vs_current_bb = u.cs_current_bb /\ z.vs_inst_idx = LENGTH u.cs_current_insts /\
    alloca_history func z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    allocas_from lo z /\ lo <= w2n w /\ s.vs_alloca_next <= z.vs_alloca_next /\
    w2n w + type_memory_size rt <= z.vs_alloca_next /\
    w2n w + type_memory_size rt < dimword (:256) /\
    src = Var root /\ eval_operand src z = SOME w /\ not_fresh_at u root /\
    ptr_covers Gz tz root z (type_memory_size rt) /\ op_taint tz src = {} /\
    FLOOKUP z.vs_allocas ready.cs_next_id = SOME (w2n w,type_memory_size rt) /\
    ready.cs_next_id < u.cs_next_id /\ ready.cs_next_var <= u.cs_next_var /\
    (!mem. mem_agree_outside tz.t_mem z.vs_memory mem ==> val_in_memory rt v (w2n w) mem) /\
    expr_val_rel cx ty v src z /\ expr_val_at ce cx ty ready u ee v src z /\
    ptr_val_ok cx ty v src Gz tz z /\ ptr_buf_ok ce e src Gz z /\ expr_store_bound cx ty v src z /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func ce cx ee z /\ immutable_frame_mods func ce cx ee z /\
       storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee Gz tz z) /\
    pure_frame ce func ee ready s z /\ wb_frame ce ee ee ready s z /\
    return_buf_frame d ce u z /\ ghost_kept_at lo ce ee ready G tn s Gz tz /\
    (!x. not_fresh_at ready x ==> lookup_var x z = lookup_var x s /\
      FLOOKUP Gz x = FLOOKUP G x /\ op_taint tz (Var x) = op_taint tn (Var x)) /\
    (!x cap. not_fresh_at ready x /\ ptr_covers G tn x s cap ==> ptr_covers Gz tz x z cap) /\
    (!id a. FLOOKUP s.vs_allocas id = SOME a ==> FLOOKUP z.vs_allocas id = SOME a) /\
    regions_disjoint (w2n w) (type_memory_size rt) b n /\
    FLOOKUP z.vs_allocas aid = SOME (b,n) /\ read_memory (b+32) k z = prefix /\
    (!i. b+32 <= i /\ i < b+32+k ==> i NOTIN tz.t_mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_encode_saved_code_restore_core_mods >>
  disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >>
  disch_then (qx_choosel_then [`z`,`Gz`,`tz`,`root`,`w`]
    (map_every assume_tac o CONJUNCTS)) >>
  drule_all_then strip_assume_tac saved_code_copy_selector >>
  qexistsl [`z`,`Gz`,`tz`,`root`,`w`] >> asm_rewrite_tac[LESS_IMP_LESS_OR_EQ] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >> first_assum ACCEPT_TAC
QED

Finalise abi_encode_saved_code_restore_mods
