Theory stmtSimCustomErrorPtrCodeMaterialise
Ancestors
  exprSimPtrTopLevelImmutablePost exprSimPtrTopLevelImmutableBranch
  exprSimPtrTopLevelImmutableRun exprSimPtrTopLevelImmutableCopy
  exprSimStorageCopy exprSimPtrTopLevelStorageAlloc
  exprSimPtrTopLevelStorageFrame exprSimPtrLiteralBuffer
  exprSimCopy exprSimAlloc exprSimUnwrap exprSimUnwrapProps
  exprLowering exprLoweringProps loweringPosts compileEnv loweringStateRelDefs
  context venomState venomInst words ptrDiscipline fragGasPathPtr
  ghostPcTransportPtr loweringHalt fragExec pred_set rich_list
  bodyPtrDefs immutableCopyExecution valueEncodingProps exprSimProps
  entrySinkExtraction bodyFieldMemoryProps bodyPtrHashBuiltinsGhostFrame

(* The finite-copy induction is already exported by
   toplevel_immutable_copy_frame, including its zero-word case. *)
Theorem custom_error_code_alloc_copy_run[local]:
  compile_alloc_buffer (32*n) sa = (buf,sm) /\
  compile_imm_copy_to_memory F imm src buf.buf_operand n 0 sm = ((),sb) /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  fn_has_code sa sm fn /\ fn_has_code sm sb fn /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ 32*n < dimword (:256) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u w Ga ta p t H tm.
    buf.buf_operand = Var p /\
    run_inst_seq (emitted_insts sa sm) s = OK u /\
    stmt_state_rel ctx fn cenv cx es u /\ u.vs_memory = s.vs_memory /\
    lookup_var p u = SOME w /\ lookup_var p t = SOME w /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    ptr_covers H tm p t (32*n) /\
    immutable_copy_ghost_frame sm
      (u with vs_inst_idx := LENGTH sm.cs_current_insts) Ga ta sb t H tm 0 (32*n) w /\
    (!i. w2n w <= i /\ i < w2n w+32*n ==> i NOTIN tm.t_mem) /\
    tm.t_mem SUBSET tn.t_mem /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\
    (!name b len. local_region cenv es.scopes u name b len ==>
      regions_disjoint (w2n w) (32*n) b len)
Proof
  strip_tac >> drule_all toplevel_alloc_buffer_ptr_run >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] strip_assume_tac) >>
  drule storage_copy_alloc_layout >> strip_tac >>
  `(!x. not_fresh_at sa x ==> not_fresh_at sm x)` by
    (gvs[not_fresh_at_def] >> decide_tac) >>
  `copy_old_operand sm src` by
    (Cases_on `src` >> gvs[copy_old_operand_def] >> metis_tac[]) >>
  qabbrev_tac `s1 = u with vs_inst_idx := LENGTH sm.cs_current_insts` >>
  `u.vs_labels = s.vs_labels` by metis_tac[hash_alloc_buffer_labels] >>
  `eval_operand src s1 = SOME a /\ op_taint tnf src = {}` by
    (Cases_on `src` >> gvs[eval_operand_def, op_taint_def, Abbr `s1`, lookup_var_def] >>
     metis_tac[]) >>
  `lookup_var p s1 = SOME w /\ ptr_covers Gf tnf p s1 (32*n)` by
    fs[Abbr `s1`, eval_operand_def, lookup_var_def] >>
  `compile_imm_copy_to_memory F imm src (Var p) n 0 sm = ((),sb) /\
   0+32*n <= 32*n` by metis_tac[arithmeticTheory.LESS_EQ_REFL, arithmeticTheory.ADD] >>
  drule_all toplevel_immutable_copy_frame >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  `sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
   same_blocks sm sb` by
    fs[immutable_copy_ghost_frame_def, copy_runtime_frame_def] >>
  `sb.cs_current_bb = sm.cs_current_bb` by fs[same_blocks_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `~s1.vs_halted /\ s1.vs_current_bb = sm.cs_current_bb /\
   s1.vs_inst_idx = LENGTH sm.cs_current_insts` by simp[Abbr `s1`] >>
  `lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sm sb) (DROP s1.vs_inst_idx bb.bb_instructions)` by
    (simp[] >>
     qpat_x_assum `fn_has_code sm sb fn` mp_tac >>
     qpat_x_assum `sb.cs_current_insts = _` mp_tac >>
     qpat_x_assum `sb.cs_current_bb = _` mp_tac >>
     qpat_x_assum `lookup_block sm.cs_current_bb _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[fn_has_code_def] >> rpt strip_tac >> gvs[] >>
     qpat_x_assum `isPREFIX _ _` mp_tac >>
     rewrite_tac[IS_PREFIX_APPEND] >> strip_tac >> qexists_tac `l` >>
     asm_rewrite_tac[] >> pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]) >>
  drule_all toplevel_immutable_copy_counted_frontier >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  drule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  `(!i. w2n w <= i /\ i < w2n w+32*n ==> i NOTIN tm'.t_mem) /\
   tm'.t_mem SUBSET tn.t_mem` by
    metis_tac[toplevel_immutable_full_copy_clean,
      toplevel_immutable_alloc_copy_taint_subset] >>
  drule_all toplevel_alloc_buffer_static_effects >> strip_tac >>
  `t'.vs_call_ctx = s.vs_call_ctx /\ t'.vs_accounts = s.vs_accounts /\
   t'.vs_transient = s.vs_transient` by
    (gvs[immutable_copy_ghost_frame_def, copy_runtime_frame_def] >>
     drule copy_static_fields >> simp[Abbr `s1`, copy_static_def]) >>
  qexistsl_tac [`w`,`Gf`,`tnf`,`t'`,`H'`,`tm'`] >>
  fs[Abbr `s1`, eval_operand_def, lookup_var_def] >>
  gvs[immutable_copy_ghost_frame_def, copy_runtime_frame_def, lookup_var_def] >>
  metis_tac[]
QED

Theorem custom_error_code_unwrap_ptr:
  unwrap_value ce (LocatedValue ty place) sm = (op,sb) /\
  place.ptr_location = LocCode /\ ~ce.ce_is_ctor /\
  ~is_word_type (post_value_type ce e) /\
  vv_post ctx func ce cx e es sa sm s0 ee raw (LocatedValue ty place) s /\
  ptr_vv_ok cx (post_value_type ce e) raw (LocatedValue ty place) ee G tn s /\
  read_result cx raw ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tv /\
  post_value_type ce e = expr_type e /\
  nb = type_memory_bytes ce ty /\ nb = type_memory_size tv /\
  nb < dimword (:256) /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!x. place.ptr_operand = Var x ==> not_fresh_at sm x) /\
  ghost_inv d ce cx ee G tn s /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  !D PG. ?G' tn' t p w.
    op = Var p /\ lookup_var p t = SOME w /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G' tn' (OK t) /\
    expr_post ctx func ce cx e es sa sb s0 ee v op t /\
    ptr_val_ok cx (post_value_type ce e) v op G' tn' t /\
    ptr_covers G' tn' p t nb /\
    ghost_inv d ce cx ee G' tn' t /\ ghost_kept ce ee sm G tn s G' tn' /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\
    (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
    FLOOKUP t.vs_allocas sm.cs_next_id = SOME (w2n w,nb) /\
    sm.cs_next_id < sb.cs_next_id /\
    (!aid b len. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
      regions_disjoint (w2n w) nb b len) /\
    (!i. i < w2n w \/ w2n w+nb <= i ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
    tn'.t_mem SUBSET tn.t_mem
Proof
  strip_tac >> rpt gen_tac >>
  `vv_post ctx func ce cx e es sa sm s0 ee (Value v) (LocatedValue ty place) s` by
    metis_tac[vv_post_read_result] >>
  `ty = expr_type e /\ ?a. eval_operand place.ptr_operand s = SOME a` by
    gvs[vv_post_def, vv_holds_def] >>
  `nb = 32 * type_slot_size tv` by simp[type_memory_size_slots] >>
  `?buf mid. compile_alloc_buffer nb sm = (buf,mid) /\
    compile_imm_copy_to_memory F ce.ce_imm_alloca place.ptr_operand
      buf.buf_operand (type_slot_size tv) 0 mid = ((),sb) /\
    op = buf.buf_operand` by
    (`(nb+31) DIV 32 = type_slot_size tv` by (simp[] >> decide_tac) >>
     gvs[] >> qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
     asm_rewrite_tac[unwrap_value_def, compile_ensure_in_memory_def] >>
     Cases_on `compile_alloc_buffer (type_memory_size tv) sm` >>
     simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     pairarg_tac >> strip_tac >> gvs[] >> metis_tac[]) >>
  `fn_has_code sm mid func /\ fn_has_code mid sb func` by
    metis_tac[toplevel_immutable_alloc_copy_code] >>
  `stmt_state_rel ctx func ce cx ee s /\ op_taint tn place.ptr_operand = {}` by
    gvs[vv_post_def, ptr_vv_ok_def] >>
  qpat_x_assum `nb = 32 * type_slot_size tv` SUBST_ALL_TAC >>
  drule_all custom_error_code_alloc_copy_run >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  suspend "assemble"
QED

Resume custom_error_code_unwrap_ptr[assemble]:
  `run_inst_seq (emitted_insts sm sb)
     (s with vs_inst_idx := LENGTH mid.cs_current_insts) = OK t` by
    (irule toplevel_immutable_alloc_copy_sequence >>
     rpt (goal_assum (drule_at Any)) >> metis_tac[]) >>
  `expr_post ctx func ce cx e es sa sb s0 ee v op t` by
    (irule toplevel_immutable_run_expr_post >>
     rpt (goal_assum (drule_at Any)) >> gvs[]) >>
  `val_wf tv v /\ val_in_memory tv v (w2n w) t.vs_memory` by
    (gvs[expr_post_def, expr_val_rel_def, expr_val_at_def, eval_operand_def] >> metis_tac[]) >>
  `ptr_val_ok cx (post_value_type ce e) v (Var p) H tm t` by
    (irule (cj 1 toplevel_immutable_clean_pointer_post) >>
     rpt (goal_assum (drule_at Any)) >> simp[] >>
     qexists_tac `ce` >> gvs[] >> metis_tac[val_store_size_le]) >>
  suspend "frames"
QED

Resume custom_error_code_unwrap_ptr[frames]:
  drule_all runtime_code_copy_alloc_run >> strip_tac >>
  `u' = u /\ w' = w` by
    (gvs[eval_operand_def] >> metis_tac[optionTheory.SOME_11, venomStateTheory.lookup_var_def]) >>
  gvs[] >>
  `immutable_holds ce cx (expr_type e) (Value v) a ee s` by
    (gvs[vv_post_def, vv_holds_def] >> metis_tac[]) >>
  `w2n a + type_memory_size tv < dimword (:256)` by
    (drule_all immutable_holds_bounds >> simp[]) >>
  `copy_old_operand mid place.ptr_operand /\ copy_old_operand mid (Var p)` by
    (drule storage_copy_alloc_layout >> strip_tac >>
     Cases_on `place.ptr_operand` >> gvs[copy_old_operand_def, not_fresh_at_def] >> decide_tac) >>
  `eval_operand place.ptr_operand (u with vs_inst_idx := LENGTH mid.cs_current_insts) = SOME a /\
   eval_operand (Var p) (u with vs_inst_idx := LENGTH mid.cs_current_insts) = SOME w` by
    (Cases_on `place.ptr_operand` >> gvs[eval_operand_def, lookup_var_def]) >>
  drule_all copy_runtime_run >> strip_tac >>
  `s' = t` by gvs[immutable_copy_ghost_frame_def, copy_runtime_frame_def] >>
  `w2n w + type_memory_size tv < dimword (:256)` by metis_tac[] >>
  drule_at (Pat `_.vs_memory = (immutable_transfers _ _ _ _ _ _ _).vs_memory`)
    runtime_code_copy_memory_frame >>
  impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
  gvs[] >>
  `!i. i < w2n w \/ w2n w + type_memory_bytes ce (expr_type e) <= i ==>
      mem_bytes_at i 1 s'.vs_memory = mem_bytes_at i 1 s.vs_memory` by
    (rpt strip_tac >>
     `1+i <= w2n w \/ w2n w + type_memory_bytes ce (expr_type e) <= i` by decide_tac >>
     metis_tac[]) >>
  `ghost_inv d ce cx ee H tm s'` by
    (irule (INST_TYPE [alpha |-> ``:256``] toplevel_immutable_alloc_copy_ghost_inv) >>
     rpt (goal_assum (drule_at Any)) >> simp[] >>
     qexistsl_tac [`type_memory_bytes ce (expr_type e)`,`w`] >> simp[] >> metis_tac[]) >>
  `ghost_kept ce ee sm G tn s H tm` by
    (irule literal_ghost_kept >> simp[] >> metis_tac[]) >>
  suspend "finish"
QED

Resume custom_error_code_unwrap_ptr[finish]:
  `s'.vs_allocas = u.vs_allocas /\ s'.vs_halted = u.vs_halted` by
    (gvs[copy_runtime_frame_def] >> drule copy_static_fields >> simp[]) >>
  `sm.cs_next_id < sb.cs_next_id` by
    (`ci_mono mid sb` by metis_tac[ci_mono_compile_imm_copy_to_memory, pairTheory.SND] >>
     gvs[ci_mono_def] >> decide_tac) >>
  `!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt ==>
     type_memory_bytes ce (expr_type e) = type_memory_size tvt` by simp[] >>
  drule_all runtime_code_copy_run_post >> strip_tac >>
  `code = emitted_insts sm sb` by gvs[emitted_insts_def, DROP_LENGTH_APPEND] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code` by
    (qpat_x_assum `EVERY (\i. MEM i.inst_opcode _) code` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     pure_rewrite_tac[listTheory.EVERY_MEM] >> disch_tac >> gen_tac >> disch_tac >>
     first_x_assum drule >> simp[] >> strip_tac >> gvs[is_terminator_def]) >>
  `run_inst_seq code (s with vs_inst_idx := LENGTH mid.cs_current_insts) = OK s'` by metis_tac[] >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  qexistsl_tac [`H`,`tm`,`s' with vs_inst_idx := LENGTH sb.cs_current_insts`,`w`] >>
  fs[hash_ghost_inv_inst_idx, ptr_val_ok_def, ptr_mem_ok_def, lookup_var_def,
     same_blocks_def] >> metis_tac[]
QED

Finalise custom_error_code_unwrap_ptr
