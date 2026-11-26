(* The store shared by the ordinary and static fixed RawLog suffixes. *)
Theory bodyRawLogFixedScratchStoreMods
Ancestors
  bodyFullBuiltinBytestringCopy bodyIfExpTypedGhostMods bodyIfExpTypedImmFrameMods
  bodyFullUnwrapSlotPost bodyFullShadowBodyInv bodyFullPostsMods bodyPtrDefs wordLoadStorePtr
  venomMemDefs assignTuplePtrCopyLen
  actualAllocExec loweringHalt exprSimAlloc exprLoweringProps stateRelProj
  allocasBelowFmpUpdatesProps fragGasOriginPtr fragExec emitHelperProps
  typedMemoryCopy loweringStateRelDefs instMemFrontier valueEncodingProps
  venomMemProps venomState venomInst ptrDiscipline words byte rich_list list pred_set

Theorem fixed_scratch_code[local]:
  emit_void MSTORE [pop;data_op] sm = ((),s1) /\
  emit_inst LOG log_ops [] s1 = ((),sb) /\ fn_has_code sm sb func ==>
  fn_has_code sm s1 func /\ s1.cs_current_bb = sm.cs_current_bb /\
  LENGTH s1.cs_current_insts = SUC (LENGTH sm.cs_current_insts)
Proof
  strip_tac >> drule emit_void_extends >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule emit_inst_extends >> strip_tac >> fs[same_blocks_def] >>
  fs[fn_has_code_def,emitted_blocks_def] >>
  metis_tac[IS_PREFIX_APPEND1]
QED

Theorem fixed_scratch_state_frame[local]:
  typed_copy_state_frame sm a 32 s (mstore a w s with vs_inst_idx := idx)
Proof
  simp[typed_copy_state_frame_def] >> conj_tac >- simp[mstore_def] >>
  conj_tac >- simp[mstore_def,lookup_var_def] >>
  simp[typed_copy_frame_def,mstore_memory_nondecreasing] >>
  rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> simp[]
QED

Theorem fixed_scratch_eval[local]:
  (!op. eval_operand op (mstore a w s with vs_inst_idx := idx) = eval_operand op s) /\
  (!ops. eval_operands ops (mstore a w s with vs_inst_idx := idx) = eval_operands ops s)
Proof
  conj_asm1_tac
  >- (Cases >> simp[mstore_def,eval_operand_def,lookup_var_def]) >>
  Induct >> simp[eval_operands_def]
QED

Theorem raw_log_fixed_scratch_store_mods:
  emit_void MSTORE [buf.buf_operand;data_op] sm = ((),s1) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;buf.buf_operand]) [] s1 = ((),sb) /\
  fn_has_code sm sb func /\
  compile_alloc_buffer 32 alloc_sa = (buf,data_sa) /\ fn_has_code alloc_sa data_sa func /\
  local_ptrs_reserved cenv sm /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  stmt_state_rel H ctx func cenv cx ee s /\ immutable_frame_mods func cenv cx ee s /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  ptr_val_ok cx ty (BytesV bs) data_op G tn s /\
  eval_operand data_op s = SOME word /\ TAKE 32 (word_to_bytes_be word) = bs /\
  buf.buf_operand = Var p /\ eval_operand buf.buf_operand s = SOME w /\ ptr_covers G tn p s 32 /\
  FLOOKUP s.vs_allocas alloc_sa.cs_next_id = SOME (w2n w,32) /\ w2n w+32 < dimword (:256) /\
  (!name b n. local_region cenv ee.scopes s name b n ==> regions_disjoint (w2n w) 32 b n) /\
  (!aid b n. aid < sa.cs_next_id /\ FLOOKUP s0.vs_allocas aid = SOME (b,n) ==>
    regions_disjoint (w2n w) 32 b n) /\
  eval_operands ops s = SOME vals /\ EVERY (\op. op_taint tn op = {}) ops /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  let i = mk_inst sm.cs_next_id MSTORE [buf.buf_operand;data_op] [];
      t = mstore (w2n w) word s;
      z = t with vs_inst_idx := LENGTH s1.cs_current_insts;
      tf = step_taint i s t tn
  in
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,G,tf) /\
    ~z.vs_halted /\ z.vs_current_bb = s1.cs_current_bb /\ z.vs_inst_idx = LENGTH s1.cs_current_insts /\
    buf.buf_operand = Var p /\ eval_operand buf.buf_operand z = SOME w /\ ptr_covers G tf p z 32 /\
    op_taint tf buf.buf_operand = {} /\
    w2n w+32 < dimword (:256) /\ w2n w+32 <= z.vs_alloca_next /\
    mem_bytes_at (w2n w) 32 z.vs_memory = bs /\
    (!j. w2n w <= j /\ j < w2n w+32 ==> j NOTIN tf.t_mem) /\
    eval_operands ops z = SOME vals /\ EVERY (\op. op_taint tf op = {}) ops /\
    allocas_from lo z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\ stor_taint_ok_at (DF H) tf z /\
    stmt_state_rel H ctx func cenv cx ee z /\ immutable_frame_mods func cenv cx ee z /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee G tf z /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G tf
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all fixed_scratch_code >> strip_tac >>
  qabbrev_tac `i = mk_inst sm.cs_next_id MSTORE [buf.buf_operand;data_op] []` >>
  qabbrev_tac `t = mstore (w2n w) word s` >>
  qabbrev_tac `z = t with vs_inst_idx := LENGTH s1.cs_current_insts` >>
  qabbrev_tac `tf = step_taint i s t tn` >>
  `local_ptrs_rel func cenv ee.scopes s /\ alloca_inv s` by
    (drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  `w2n w + 32 <= s.vs_alloca_next` by
    (irule alloca_region_below_frontier >> conj_tac >- fs[alloca_inv_def] >>
     qexistsl_tac [`alloc_sa.cs_next_id`,`w2n w`,`32`] >> simp[]) >>
  `allocas_from lo s /\ stor_taint_ok_at (DF H) tn s` by fs[ghost_inv_at_mods_def] >>
  `lo <= w2n w` by
    (qpat_x_assum `allocas_from lo s` mp_tac >> simp[allocas_from_def] >>
     disch_then drule >> simp[]) >>
  `op_taint tn data_op = {}` by fs[ptr_val_ok_def] >>
  `lookup_var p s = SOME w` by
    (qpat_assum `eval_operand buf.buf_operand s = SOME w` mp_tac >>
     qpat_assum `buf.buf_operand = Var p`
       (fn th => pure_rewrite_tac [th,eval_operand_def]) >> simp[]) >>
  `~z.vs_halted /\ z.vs_current_bb = s1.cs_current_bb /\
   z.vs_inst_idx = LENGTH s1.cs_current_insts /\ z.vs_alloca_next = s.vs_alloca_next /\
   z.vs_allocas = s.vs_allocas` by simp[Abbr `z`,Abbr `t`,mstore_def] >>
  `tf.t_var = tn.t_var /\ tf.t_stor = tn.t_stor /\
   tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm` by
    simp[Abbr `tf`,Abbr `i`,Abbr `t`,ifexp_materialize_mstore_ghost] >>
  `tf.t_mem = tn.t_mem DIFF {j | w2n w <= j /\ j < w2n w+32}` by
    simp[Abbr `tf`,Abbr `i`,Abbr `t`,ifexp_materialize_mstore_taint] >>
  `typed_copy_state_frame sm (w2n w) 32 s z` by
    simp[Abbr `z`,Abbr `t`,fixed_scratch_state_frame] >>
  `MEM (mk_inst alloc_sa.cs_next_id ALLOCA [Lit 32w] [p]) (fn_insts func)` by
    (drule compile_alloc_buffer_parts >> strip_tac >>
     drule_all actual_alloc_buffer_site >> fs[]) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,G,tf)` by
    suspend "path" >>
  `stmt_state_rel H ctx func cenv cx ee z` by suspend "state" >>
  `immutable_frame_mods func cenv cx ee z` by suspend "imm" >>
  `ghost_inv_at_mods (DF H) lo d cenv cx ee G tf z` by suspend "ghost" >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G tf` by suspend "kept" >>
  suspend "finish"
QED

Resume raw_log_fixed_scratch_store_mods[path]:
  `gas_origin_ptr_edge (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,G,tf)` by
    (`emit_void MSTORE [Var p;data_op] sm = ((),s1)` by fs[] >>
     drule_all bytestring_length_store_origin_edge >>
     simp[Abbr `z`,Abbr `t`,Abbr `tf`,Abbr `i`,ifexp_materialize_mstore_ghost]) >>
  metis_tac[gas_origin_ptr_path_rules,APPEND_NIL]
QED

Resume raw_log_fixed_scratch_store_mods[state]:
  simp[Abbr `z`,Abbr `t`,stmt_state_rel_inst_idx] >>
  irule literal_mstore_state_rel >> simp[] >>
  qexistsl_tac [`w2n w`,`mk_inst alloc_sa.cs_next_id ALLOCA [Lit 32w] [p]`,`32`] >>
  simp[mk_inst_def] >>
  qpat_assum `!name b n. local_region _ _ _ _ _ _ ==> _` mp_tac >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def]
QED

Resume raw_log_fixed_scratch_store_mods[imm]:
  irule ifexp_typed_immutable_frame_mods >>
  qexistsl_tac [`w2n w`,`mk_inst alloc_sa.cs_next_id ALLOCA [Lit 32w] [p]`,`sm`,`32`,`s`] >>
  simp[mk_inst_def]
QED

Resume raw_log_fixed_scratch_store_mods[ghost]:
  irule ifexp_typed_copy_ghost_mods >>
  goal_assum (drule_at (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`)) >>
  qexistsl_tac [`w2n w`,`func`,`sm`,`32`] >> simp[op_taint_def] >>
  rpt strip_tac >>
  qpat_assum `!name b n. local_region _ _ _ _ _ _ ==> _` (drule_then ACCEPT_TAC)
QED

Resume raw_log_fixed_scratch_store_mods[kept]:
  irule unwrap_slot_copy_ghost_kept_at >>
  goal_assum (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
  simp[op_taint_def]
QED

Resume raw_log_fixed_scratch_store_mods[finish]:
  `!x. lookup_var x z = lookup_var x s` by
    simp[Abbr `z`,Abbr `t`,mstore_def,lookup_var_def] >>
  `ptr_covers G tf p z 32` by
    (irule ptr_covers_lookup_frame >> qexistsl_tac [`G`,`s`,`tn`] >> simp[op_taint_def]) >>
  `op_taint tf buf.buf_operand = {}` by fs[ptr_covers_def] >>
  `mem_bytes_at (w2n w) 32 z.vs_memory = bs` by
    (qpat_x_assum `TAKE 32 _ = bs` mp_tac >>
     `LENGTH (word_to_bytes_be word) = 32` by
       simp[word_to_bytes_be_def,LENGTH_word_to_bytes] >>
     `TAKE 32 (word_to_bytes_be word) = word_to_bytes_be word` by metis_tac[TAKE_LENGTH_ID] >>
     simp[Abbr `z`,Abbr `t`,mem_bytes_at_mstore_same,word_to_bytes_be_def]) >>
  `eval_operand buf.buf_operand z = SOME w /\ eval_operands ops z = SOME vals` by
    simp[Abbr `z`,Abbr `t`,fixed_scratch_eval] >>
  `allocas_from lo z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
   stor_taint_ok_at (DF H) tf z` by
    (qpat_assum `ghost_inv_at_mods _ _ _ _ _ _ G tf z` mp_tac >>
     simp_tac bool_ss [ghost_inv_at_mods_def] >> strip_tac >> simp[] >>
     disch_tac >> simp[Abbr `z`,Abbr `t`,allocas_below_fmp_updates]) >>
  `EVERY (\op. op_taint tf op = {}) ops` by
    (qpat_assum `tf.t_var = tn.t_var` (fn th => pure_rewrite_tac [op_taint_def,th]) >>
     qpat_assum `EVERY (\op. op_taint tn op = {}) ops`
       (ACCEPT_TAC o REWRITE_RULE [op_taint_def])) >>
  qpat_assum `buf.buf_operand = Var p`
    (fn th => rule_assum_tac (REWRITE_RULE [th]) >> pure_rewrite_tac [th]) >>
  simp[]
QED

Finalise raw_log_fixed_scratch_store_mods
