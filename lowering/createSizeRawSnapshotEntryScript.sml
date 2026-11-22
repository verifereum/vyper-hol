(* Entry resources at the data-pointer cut of a raw CREATE snapshot. *)
Theory createSizeRawSnapshotEntry
Ancestors
  bodyFullUnwrapSlotPost exprPtrUnwrapAllocSemantic exprPtrUnwrapAllocEntry
  bodyMemoryDefs bodyPtrDefs ptrDiscipline decoderAllocationBoundsPtr exprSimCopy exprPtrUnwrapRetained
  exprPtrUnwrapAllocSeparation bodyFullHashKeccakFixed
  exprLowering exprLoweringProps emitHelperProps compileEnv loweringPosts
  bufferAllocationExecution allocaHistory venomState venomMemDefs
  venomExecSemantics venomMemProps venomInst finite_map pred_set words arithmetic
  exprSimAlloc exprSimStorageCopy exprPtrUnwrapAllocation
  createSizeRawMemoryFootprint createSizeRawImmutableFootprint
  createSizeRawScalarFrame createSizeRawCutHistory createSizeSlotTraversal
  exprPtrUnwrapRuntimeFrame createBlueprintRawCopyLayout bodyPtrMakeArrayExternalCaller
  exprPtrUnwrapMarked externalEntryShape loweringShapeDefs abiBufferAllocationCode
  loweringHalt valueTypingMemoryProps exprSimAggregateLayout vfmConstants
  exprBodyPreProps exprSimSource exprSimHyps abiEncodeArgsCase vyperInterpreter vyperTyping valueEncodingProps valueEncodingDefs
  fragGasOrigin fragExec context copyExecution slotCopyExecution relation list rich_list
  vyperTypeSystem stateRelProj bodyPtrAttributeSource freshWrites reasonEndpointResourcesPtr
Libs BasicProvers

(* These are entry ghosts, not a claimed ghost execution. In particular,
   the bytes in the snapshot window are conservatively allowed to be tainted. *)
Theorem raw_snapshot_entry_ghost[local]:
  ghost_inv_at D lo d ce cx es G tn u /\ local_ptrs_reserved ce a /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at a x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at a x) /\
  local_ptrs_rel func ce es.scopes u /\
  (!name b n. local_region ce es.scopes u name b n ==>
     (snapshot_base:num) + cap <= b \/ b + n <= snapshot_base) /\
  (!x. not_fresh_at a x ==> lookup_var x r = lookup_var x u) /\
  (!off n. off + n <= snapshot_base \/ snapshot_base + cap <= off ==>
     mem_bytes_at off n r.vs_memory = mem_bytes_at off n u.vs_memory) /\
  ~not_fresh_at a len /\ ~not_fresh_at a data /\ lo <= snapshot_base /\
  r.vs_accounts = u.vs_accounts /\ r.vs_transient = u.vs_transient /\
  r.vs_immutables = u.vs_immutables /\ r.vs_call_ctx = u.vs_call_ctx /\
  allocas_from lo r /\ lo <= r.vs_alloca_next ==>
  ghost_inv_at D lo d ce cx es (G |+ (data,snapshot_base,cap))
    (tn with <|t_var := tn.t_var |+ (len,{}) |+ (data,{});
               t_mem := tn.t_mem UNION {i | snapshot_base <= i /\ i < snapshot_base + cap}|>) r
Proof
  strip_tac >> irule unwrap_slot_copy_ghost_inv_at >>
  simp[] >> conj_tac
  >- (fs[ghost_inv_at_def, stor_taint_ok_at_def]) >>
  qexistsl_tac [`G`,`func`,`cap`,`u`,`a`,`snapshot_base`,`tn`] >>
  simp[op_taint_def, FLOOKUP_UPDATE] >> rpt conj_tac
  >- (rpt strip_tac >> qpat_assum `!name b n. local_region _ _ _ _ _ _ ==> _` drule >> decide_tac)
  >- (rpt strip_tac >> `x <> len /\ x <> data` by metis_tac[] >> simp[])
  >- (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  rpt strip_tac >> `~(snapshot_base <= j /\ j < cap + snapshot_base)` by decide_tac >> simp[]
QED

(* Shared boundary of the three write cases. The concrete copy proofs provide
   the exterior footprint between the observed ALLOCA and preparation cuts. *)
Theorem raw_snapshot_finish_entry[local]:
  compile_alloc_buffer cap a = (buf,m) /\ fn_has_code a m func /\
  buf.buf_operand = Var root /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce a /\ cap < dimword (:256) /\
  step_inst_base (mk_inst a.cs_next_id ALLOCA [Lit (n2w cap)] [root]) u = OK v /\
  snapshot_base = buffer_allocation_base u a.cs_next_id /\
  u.vs_current_bb = a.cs_current_bb /\ u.vs_inst_idx = LENGTH a.cs_current_insts /\
  alloca_history func u /\ ~u.vs_halted /\
  (?H. valid_horizon cx st0 H p.storage_trace) /\
  (!H. valid_horizon cx st0 H p.storage_trace ==>
     stmt_state_rel H ctx func ce cx (p with gas_obs := []) u /\
     storage_well_formed_on cx (p with gas_obs := []) (FST H) /\
     ghost_inv_at (DF H) lo d ce cx (p with gas_obs := []) G tn u) /\
  return_buf_frame d ce a u /\ a.cs_next_var <= ac.cs_next_var /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at a x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at a x) /\
  copy_static r = copy_static v /\ LENGTH v.vs_memory <= LENGTH r.vs_memory /\
  (!x. not_fresh_at a x ==> lookup_var x r = lookup_var x v) /\
  (!off k. off+k <= snapshot_base \/ snapshot_base+cap <= off ==>
    mem_bytes_at off k r.vs_memory = mem_bytes_at off k v.vs_memory) /\
  alloca_history func r /\
  r.vs_current_bb = ac.cs_current_bb /\ r.vs_inst_idx = LENGTH ac.cs_current_insts /\
  ~not_fresh_at a len /\ ~not_fresh_at a data /\
  not_fresh_at ac len /\ not_fresh_at ac data /\
  lookup_var len r = SOME (n2w (LENGTH code)) /\
  lookup_var data r = SOME (n2w (snapshot_base+32)) /\ LENGTH code + 32 <= cap ==>
  ?Gr tnr.
    (!H. valid_horizon cx st0 H p.storage_trace ==>
       stmt_state_rel H ctx func ce cx (p with gas_obs := []) r /\
       storage_well_formed_on cx (p with gas_obs := []) (FST H) /\
       ghost_inv_at (DF H) lo d ce cx (p with gas_obs := []) Gr tnr r) /\
    return_buf_frame d ce ac r /\ alloca_history func r /\ ~r.vs_halted /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp r) /\
    r.vs_current_bb = ac.cs_current_bb /\ r.vs_inst_idx = LENGTH ac.cs_current_insts /\
    FLOOKUP r.vs_allocas a.cs_next_id = SOME (snapshot_base,cap) /\
    lookup_var len r = SOME (n2w (LENGTH code)) /\
    lookup_var data r = SOME (n2w (snapshot_base+32)) /\
    not_fresh_at ac len /\ not_fresh_at ac data /\
    op_taint tnr (Var len) = {} /\ ptr_covers Gr tnr data r (LENGTH code) /\
    w2n (n2w (snapshot_base+32) : bytes32) + LENGTH code <= r.vs_alloca_next
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qabbrev_tac `ee = p with gas_obs := []` >> fs[GSYM markerTheory.Abbrev_def] >>
  `stmt_state_rel H ctx func ce cx ee u /\ ghost_inv_at (DF H) lo d ce cx ee G tn u` by
    (qpat_assum `!H. valid_horizon _ _ _ _ ==> _` drule >> simp[]) >>
  `snapshot_base + cap < dimword (:256)` by
    (drule_all unwrap_alloc_site_bound >> simp[]) >>
  `snapshot_base + 32 < dimword (:256) /\ snapshot_base < dimword (:256)` by decide_tac >>
  qabbrev_tac `i = mk_inst a.cs_next_id ALLOCA [Lit (n2w cap)] [root]` >>
  `exec_alloca i u (n2w cap:bytes32) = OK v` by
    (qpat_assum `step_inst_base _ u = _` mp_tac >>
     simp_tac (srw_ss()) [Abbr `i`, step_inst_base_opcode_eqs, mk_inst_def]) >>
  `v = update_var root (n2w snapshot_base) (buffer_allocation_fields u a.cs_next_id cap)` by
    (drule_all unwrap_alloc_generated_step >>
     disch_then (qspec_then `u` strip_assume_tac) >> gvs[]) >>
  `MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\ i.inst_id = a.cs_next_id` by
    (drule unwrap_alloc_generated_code >> strip_tac >>
     `root = STRING #"%" (toString a.cs_next_var)` by fs[] >>
     drule_all buffer_alloc_code >> fs[Abbr `i`, mk_inst_def]) >>
  qunabbrev_tac `i` >>
  `!H. valid_horizon cx st0 H p.storage_trace ==> stmt_state_rel H ctx func ce cx ee v` by
    (rpt strip_tac >> qpat_assum `!H. valid_horizon _ _ _ _ ==> _ /\ _` drule >> strip_tac >>
     drule_all unwrap_alloc_semantic_frames >> simp[]) >>
  `FLOOKUP v.vs_allocas a.cs_next_id = SOME (snapshot_base,cap) /\
   v.vs_memory = u.vs_memory /\
   (!x. not_fresh_at a x ==> lookup_var x v = lookup_var x u)` by
    (drule_all unwrap_alloc_semantic_frames >> simp[w2n_n2w, LESS_MOD]) >>
  `!name b n. local_region ce ee.scopes u name b n ==>
     snapshot_base+cap <= b \/ b+n <= snapshot_base` by
    (rpt strip_tac >> drule_all unwrap_alloc_local_separation >> simp[]) >>
  `!name b n. local_region ce ee.scopes v name b n ==>
     snapshot_base+cap <= b \/ b+n <= snapshot_base` by
    (rpt strip_tac >> drule_all unwrap_alloc_semantic_frames >> strip_tac >>
     qpat_assum `!name b k. local_region _ _ v _ _ _ ==> _` drule >>
     simp_tac (srw_ss()) [loweringStateRelDefsTheory.regions_disjoint_def, w2n_n2w, ADD_COMM] >>
     `snapshot_base MOD dimword (:256) = snapshot_base` by simp[LESS_MOD] >>
     simp[]) >>
  `v.vs_alloca_next >= u.vs_alloca_next /\ allocas_from lo v` by
    (qpat_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` (strip_assume_tac o REWRITE_RULE [ghost_inv_at_def]) >>
     `allocas_from lo v` by (drule_all exec_alloca_preserves_allocas_from >> simp[]) >>
     drule exec_alloca_alloca_next_mono >> simp[]) >>
  `!H. valid_horizon cx st0 H p.storage_trace ==> stmt_state_rel H ctx func ce cx ee r` by
    (rpt strip_tac >> irule copy_buffer_state_rel_frame >>
     qexistsl_tac [`snapshot_base`,`mk_inst a.cs_next_id ALLOCA [Lit (n2w cap)] [root]`,`v`,`a`,`cap`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     TRY (qpat_assum `!H. valid_horizon _ _ _ _ ==> stmt_state_rel _ _ _ _ _ _ _` irule >> simp[] >> NO_TAC) >>
     simp_tac (srw_ss()) [mk_inst_def] >> metis_tac[ADD_COMM]) >>
  `!x. not_fresh_at a x ==> lookup_var x r = lookup_var x u` by metis_tac[] >>
  `return_buf_frame d ce ac r` by
    (drule copy_static_fields >> strip_tac >> irule return_buf_frame_frame >>
     qexistsl_tac [`ce`,`u`,`a`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     metis_tac[GREATER_EQ]) >>
  suspend "finish"
QED
Resume raw_snapshot_finish_entry[finish]:
  drule copy_static_fields >> strip_tac >>
  `r.vs_immutables = v.vs_immutables` by
    (qpat_assum `copy_static r = _` (mp_tac o AP_TERM ``\s. s.vs_immutables``) >>
     simp_tac (srw_ss()) [copy_static_def]) >>
  `!H. valid_horizon cx st0 H p.storage_trace ==>
    ghost_inv_at (DF H) lo d ce cx ee (G |+ (data,snapshot_base,cap))
      (tn with <|t_var := tn.t_var |+ (len,{}) |+ (data,{});
                 t_mem := tn.t_mem UNION {i | snapshot_base <= i /\ i < snapshot_base + cap}|>) r` by
    (rpt strip_tac >> irule raw_snapshot_entry_ghost >>
     suspend "ghost") >>
  `snapshot_base + cap <= r.vs_alloca_next` by
    (qpat_assum `!H. valid_horizon _ _ _ _ ==> stmt_state_rel _ _ _ _ _ _ r` drule >>
     simp_tac (srw_ss()) [stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >>
     strip_tac >> qpat_assum `!aid b sz. FLOOKUP r.vs_allocas aid = _ ==> _` irule >>
     qexists_tac `a.cs_next_id` >> metis_tac[]) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp r)` by
    (qpat_assum `!H. valid_horizon _ _ _ _ ==> stmt_state_rel _ _ _ _ _ _ r` drule >>
     metis_tac[stmt_state_rel_allocas_below_fmp]) >>
  qexistsl_tac [`G |+ (data,snapshot_base,cap)`,
    `tn with <|t_var := tn.t_var |+ (len,{}) |+ (data,{});
               t_mem := tn.t_mem UNION {i | snapshot_base <= i /\ i < snapshot_base + cap}|>`] >>
  suspend "conclude"
QED
Resume raw_snapshot_finish_entry[ghost]:
  `lo <= u.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `lo <= r.vs_alloca_next` by metis_tac[GREATER_EQ, LESS_EQ_TRANS] >>
  `allocas_from lo r` by (simp_tac (srw_ss()) [allocas_from_def] >> metis_tac[allocas_from_def]) >>
  `FLOOKUP r.vs_allocas a.cs_next_id = SOME (snapshot_base,cap)` by metis_tac[] >>
  `lo <= snapshot_base` by (fs[allocas_from_def] >> metis_tac[]) >>
  simp[] >> qexistsl_tac [`a`,`func`,`u`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (qpat_assum `!H. valid_horizon _ _ _ _ ==> _ /\ _` (drule_then strip_assume_tac) >>
       drule stateRelProjTheory.stmt_state_rel_local_ptrs_alloca >> simp[] >> NO_TAC) >>
  qpat_assum `v = update_var _ _ _` SUBST1_TAC >>
  simp[update_var_def,buffer_allocation_fields_def,AllCaseEqs()] >>
  every_case_tac >> gs[]
QED
Resume raw_snapshot_finish_entry[conclude]:
  `w2n (n2w (snapshot_base + 32) : bytes32) = snapshot_base+32` by
    (simp_tac (srw_ss()) [w2n_n2w,LESS_MOD] >> first_assum ACCEPT_TAC) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (rpt strip_tac >> first_assum irule >> first_assum ACCEPT_TAC)
  >- (qpat_assum `r.vs_halted <=> v.vs_halted` (fn th => PURE_REWRITE_TAC[th]) >>
      qpat_assum `v = update_var _ _ _` SUBST1_TAC >>
      Cases_on `FLOOKUP u.vs_allocas a.cs_next_id` >>
      simp[update_var_def,buffer_allocation_fields_def])
  >- metis_tac[]
  >- simp[op_taint_def, FLOOKUP_UPDATE]
  >- (simp_tac (srw_ss()) [ptr_covers_def,op_taint_def,FLOOKUP_UPDATE] >>
      qexists_tac `n2w (snapshot_base + 32)` >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac) >>
  `w2n (n2w (buffer_allocation_base u a.cs_next_id + 32) : bytes32) = snapshot_base + 32` by metis_tac[] >>
  qpat_assum `w2n (n2w (buffer_allocation_base u a.cs_next_id + 32):bytes32) = _`
    (fn th => PURE_REWRITE_TAC [REWRITE_RULE [w2n_n2w] th]) >>
  decide_tac
QED
Finalise raw_snapshot_finish_entry[local]

(* The raw result of the allocation and its cursor-advanced view have the
   same operands and memory. The loop certificate uses the latter. *)
Theorem raw_snapshot_alloc_operands[local]:
  compile_alloc_buffer cap a = (buf,m) /\ cap < dimword (:256) ==>
  ?root v. buf.buf_operand = Var root /\
    step_inst_base (mk_inst a.cs_next_id ALLOCA [Lit (n2w cap)] [root]) u = OK v /\
    run_inst_seq (emitted_insts a m) u = OK v /\
    m.cs_current_insts = a.cs_current_insts ++ emitted_insts a m /\
    m.cs_current_bb = a.cs_current_bb /\
    LENGTH m.cs_current_insts = SUC (LENGTH a.cs_current_insts) /\
    m.cs_next_var = a.cs_next_var + 1 /\
    v.vs_current_bb = u.vs_current_bb /\ v.vs_memory = u.vs_memory /\
    v.vs_inst_idx = u.vs_inst_idx /\ copy_old_operand m (Var root) /\
    eval_operand (Var root) v = SOME (n2w (buffer_allocation_base u a.cs_next_id)) /\
    (!op. copy_old_operand a op ==>
       copy_old_operand m op /\ eval_operand op v = eval_operand op u)
Proof
  strip_tac >> drule compile_alloc_buffer_parts >> strip_tac >>
  drule abiBufferAllocationCodeTheory.compile_alloc_buffer_code >> strip_tac >>
  drule_all unwrap_alloc_generated_step >> disch_then (qspec_then `u` strip_assume_tac) >>
  gvs[] >> simp[run_inst_seq_def, copy_old_operand_def] >>
  Cases_on `FLOOKUP u.vs_allocas a.cs_next_id` >>
  simp[buffer_allocation_fields_def, update_var_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  gen_tac >> Cases_on `op` >>
  rw[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem raw_snapshot_labels_append[local]:
  cs_extends a b /\ added_labels a b = [] ==>
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b
Proof
  simp[cs_extends_def] >> strip_tac >>
  `new = []` by
    (qpat_x_assum `added_labels _ _ = _` mp_tac >>
     Cases_on `new` >> simp[added_labels_def, all_blocks_def, LENGTH_NIL]) >>
  fs[rich_listTheory.IS_PREFIX_APPEND, emitted_insts_def, DROP_LENGTH_APPEND]
QED

Theorem raw_snapshot_imm_code[local]:
  vv_location vv = SOME LocCode /\
  compile_alloc_buffer (type_memory_bytes ce ty) a = (buf,m) /\
  compile_create_snapshot ce vv ty a = (snap,b) ==>
  snap = buf.buf_operand /\
  compile_imm_copy_to_memory ce.ce_is_ctor ce.ce_imm_alloca (vv_operand vv) snap
    ((type_memory_bytes ce (vv_type vv) + 31) DIV 32) 0 m = ((),b) /\
  cs_extends m b /\ b.cs_current_insts = m.cs_current_insts ++ emitted_insts m b
Proof
  strip_tac >>
  qpat_x_assum `compile_create_snapshot _ _ _ _ = _` mp_tac >>
  simp[compile_create_snapshot_def,comp_bind_def,comp_return_def,comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  qmatch_asmsub_abbrev_tac `compile_imm_copy_to_memory _ _ src dst n 0 m` >>
  qspecl_then [`n`,`ce.ce_is_ctor`,`ce.ce_imm_alloca`,`src`,`dst`,`0`,`m`,`K F`]
    mp_tac compile_imm_copy_to_memory_labels >>
  simp[] >> Cases_on `added_labels m b` >> simp[raw_snapshot_labels_append]
QED

Theorem raw_snapshot_mem_code[local]:
  (vv_location vv = NONE \/ vv_location vv = SOME LocMemory) /\
  compile_alloc_buffer (type_memory_bytes ce ty) a = (buf,m) /\
  compile_create_snapshot ce vv ty a = (snap,b) ==>
  snap = buf.buf_operand /\
  cs_extends m b /\ b.cs_current_insts = m.cs_current_insts ++ emitted_insts m b /\
  ?cnt len bl bc. emit_op MLOAD [vv_operand vv] m = (len,bl) /\
    emit_op ADD [len;Lit 32w] bl = (cnt,bc) /\
    compile_copy_memory_dynamic snap (vv_operand vv) cnt bc = ((),b)
Proof
  strip_tac >> qpat_x_assum `compile_create_snapshot _ _ _ _ = _` mp_tac >>
  simp[compile_create_snapshot_def,comp_bind_def,comp_return_def,comp_ignore_bind_def] >>
  Cases_on `emit_op MLOAD [vv_operand vv] m` >>
  rename1 `emit_op MLOAD _ m = (len,bl)` >> simp[] >>
  Cases_on `emit_op ADD [len;Lit 32w] bl` >>
  rename1 `emit_op ADD _ bl = (cnt,bc)` >> simp[] >>
  Cases_on `compile_copy_memory_dynamic buf.buf_operand (vv_operand vv) cnt bc` >>
  simp[] >> strip_tac >> gvs[] >>
  imp_res_tac emitted_insts_emit_op >>
  `emit_void MCOPY [buf.buf_operand;vv_operand vv;cnt] bc = ((),b)` by
    fs[compile_copy_memory_dynamic_def] >>
  imp_res_tac emitted_insts_emit_void >>
  `ci_mono m bl /\ ci_mono bl bc /\ ci_mono bc b` by
    metis_tac[ci_mono_emit_op,ci_mono_emit_void,pairTheory.SND] >>
  `cs_extends m b` by metis_tac[ci_mono_trans,ci_mono_def] >>
  asm_rewrite_tac[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC,DROP_LENGTH_APPEND] >> simp[]
QED

Theorem raw_snapshot_slot_code[local]:
  vv_location vv = SOME (slot_loc tr) /\
  compile_alloc_buffer (type_memory_bytes ce ty) a = (buf,m) /\
  compile_create_snapshot ce vv ty a = (snap,b) ==>
  snap = buf.buf_operand /\
  b = slot_copy_final m (vv_operand vv) snap
    ((type_memory_bytes ce ty + 31) DIV 32) (if tr then TLOAD else SLOAD)
Proof
  strip_tac >> Cases_on `tr` >>
  gvs[compile_create_snapshot_def,comp_bind_def,comp_ignore_bind_def,comp_return_def,
      slot_loc_def,compile_slot_to_memory_shape,AllCaseEqs()]
QED

Theorem raw_snapshot_typed_capacity[local]:
  expr_body_pre ce cx env e es /\ expr_type e = BaseT (BytesT (Dynamic k)) /\ k <= 49152 /\
  compile_expr ce (expr_type e) e sa = (vv,a) /\
  eval_expr cx e (es with gas_obs := obs) = (INL tv,p) /\
  read_result cx tv p = (INL (BytesV code),p) /\
  vv_post H ctx func ce cx e es sa a s0 (p with gas_obs := []) tv vv u ==>
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic k))) = SOME (BaseTV (BytesT (Dynamic k))) /\
  LENGTH code + 32 <= type_memory_bytes ce (lowered_value_type ce e) /\
  type_memory_bytes ce (lowered_value_type ce e) < dimword (:256) /\
  32 * ((type_memory_bytes ce (lowered_value_type ce e) + 31) DIV 32) =
    type_memory_bytes ce (lowered_value_type ce e) /\
  (vv_location vv = SOME LocCode ==>
    type_memory_bytes ce (vv_type vv) = type_memory_bytes ce (lowered_value_type ce e))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_body_pre ce cx env e (es with gas_obs := obs)` by simp[expr_body_pre_gas_obs] >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := obs) = (INL (BytesV code),p)` by
    simp[vyperStateTheory.bind_def] >>
  drule_all create_blueprint_raw_copy_layout >> strip_tac >>
  rename1 `lowered_value_type ce e = BaseT (BytesT (Dynamic kl))` >>
  `type_memory_bytes ce (lowered_value_type ce e) = type_memory_size (BaseTV (BytesT (Dynamic kl)))` by
    (pure_rewrite_tac[] >> metis_tac[typeLayoutPropsTheory.type_memory_bytes_base_evaluated]) >>
  drule expr_body_pre_static_facts >> strip_tac >>
  drule expr_body_pre_lowered_fits >> strip_tac >>
  `type_memory_bytes ce (lowered_value_type ce e) <= type_memory_bytes ce (expr_type e)` by
    metis_tac[abi_args_fits_memory_bytes] >>
  `LENGTH code <= 32 * word_size (LENGTH code)` by simp[word_size_capacity] >>
  `LENGTH code + 32 <= type_memory_bytes ce (lowered_value_type ce e)` by
    (qpat_assum `val_store_size _ _ <= type_memory_size (BaseTV (BytesT (Dynamic kl)))`
       mp_tac >>
     qpat_assum `type_memory_bytes ce (lowered_value_type ce e) = type_memory_size _`
       (fn th => pure_rewrite_tac[GSYM th]) >>
     simp[exprSimPropsTheory.val_store_size_def]) >>
  `type_memory_bytes ce (expr_type e) <= type_memory_bytes ce (BaseT (BytesT (Dynamic 49152)))` by
    (`(k+31) DIV 32 <= (49152+31) DIV 32` by
       (irule arithmeticTheory.DIV_LE_MONOTONE >> decide_tac) >>
     fs[type_memory_bytes_def] >> decide_tac) >>
  `type_memory_bytes ce (BaseT (BytesT (Dynamic 49152))) < dimword (:256)` by
    (simp[dimword_def,type_memory_bytes_def]) >>
  `type_memory_bytes ce (lowered_value_type ce e) < dimword (:256)` by decide_tac >>
  simp[] >> conj_tac
  >- (qpat_assum `type_memory_bytes ce (lowered_value_type ce e) = type_memory_size _`
        (fn th => pure_rewrite_tac[th,type_memory_size_slots]) >>
      simp[Once MULT_COMM, ADD_DIV_ADD_DIV]) >>
  strip_tac >> Cases_on `vv` >> gvs[vv_location_def,vv_type_def] >>
  drule_all vv_post_located_type >> simp[] >> strip_tac >>
  `lowered_value_type ce e = expr_type e` by (drule external_located_lowered_type >> simp[]) >>
  `post_value_type ce e = expr_type e` by simp[is_bytestring_type_def] >>
  `BaseT (BytesT (Dynamic q)) = BaseT (BytesT (Dynamic kl))` by
    metis_tac[] >>
  `q = kl` by (qpat_x_assum `BaseT (BytesT (Dynamic q)) = BaseT (BytesT (Dynamic kl))` mp_tac >> simp[]) >>
  simp[]
QED

Theorem raw_snapshot_straight_after_alloc[local]:
  m.cs_current_insts = a.cs_current_insts ++ emitted_insts a m /\
  b.cs_current_insts = m.cs_current_insts ++ emitted_insts m b /\
  run_inst_seq (emitted_insts a m) u = OK v /\
  run_inst_seq (emitted_insts a b) u = OK (z with vs_inst_idx := u.vs_inst_idx) /\
  v.vs_inst_idx = u.vs_inst_idx ==>
  run_inst_seq (emitted_insts m b) v = OK (z with vs_inst_idx := v.vs_inst_idx)
Proof
  strip_tac >>
  `emitted_insts a b = emitted_insts a m ++ emitted_insts m b` by metis_tac[emitted_insts_append] >>
  metis_tac[run_inst_seq_append]
QED

Theorem raw_snapshot_memory_header[local]:
  vv_holds ce cx (BaseT (BytesT (Dynamic k))) tv vv ee u /\
  read_result cx tv ee = (INL (BytesV code),ee) /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic k))) = SOME (BaseTV (BytesT (Dynamic k))) /\
  (vv_location vv = NONE \/ vv_location vv = SOME LocMemory) ==>
  ?s. eval_operand (vv_operand vv) u = SOME s /\ mload (w2n s) u = n2w (LENGTH code)
Proof
  Cases_on `vv` >>
  simp[vv_holds_def,vv_operand_def,vv_location_def,expr_val_rel_def,is_word_type_def] >>
  strip_tac >> gvs[val_in_memory_def,mem_word_at_eq_mload] >> metis_tac[]
QED

Theorem raw_snapshot_copy_footprint[local]:
  compile_alloc_buffer cap a = (buf,m) /\
  compile_create_snapshot ce vv ty a = (snap,b) /\ cap = type_memory_bytes ce ty /\
  fn_has_code a b func /\ B = buffer_allocation_base u a.cs_next_id /\
  B + cap < dimword (:256) /\ LENGTH code + 32 <= cap /\
  32 * ((cap + 31) DIV 32) = cap /\
  (vv_location vv = SOME LocCode ==> type_memory_bytes ce (vv_type vv) = cap) /\
  (vv_location vv = NONE \/ vv_location vv = SOME LocMemory \/ vv_location vv = SOME LocCode \/
    ?tr. vv_location vv = SOME (slot_loc tr)) /\
  local_ptrs_reserved ce a /\ stmt_state_rel H ctx func ce cx ee u /\
  vv_holds ce cx (BaseT (BytesT (Dynamic k))) tv vv ee u /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic k))) = SOME (BaseTV (BytesT (Dynamic k))) /\
  read_result cx tv ee = (INL (BytesV code),ee) /\ copy_old_operand a (vv_operand vv) /\
  u.vs_current_bb = a.cs_current_bb /\ u.vs_inst_idx = LENGTH a.cs_current_insts /\
  v.vs_current_bb = u.vs_current_bb /\ v.vs_memory = u.vs_memory /\ v.vs_inst_idx = u.vs_inst_idx /\
  run_inst_seq (emitted_insts a m) u = OK v /\
  m.cs_current_insts = a.cs_current_insts ++ emitted_insts a m /\
  m.cs_current_bb = a.cs_current_bb /\ LENGTH m.cs_current_insts = SUC (LENGTH a.cs_current_insts) /\
  buf.buf_operand = Var root /\
  copy_old_operand m buf.buf_operand /\ eval_operand buf.buf_operand v = SOME (n2w B) /\
  (!op. copy_old_operand a op ==> copy_old_operand m op /\ eval_operand op v = eval_operand op u) /\
  ((vv_location vv = NONE \/ vv_location vv = SOME LocMemory \/ vv_location vv = SOME LocCode) ==>
    run_inst_seq (emitted_insts a b) u = OK (z with vs_inst_idx := u.vs_inst_idx)) /\
  ((!tr. vv_location vv = SOME (slot_loc tr) ==>
    ?y exit. lookup_block b.cs_current_bb func.fn_blocks = SOME exit /\
      phi_prefix_length exit.bb_instructions = 0 /\
      fn_has_code m b func /\
      y.vs_current_bb = m.cs_current_bb /\ y.vs_inst_idx = LENGTH m.cs_current_insts /\
      z.vs_current_bb = b.cs_current_bb /\ z.vs_inst_idx = 0 /\
      run_inst_seq (emitted_insts a m) u = OK (y with vs_inst_idx := u.vs_inst_idx) /\
      RTC (\x t. (x.vs_current_bb <> b.cs_current_bb \/ x.vs_inst_idx <> 0) /\
                 ?ms. gas_origin_edge F explicit ctx func x ms (OK t)) y z)) ==>
  copy_static z = copy_static v /\ LENGTH v.vs_memory <= LENGTH z.vs_memory /\
  copy_old_operand b snap /\ eval_operand snap z = SOME (n2w B) /\
  (!x. not_fresh_at m x ==> lookup_var x z = lookup_var x v) /\
  (!off n. off+n <= B \/ B+cap <= off ==>
    mem_bytes_at off n z.vs_memory = mem_bytes_at off n v.vs_memory)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `w2n (n2w B : bytes32) = B` by (simp_tac (srw_ss()) [w2n_n2w,LESS_MOD] >> decide_tac) >>
  `m.cs_next_var <= b.cs_next_var ==> copy_old_operand b buf.buf_operand` by
    metis_tac[copy_old_operand_mono] >>
  Cases_on `vv_location vv = NONE \/ vv_location vv = SOME LocMemory`
  >- suspend "memory" >>
  Cases_on `vv_location vv = SOME LocCode`
  >- suspend "immutable" >>
  suspend "slot"
QED
Resume raw_snapshot_copy_footprint[memory]:
  `compile_alloc_buffer (type_memory_bytes ce ty) a = (buf,m)` by metis_tac[] >>
  drule_all raw_snapshot_mem_code >> strip_tac >>
  `run_inst_seq (emitted_insts a b) u = OK (z with vs_inst_idx := u.vs_inst_idx)` by metis_tac[] >>
  drule_all raw_snapshot_straight_after_alloc >> strip_tac >>
  `?s. eval_operand (vv_operand vv) u = SOME s /\ mload (w2n s) u = n2w (LENGTH code)` by
    (irule raw_snapshot_memory_header >> metis_tac[]) >>
  qpat_assum `!op. copy_old_operand a op ==> _` (drule_then strip_assume_tac) >>
  `mload (w2n s) v = n2w (LENGTH code)` by fs[mload_def,read_memory_def] >>
  `LENGTH code + 32 < dimword (:256)` by decide_tac >>
  `eval_operand (vv_operand vv) v = SOME s /\
   copy_old_operand m snap /\ eval_operand snap v = SOME (n2w B)` by metis_tac[] >>
  drule_all create_raw_memory_copy_frame >> simp[] >> strip_tac >>
  `ci_mono m b` by
    metis_tac[ci_mono_emit_op,ci_mono_compile_copy_memory_dynamic,ci_mono_trans,pairTheory.SND] >>
  `copy_old_operand b snap` by metis_tac[ci_mono_def] >>
  `eval_operand snap z = SOME (n2w B)` by
    (`not_fresh_at m root` by metis_tac[copy_old_operand_def] >>
     `snap = Var root` by metis_tac[] >>
     `eval_operand (Var root) v = SOME (n2w B)` by metis_tac[] >>
     `lookup_var root z = lookup_var root v` by metis_tac[] >>
     `eval_operand (Var root) z = SOME (n2w B)` by fs[eval_operand_def] >>
     metis_tac[]) >>
  (rpt conj_tac >>> LASTGOAL
    (asm_rewrite_tac[] >> rpt gen_tac >> strip_tac >>
     qpat_assum `!off k. _ ==> mem_bytes_at _ _ z.vs_memory = _` irule >> decide_tac)) >>
  metis_tac[]
QED
Resume raw_snapshot_copy_footprint[immutable]:
  `compile_alloc_buffer (type_memory_bytes ce ty) a = (buf,m)` by metis_tac[] >>
  drule_all raw_snapshot_imm_code >> strip_tac >>
  `run_inst_seq (emitted_insts a b) u = OK (z with vs_inst_idx := u.vs_inst_idx)` by metis_tac[] >>
  drule_all raw_snapshot_straight_after_alloc >> strip_tac >>
  drule attribute_vv_holds_read_operand >> strip_tac >>
  `?w. eval_operand (vv_operand vv) v = SOME w /\ copy_old_operand m (vv_operand vv)` by metis_tac[] >>
  `copy_old_operand m snap /\ eval_operand snap v = SOME (n2w B)` by metis_tac[] >>
  `(ce.ce_is_ctor ==> !op. ce.ce_imm_alloca = SOME op ==>
      copy_old_operand m op /\ eval_operand op v = SOME 0w)` by
    (rpt strip_tac >>
     `copy_old_operand a op` by (simp[copy_old_operand_def] >> metis_tac[local_ptrs_reserved_imm_base]) >>
     drule stmt_state_rel_immutable_base_zero >>
     simp[loweringStateRelDefsTheory.immutable_base_zero_def] >> metis_tac[]) >>
  `32 * ((type_memory_bytes ce (vv_type vv) + 31) DIV 32) = cap` by metis_tac[] >>
  `w2n (n2w B : bytes32) + 32 * ((type_memory_bytes ce (vv_type vv) + 31) DIV 32)
     < dimword (:256)` by metis_tac[] >>
  drule_all create_raw_immutable_copy_frame >> strip_tac >>
  `ci_mono m b` by metis_tac[ci_mono_compile_imm_copy_to_memory,pairTheory.SND] >>
  `copy_old_operand b snap` by metis_tac[ci_mono_def] >>
  `eval_operand snap z = SOME (n2w B)` by
    (`snap = Var root` by metis_tac[] >>
     `not_fresh_at m root` by metis_tac[copy_old_operand_def] >>
     `lookup_var root z = lookup_var root v` by metis_tac[] >>
     `eval_operand (Var root) v = SOME (n2w B)` by metis_tac[] >>
     `eval_operand (Var root) z = SOME (n2w B)` by fs[eval_operand_def] >> metis_tac[]) >>
  (rpt conj_tac >>> LASTGOAL
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!off k. _ ==> mem_bytes_at _ _ z.vs_memory = _` irule >> simp[])) >>
  metis_tac[]
QED
Resume raw_snapshot_copy_footprint[slot]:
  `?tr. vv_location vv = SOME (slot_loc tr)` by metis_tac[] >> pop_assum strip_assume_tac >>
  `compile_alloc_buffer (type_memory_bytes ce ty) a = (buf,m)` by metis_tac[] >>
  drule_all raw_snapshot_slot_code >> strip_tac >>
  qpat_assum `!tr. vv_location vv = SOME (slot_loc tr) ==> _` (drule_then strip_assume_tac) >>
  `v = y with vs_inst_idx := u.vs_inst_idx` by metis_tac[optionTheory.SOME_11,exec_result_11] >>
  drule attribute_vv_holds_read_operand >> strip_tac >>
  `eval_operand (vv_operand vv) v = SOME w /\ copy_old_operand m (vv_operand vv) /\
   copy_old_operand m snap /\ eval_operand snap v = SOME (n2w B)` by metis_tac[] >>
  `eval_operand (vv_operand vv) y = SOME w /\ eval_operand snap y = SOME (n2w B)` by
    (qpat_assum `v = y with vs_inst_idx := _` (fn th =>
       qpat_assum `eval_operand (vv_operand vv) v = SOME w` (mp_tac o REWRITE_RULE [th]) >>
       qpat_assum `eval_operand snap v = SOME (n2w B)` (mp_tac o REWRITE_RULE [th])) >> simp[]) >>
  `slot_copy_external m (vv_operand vv) /\ slot_copy_external m snap` by
    (`!op. copy_old_operand m op ==> slot_copy_external m op` by
       (Cases >> simp[copy_old_operand_def,slot_copy_external_def] >>
        metis_tac[slot_copy_not_fresh_external,slot_copy_external_def]) >> metis_tac[]) >>
  qabbrev_tac `n = (cap + 31) DIV 32` >>
  qabbrev_tac `load = if tr then TLOAD else SLOAD` >>
  `b = slot_copy_final m (vv_operand vv) snap n load` by simp[Abbr `n`,Abbr `load`] >>
  `m.cs_next_var <= b.cs_next_var /\ b.cs_current_bb = slot_copy_exit m` by
    (qpat_assum `b = slot_copy_final _ _ _ n load` SUBST1_TAC >> simp[slot_copy_final_def]) >>
  Q.SUBGOAL_THEN `load = SLOAD \/ load = TLOAD` assume_tac
  >- (Cases_on `tr` >> simp[Abbr `load`]) >>
  `32*n = cap` by simp[Abbr `n`] >>
  `w2n (n2w B : bytes32) + 32*n < 2 ** 256 /\ n < 2 ** 256` by
    (RULE_ASSUM_TAC (REWRITE_RULE [dimword_def,dimindex_256]) >>
     pure_rewrite_tac[] >> metis_tac[DECIDE ``(n:num) <= 32*n``, LESS_EQ_LESS_TRANS, DECIDE ``a+b < c ==> a < c /\ b < c``]) >>
  `slot_copy_runtime_frame m (n2w B : bytes32) n y z /\ eval_operand snap z = SOME (n2w B)` by
    (`fn_has_code m (slot_copy_final m (vv_operand vv) snap n load) func` by metis_tac[] >>
     qpat_assum `b.cs_current_bb = slot_copy_exit m` (fn th =>
       qpat_assum `RTC _ y z` (assume_tac o REWRITE_RULE [th]) >>
       qpat_assum `lookup_block b.cs_current_bb _ = _` (assume_tac o REWRITE_RULE [th])) >>
     `z.vs_current_bb = slot_copy_exit m` by metis_tac[] >>
     Q.SUBGOAL_THEN `m.cs_current_bb <> slot_copy_exit m \/ 0 < LENGTH m.cs_current_insts` assume_tac
     >- simp[] >>
     drule_all create_slot_copy_actual_exit_frame >>
     disch_then (mp_tac o REWRITE_RULE [CONJ_ASSOC]) >>
     disch_then (map_every assume_tac o CONJUNCTS) >> gvs[]) >>
  `32*n <= cap` by decide_tac >>
  drule_all slot_copy_semantic_frame >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `copy_static y = copy_static v /\ y.vs_memory = v.vs_memory /\
   (!x. lookup_var x y = lookup_var x v)` by
    (qpat_assum `v = y with vs_inst_idx := _` SUBST1_TAC >> simp[copy_static_def,lookup_var_def]) >>
  `copy_old_operand b snap` by metis_tac[] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- metis_tac[]
  >- metis_tac[]
  >- (rpt strip_tac >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `off+n' <= w2n (n2w B : bytes32) \/ w2n (n2w B : bytes32) + cap <= off` by metis_tac[] >>
  metis_tac[]
QED
Finalise raw_snapshot_copy_footprint[local]

Theorem raw_snapshot_alloc_embedded[local]:
  compile_alloc_buffer (type_memory_bytes ce ty) a = (buf,m) /\
  compile_create_snapshot ce vv ty a = (snap,b) /\ fn_has_code a b func /\
  (vv_location vv = NONE \/ vv_location vv = SOME LocMemory \/ vv_location vv = SOME LocCode \/
    ?tr. vv_location vv = SOME (slot_loc tr)) ==>
  fn_has_code a m func
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `cs_extends a m` by metis_tac[ci_mono_compile_alloc_buffer,ci_mono_def,pairTheory.SND] >>
  `cs_extends m b` by
    (Cases_on `vv_location vv = NONE \/ vv_location vv = SOME LocMemory`
     >- (drule_all raw_snapshot_mem_code >> simp[]) >>
     Cases_on `vv_location vv = SOME LocCode`
     >- (drule_all raw_snapshot_imm_code >> simp[]) >>
     `?tr. vv_location vv = SOME (slot_loc tr)` by metis_tac[] >>
     drule_all raw_snapshot_slot_code >> metis_tac[slot_copy_extends]) >>
  metis_tac[fn_has_code_split]
QED

(* The states u, z, l and r are the actual exits of the bytecode operand,
   snapshot copy, header read and data-pointer computation, respectively. *)
Theorem create_raw_snapshot_payload_entry:
  expr_body_pre ce cx env e es /\ expr_type e = BaseT (BytesT (Dynamic k)) /\ k <= 49152 /\
  compile_expr ce (expr_type e) e sa = (vv,a) /\
  eval_expr cx e (es with gas_obs := obs) = (INL tv,p) /\
  read_result cx tv p = (INL (BytesV code),p) /\
  read_result cx tv (p with gas_obs := []) = (INL (BytesV code),p with gas_obs := []) /\
  valid_horizon cx st0 H p.storage_trace /\
  vv_post H ctx func ce cx e es sa a s0 (p with gas_obs := []) tv vv u /\
  (!h. valid_horizon cx st0 h p.storage_trace ==>
      stmt_state_rel h ctx func ce cx (p with gas_obs := []) u /\
      storage_well_formed_on cx (p with gas_obs := []) (FST h) /\
      ghost_inv_at (DF h) lo d ce cx (p with gas_obs := []) G tn u) /\
  return_buf_frame d ce a u /\ alloca_history func u /\ ~u.vs_halted /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce a /\ fn_inst_ids_distinct func /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at a x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at a x) /\
  compile_create_snapshot ce vv (lowered_value_type ce e) a = (snap,b) /\
  emit_op MLOAD [snap] b = (len_op,c) /\ emit_op ADD [snap; Lit 32w] c = (data_op,ac) /\
  fn_has_code a b func /\
  u.vs_current_bb = a.cs_current_bb /\ u.vs_inst_idx = LENGTH a.cs_current_insts /\
  r.vs_current_bb = ac.cs_current_bb /\ r.vs_inst_idx = LENGTH ac.cs_current_insts /\
  ((vv_location vv = NONE \/ vv_location vv = SOME LocMemory \/ vv_location vv = SOME LocCode) ==>
    run_inst_seq (emitted_insts a b) u = OK (z with vs_inst_idx := u.vs_inst_idx)) /\
  (!tr. vv_location vv = SOME (slot_loc tr) ==>
    ?buf m y exit. compile_alloc_buffer (type_memory_bytes ce (lowered_value_type ce e)) a = (buf,m) /\
      fn_has_code m b func /\ lookup_block b.cs_current_bb func.fn_blocks = SOME exit /\
      phi_prefix_length exit.bb_instructions = 0 /\
      y.vs_current_bb = m.cs_current_bb /\ y.vs_inst_idx = LENGTH m.cs_current_insts /\
      z.vs_current_bb = b.cs_current_bb /\ z.vs_inst_idx = 0 /\
      run_inst_seq (emitted_insts a m) u = OK (y with vs_inst_idx := u.vs_inst_idx) /\
      RTC (\x t. (x.vs_current_bb <> b.cs_current_bb \/ x.vs_inst_idx <> 0) /\
                 ?ms. gas_origin_edge F explicit ctx func x ms (OK t)) y z) /\
  run_inst_seq (emitted_insts b c) z = OK (l with vs_inst_idx := z.vs_inst_idx) /\
  run_inst_seq (emitted_insts c ac) l = OK (r with vs_inst_idx := l.vs_inst_idx) /\
  RTC (\x t. ?ms. gas_origin_edge F explicit ctx func x ms (OK t)) u r /\
  eval_operand len_op l = SOME (n2w (LENGTH code)) ==>
  ?Gr tnr len data.
    len_op = Var len /\ data_op = Var data /\
    (!h. valid_horizon cx st0 h p.storage_trace ==>
       stmt_state_rel h ctx func ce cx (p with gas_obs := []) r /\
       storage_well_formed_on cx (p with gas_obs := []) (FST h) /\
       ghost_inv_at (DF h) lo d ce cx (p with gas_obs := []) Gr tnr r) /\
    return_buf_frame d ce ac r /\ alloca_history func r /\ ~r.vs_halted /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp r) /\
    r.vs_current_bb = ac.cs_current_bb /\ r.vs_inst_idx = LENGTH ac.cs_current_insts /\
    FLOOKUP r.vs_allocas a.cs_next_id =
      SOME (buffer_allocation_base u a.cs_next_id,type_memory_bytes ce (lowered_value_type ce e)) /\
    lookup_var len r = SOME (n2w (LENGTH code)) /\
    lookup_var data r = SOME (n2w (buffer_allocation_base u a.cs_next_id + 32)) /\
    not_fresh_at ac len /\ not_fresh_at ac data /\
    op_taint tnr (Var len) = {} /\ ptr_covers Gr tnr data r (LENGTH code) /\
    w2n (n2w (buffer_allocation_base u a.cs_next_id + 32) : bytes32) + LENGTH code <= r.vs_alloca_next
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all raw_snapshot_typed_capacity >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all reasonEndpointResourcesPtrTheory.compile_expr_old_operand >> strip_tac >>
  Q.SUBGOAL_THEN
    `vv_location vv = NONE \/ vv_location vv = SOME LocMemory \/ vv_location vv = SOME LocCode \/
     ?tr. vv_location vv = SOME (slot_loc tr)` assume_tac
  >- (Cases_on `vv` >> simp[vv_location_def] >>
      rename1 `vv_post H ctx func ce cx e es sa a s0 _ tv (LocatedValue _ pp) u` >>
      drule vv_post_not_calldata >> Cases_on `pp.ptr_location` >> simp[slot_loc_def] >> metis_tac[]) >>
  qabbrev_tac `cap = type_memory_bytes ce (lowered_value_type ce e)` >>
  qabbrev_tac `B = buffer_allocation_base u a.cs_next_id` >>
  Cases_on `compile_alloc_buffer cap a` >> rename1 `_ = (buf,m)` >>
  `fn_has_code a m func` by (irule raw_snapshot_alloc_embedded >> metis_tac[]) >>
  `?v root. buf.buf_operand = Var root /\
    step_inst_base (mk_inst a.cs_next_id ALLOCA [Lit (n2w cap)] [root]) u = OK v /\
    run_inst_seq (emitted_insts a m) u = OK v /\
    m.cs_current_insts = a.cs_current_insts ++ emitted_insts a m /\
    m.cs_current_bb = a.cs_current_bb /\ LENGTH m.cs_current_insts = SUC (LENGTH a.cs_current_insts) /\
    m.cs_next_var = a.cs_next_var + 1 /\
    v.vs_current_bb = u.vs_current_bb /\ v.vs_memory = u.vs_memory /\ v.vs_inst_idx = u.vs_inst_idx /\
    copy_old_operand m buf.buf_operand /\ eval_operand buf.buf_operand v = SOME (n2w B) /\
    (!op. copy_old_operand a op ==> copy_old_operand m op /\ eval_operand op v = eval_operand op u)` by
    (drule_all raw_snapshot_alloc_operands >>
     disch_then (qspec_then `u` strip_assume_tac) >> qexistsl_tac [`v`,`root`] >> simp[Abbr `B`]) >>
  qpat_assum `!h. valid_horizon _ _ h _ ==> _ /\ _` (drule_then strip_assume_tac) >>
  `B + cap < dimword (:256)` by (drule_all unwrap_alloc_site_bound >> simp[Abbr `B`]) >>
  `alloca_inv u` by metis_tac[stmt_state_rel_local_ptrs_alloca] >>
  `alloca_history func r` by (drule_all create_raw_ok_rtc_alloca_history >> simp[]) >>
  `vv_holds ce cx (BaseT (BytesT (Dynamic k))) tv vv (p with gas_obs := []) u` by
    (`post_value_type ce e = BaseT (BytesT (Dynamic k))` by
       (irule EQ_TRANS >> qexists_tac `expr_type e` >>
        simp[post_value_type_bytestring,is_bytestring_type_def]) >>
     fs[vv_post_def]) >>
  suspend "frame"
QED
Resume create_raw_snapshot_payload_entry[frame]:
  `cap = type_memory_bytes ce (lowered_value_type ce e) /\ B = buffer_allocation_base u a.cs_next_id` by
    simp[Abbr `cap`,Abbr `B`] >>
  `!tr. vv_location vv = SOME (slot_loc tr) ==>
    ?y exit. lookup_block b.cs_current_bb func.fn_blocks = SOME exit /\
      phi_prefix_length exit.bb_instructions = 0 /\ fn_has_code m b func /\
      y.vs_current_bb = m.cs_current_bb /\ y.vs_inst_idx = LENGTH m.cs_current_insts /\
      z.vs_current_bb = b.cs_current_bb /\ z.vs_inst_idx = 0 /\
      run_inst_seq (emitted_insts a m) u = OK (y with vs_inst_idx := u.vs_inst_idx) /\
      RTC (\x t. (x.vs_current_bb <> b.cs_current_bb \/ x.vs_inst_idx <> 0) /\
                 ?ms. gas_origin_edge F explicit ctx func x ms (OK t)) y z` by
    (gen_tac >> disch_tac >>
     qpat_assum `!tr. vv_location vv = SOME (slot_loc tr) ==> _` (drule_then strip_assume_tac) >>
     qpat_x_assum `(buf,m) = (_,_)`
       (map_every (SUBST_ALL_TAC o SYM) o CONJUNCTS o REWRITE_RULE [pairTheory.PAIR_EQ]) >>
     qexistsl_tac [`y`,`exit`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule_all raw_snapshot_copy_footprint >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all create_raw_snapshot_scalar_frame >> strip_tac >>
  `a.cs_next_var <= m.cs_next_var` by simp[] >>
  `a.cs_next_var <= b.cs_next_var` by
    metis_tac[ci_mono_compile_create_snapshot,ci_mono_def,pairTheory.SND] >>
  `b.cs_next_var <= ac.cs_next_var` by
    metis_tac[ci_mono_emit_op,ci_mono_trans,ci_mono_def,pairTheory.SND] >>
  suspend "join"
QED
Resume create_raw_snapshot_payload_entry[join]:
  `a.cs_next_var <= ac.cs_next_var` by decide_tac >>
  `~not_fresh_at a len /\ ~not_fresh_at a data` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `copy_static r = copy_static v /\ LENGTH v.vs_memory <= LENGTH r.vs_memory` by
    metis_tac[] >>
  `!x. not_fresh_at a x ==> lookup_var x r = lookup_var x v` by
    (rpt strip_tac >>
     `not_fresh_at m x /\ not_fresh_at b x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
     metis_tac[]) >>
  `!off n. off+n <= B \/ B+cap <= off ==>
    mem_bytes_at off n r.vs_memory = mem_bytes_at off n v.vs_memory` by metis_tac[] >>
  Q.SUBGOAL_THEN `?h. valid_horizon cx st0 h p.storage_trace` assume_tac
  >- (qexists_tac `H` >> first_assum ACCEPT_TAC) >>
  drule_all raw_snapshot_finish_entry >> strip_tac >>
  qexistsl_tac [`Gr`,`tnr`,`len`,`data`] >> asm_rewrite_tac[]
QED
Finalise create_raw_snapshot_payload_entry
