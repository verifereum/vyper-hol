Theory bodyPtrIfExpStorageCaller
Ancestors bodyPtrIfExpStorageAllocation bodyPtrIfExpStorageCountedLoop
  bodyPtrIfExpAllocSource loweringHalt ptrDiscipline compileEnv venomState
  venomInst finite_map words arithmetic fragGasPathPtr decoderGhostFramePtr

Theorem ifexp_copy_allocated_execution:
  stmt_state_rel ctx fn ce cx es s0 /\
  vv_post ctx fn ce cx e es sa sb s0 ee raw vv s /\
  ghost_inv rty ce cx ee G tn s /\ ghost_kept ce es sa G0 tn0 s0 G tn /\
  local_ptrs_reserved ce sa /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  fn_inst_ids_distinct fn /\ sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  compile_alloc_buffer (32*n) sb = (buf,cs) /\ fn_has_code sb cs fn /\
  fn_has_code cs (slot_copy_final cs src buf.buf_operand n load) fn /\
  MEM load [SLOAD;TLOAD] /\ 32*n < dimword (:256) /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  fresh_vars_wrt sb s /\ eval_operand src s = SOME p /\ op_taint tn src = {} /\
  (!j k. j<n /\ k IN (if load=SLOAD then key_taint tn.t_stor (p+n2w j)
    else key_taint tn.t_trans (p+n2w j)) ==> (j,k) IN X) ==>
  ?out u (d:bytes32) GBase tnBase t G' tn'.
    buf.buf_operand = Var out /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    ifexp_copy_ptr_inv ce cx rty es sa s0 G0 tn0 ee cs load src (Var out)
      (u with vs_inst_idx := SUC s.vs_inst_idx) GBase tnBase p d n X n t G' tn' /\
    t.vs_current_bb = slot_copy_exit cs /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
    eval_operand (Var out) t = SOME d /\
    contract_storage u = contract_storage s /\ contract_transient u = contract_transient s /\
    tnBase.t_stor = tn.t_stor /\ tnBase.t_trans = tn.t_trans
Proof
  strip_tac >> drule_all ifexp_copy_allocation_start >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  drule_all ifexp_copy_allocation_loop_bounds >> strip_tac >>
  drule_all alloca_step_contracts >> strip_tac >>
  `sa.cs_next_var <= cs.cs_next_var` by
    (drule compile_alloc_buffer_parts >> strip_tac >> decide_tac) >>
  `fn_has_code cs (slot_copy_final cs src (Var out) n load) fn` by metis_tac[] >>
  `tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans` by
    simp[step_taint_nonmemory_frame, mk_inst_def] >>
  `!j k. j<n /\ k IN (if load=SLOAD then key_taint tn1.t_stor (p+n2w j)
    else key_taint tn1.t_trans (p+n2w j)) ==> (j,k) IN X` by simp[] >>
  `~(u with vs_inst_idx := SUC s.vs_inst_idx).vs_halted` by simp[] >>

  drule_all ifexp_copy_ptr_execution >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `eval_operand (Var out) t = SOME d` by
    (fs[bodyPtrIfExpStorageInvariantTheory.ifexp_copy_ptr_inv_def, slotCopyExecutionTheory.slot_copy_inv_def] >> metis_tac[]) >>
  qexistsl_tac [`out`, `u`, `d`, `G1`, `tn1`, `t`, `G'`, `tn'`] >>
  simp[] >> metis_tac[gas_path_ptr_then, ADD_CLAUSES]
QED
