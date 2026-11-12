Theory bodyPtrIfExpOldOperandAllocation
Ancestors bodyPtrIfExpOldOperandStart bodyPtrIfExpStorageStart
  bodyPtrIfExpAllocCompiler bodyPtrIfExpAllocGhost bodyPtrIfExpAllocKept
  bodyPtrDefs loweringPosts compileEnv venomState venomInst exprSimPtrLiteralBuffer stmtFragPtr

Theorem ifexp_old_source_allocation_start:
  vv_post ctx fn ce cx e es sa sb s0 ee raw vv s /\
  ghost_inv rty ce cx ee G tn s /\ ghost_kept ce es sa G0 tn0 s0 G tn /\
  local_ptrs_reserved ce sa /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sb.cs_next_var /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  compile_alloc_buffer capacity sb = (buf,cs) /\ fn_has_code sb cs fn /\
  capacity < dimword (:256) /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  copy_old_operand sb src /\ eval_operand src s = SOME p /\ op_taint tn src = {} ==>
  ?out u G1 tn1.
    buf.buf_operand = Var out /\
    step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w capacity)] [out]) s = OK u /\
    G1 = step_prov PG G (mk_inst sb.cs_next_id ALLOCA [Lit (n2w capacity)] [out]) u /\
    tn1 = step_taint (mk_inst sb.cs_next_id ALLOCA [Lit (n2w capacity)] [out]) s u tn /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK (u with vs_inst_idx := SUC s.vs_inst_idx)) /\
    ptr_covers G1 tn1 out (u with vs_inst_idx := SUC s.vs_inst_idx) capacity /\
    ghost_inv rty ce cx ee G1 tn1 (u with vs_inst_idx := SUC s.vs_inst_idx) /\
    ghost_kept ce es sa G0 tn0 s0 G1 tn1 /\
    copy_old_operand cs src /\ copy_old_operand cs (Var out) /\
    eval_operand src (u with vs_inst_idx := SUC s.vs_inst_idx) = SOME p /\
    op_taint tn1 src = {} /\ slot_copy_external cs src /\ slot_copy_external cs (Var out) /\
    (u with vs_inst_idx := SUC s.vs_inst_idx).vs_current_bb = cs.cs_current_bb /\
    (u with vs_inst_idx := SUC s.vs_inst_idx).vs_inst_idx = LENGTH cs.cs_current_insts
Proof
  strip_tac >>
  `stmt_state_rel ctx fn ce cx ee s` by fs[vv_post_def] >>
  drule_all compile_alloc_buffer_counted >>
  disch_then (qspecl_then [`D`, `PG`, `G`, `tn`] strip_assume_tac) >>
  drule_all compile_alloc_buffer_ghost_frame >>
  disch_then (qspec_then `PG` assume_tac) >>
  drule_all compile_alloc_buffer_kept_frame >>
  disch_then (qspec_then `PG` assume_tac) >>
  drule_all ifexp_alloc_old_source >>
  disch_then (qspecl_then [`tn`, `PG`, `G`] strip_assume_tac) >>
  drule_all ifexp_alloc_start_cursor >> strip_tac >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  qexistsl_tac [`out`, `u`, `G1`, `tn1`] >> gvs[] >>
  simp[SRULE [ghost_inv_gas_obs] literal_ptr_ghost_inv_normalize]
QED
