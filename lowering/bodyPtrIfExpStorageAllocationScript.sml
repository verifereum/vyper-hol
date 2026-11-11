Theory bodyPtrIfExpStorageAllocation
Ancestors bodyPtrIfExpStorageStart bodyPtrIfExpStorageAllocBounds
  bodyPtrIfExpAllocCompiler bodyPtrIfExpAllocGhost bodyPtrIfExpAllocKept
  bodyPtrIfExpBytesEndpoint bodyPtrIfExpAllocSeparation
  loweringPosts compileEnv venomState venomInst words arithmetic

Theorem ifexp_copy_allocation_start:
  vv_post ctx fn ce cx e es sa sb s0 ee raw vv s /\
  ghost_inv rty ce cx ee G tn s /\ ghost_kept ce es sa G0 tn0 s0 G tn /\
  local_ptrs_reserved ce sa /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sb.cs_next_var /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  compile_alloc_buffer capacity sb = (buf,cs) /\ fn_has_code sb cs fn /\
  capacity < dimword (:256) /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  fresh_vars_wrt sb s /\ eval_operand src s = SOME p /\ op_taint tn src = {} ==>
  ?out u G1 tn1.
    buf.buf_operand = Var out /\
    step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w capacity)] [out]) s = OK u /\
    G1 = step_prov PG G (mk_inst sb.cs_next_id ALLOCA [Lit (n2w capacity)] [out]) u /\
    tn1 = step_taint (mk_inst sb.cs_next_id ALLOCA [Lit (n2w capacity)] [out]) s u tn /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK (u with vs_inst_idx := SUC s.vs_inst_idx)) /\
    ptr_covers G1 tn1 out (u with vs_inst_idx := SUC s.vs_inst_idx) capacity /\
    ghost_inv rty ce cx ee G1 tn1 (u with vs_inst_idx := SUC s.vs_inst_idx) /\
    ghost_kept ce es sa G0 tn0 s0 G1 tn1 /\
    fresh_vars_wrt cs (u with vs_inst_idx := SUC s.vs_inst_idx) /\
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
  drule_all ifexp_alloc_start_fresh >> strip_tac >>
  drule_all ifexp_alloc_start_source >>
  disch_then (qspecl_then [`tn`, `PG`, `G`] strip_assume_tac) >>
  drule_all ifexp_alloc_start_cursor >> strip_tac >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  drule_all ifexp_alloc_start_destination_external >> strip_tac >>
  qexistsl_tac [`out`, `u`, `G1`, `tn1`] >> gvs[]
QED

Theorem ifexp_copy_allocation_loop_bounds:
  stmt_state_rel ctx fn ce cx es s0 /\
  vv_post ctx fn ce cx e es sa sb s0 ee raw vv s /\
  local_ptrs_reserved ce sa /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  fn_inst_ids_distinct fn /\ sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  compile_alloc_buffer (32*n) sb = (buf,cs) /\ fn_has_code sb cs fn /\
  32*n < dimword (:256) /\ buf.buf_operand = Var out /\
  step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w (32*n))] [out]) s = OK u ==>
  ?d. eval_operand (Var out) (u with vs_inst_idx := SUC s.vs_inst_idx) = SOME d /\
    n < 2**256 /\ w2n d+32*n < 2**256 /\
    (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id ==>
      off+sz <= w2n d \/ w2n d+32*n <= off) /\
    (!name pos len. local_region ce es.scopes s0 name pos len ==>
      pos+len <= w2n d \/ w2n d+32*n <= pos) /\
    (!name entry v sz w. lookup_scopes name ee.scopes = SOME entry /\
      FLOOKUP ce.ce_vars name = SOME (PtrVar (Var v) sz) /\
      lookup_var v (u with vs_inst_idx := SUC s.vs_inst_idx) = SOME w ==>
      val_wf entry.type entry.value /\
      (w2n w+type_memory_size entry.type <= w2n d \/ w2n d+32*n <= w2n w))
Proof
  strip_tac >>
  drule_all (SRULE [] (Q.INST
    [`b` |-> `buffer_allocation_base sArm sb.cs_next_id`] ifexp_copy_allocation_bounds)) >>
  strip_tac >>
  drule_at (Pat `step_inst_base _ _ = _`) ifexp_copy_allocation_local_lookups >>
  disch_then (qspecl_then [`sa`, `cs`, `ce`, `buf`] mp_tac) >> simp[] >> strip_tac >>
  drule_all ifexp_alloca_step_base >> strip_tac >>
  qexists_tac `n2w (buffer_allocation_base s sb.cs_next_id)` >>
  `buffer_allocation_base s sb.cs_next_id < dimword (:256)` by decide_tac >>
  simp[eval_operand_def, lookup_var_def, w2n_n2w, LESS_MOD] >>
  conj_tac >- (fs[dimword_def] >> decide_tac) >>
  conj_tac >- fs[dimword_def] >>
  conj_tac
  >- (rpt strip_tac >> qpat_x_assum `!aid off sz. _` drule_all >> decide_tac) >>
  conj_tac
  >- (rpt strip_tac >> qpat_x_assum `!name p sz. _` drule_all >> decide_tac) >>
  rpt strip_tac >>
  `lookup_var v u = SOME w` by simp[lookup_var_def] >>
  `lookup_var v s = SOME w` by metis_tac[] >>
  qpat_x_assum `!name entry p sz w. _` drule_all >>
  strip_tac >> simp[] >> decide_tac
QED
