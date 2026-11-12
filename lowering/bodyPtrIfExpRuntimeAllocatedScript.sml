Theory bodyPtrIfExpRuntimeAllocated
Ancestors bodyPtrIfExpStorageAllocation bodyPtrIfExpRuntimeCopy
  bodyPtrIfExpAllocSource loweringHalt exprLoweringProps ptrDiscipline
  compileEnv loweringStateRelDefs venomState venomInst finite_map words arithmetic fragGasPathPtr
  slotCopyExecution exprSimCopy loweringPosts bodyPtrIfExpRuntimeFrame

Theorem ifexp_runtime_allocated_execution:
  stmt_state_rel ctx fn ce cx es s0 /\
  vv_post ctx fn ce cx e es sa sb s0 ee raw vv s /\
  ghost_inv rty ce cx ee G tn s /\ ghost_kept ce es sa G0 tn0 s0 G tn /\
  local_ptrs_reserved ce sa /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  fn_inst_ids_distinct fn /\ sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  compile_alloc_buffer (32*n) sb = (buf,cs) /\ fn_has_code sb cs fn /\
  compile_imm_copy_to_memory F imm src buf.buf_operand n 0 cs = ((),sd) /\
  fn_has_code cs sd fn /\ 32*n < dimword (:256) /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  fresh_vars_wrt sb s /\ eval_operand src s = SOME a /\ op_taint tn src = {} ==>
  ?out d q J tr t H tt.
    buf.buf_operand = Var out /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tt (OK t) /\
    stmt_state_rel ctx fn ce cx ee q /\
    t.vs_memory = (immutable_transfers F F a d n 0 q).vs_memory /\
    t.vs_current_bb = sd.cs_current_bb /\
    t.vs_inst_idx = LENGTH sd.cs_current_insts /\ ~t.vs_halted /\
    ptr_covers H tt out t (32*n) /\ lookup_var out t = SOME d /\
    w2n d+32*n < dimword (:256) /\
    tt.t_mem = tr.t_mem DIFF {i | w2n d <= i /\ i < w2n d+32*n} /\
    ghost_inv rty ce cx ee H tt t /\ ghost_kept ce es sa G0 tn0 s0 H tt /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 J tr (OK q) /\
    copy_runtime_frame cs q sd (t with vs_inst_idx := q.vs_inst_idx) /\
    (?u. step_inst_base (mk_inst sb.cs_next_id ALLOCA
          [Lit (n2w (32*n))] [out]) s = OK u /\
         q = u with vs_inst_idx := SUC s.vs_inst_idx) /\
    (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id ==>
      off+sz <= w2n d \/ w2n d+32*n <= off) /\
    (!name pos len. local_region ce es.scopes s0 name pos len ==>
      pos+len <= w2n d \/ w2n d+32*n <= pos) /\
    (!x. not_fresh_at sb x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!b len. b+len <= w2n d \/ w2n d+32*n <= b ==>
      mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory) /\
    t.vs_accounts = s.vs_accounts /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_transient = s.vs_transient
Proof
  strip_tac >> drule_all ifexp_copy_allocation_start >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  drule_all ifexp_copy_allocation_loop_bounds >> strip_tac >>
  drule_all alloca_step_contracts >> strip_tac >>
  `sa.cs_next_var <= cs.cs_next_var /\ sb.cs_next_var <= cs.cs_next_var` by
    (drule compile_alloc_buffer_parts >> strip_tac >> decide_tac) >>
  `local_ptrs_reserved ce sb /\ local_ptrs_reserved ce cs` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `stmt_state_rel ctx fn ce cx ee s` by fs[vv_post_def] >>
  drule_all compile_alloc_buffer_raw_resources >> strip_tac >>
  `stmt_state_rel ctx fn ce cx ee (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[stmt_state_rel_inst_idx] >>
  suspend "copy"
QED

Resume ifexp_runtime_allocated_execution[copy]:
  `!x. not_fresh_at sa x ==> not_fresh_at cs x` by
    (simp[not_fresh_at_def] >> rpt strip_tac >>
     first_x_assum drule >> decide_tac) >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cs x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cs x)` by
    metis_tac[] >>
  `copy_old_operand cs src /\ copy_old_operand cs (Var out)` by
    (simp[copy_old_operand_def] >>
     metis_tac[exprSimWordBuiltinsTheory.fresh_vars_wrt_not_fresh_at]) >>
  `compile_imm_copy_to_memory F imm src (Var out) n 0 cs = ((),sd)` by metis_tac[] >>
  `lookup_var out (u with vs_inst_idx := SUC s.vs_inst_idx) = SOME d` by
    fs[eval_operand_def] >>
  `w2n d+32*n < dimword (:256)` by fs[dimword_def] >>
  `~(u with vs_inst_idx := SUC s.vs_inst_idx).vs_halted` by simp[] >>
  `0+32*n <= 32*n` by simp[] >>
  drule_all ifexp_runtime_copy_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  suspend "finish"
QED

Resume ifexp_runtime_allocated_execution[finish]:
  drule_all ifexp_runtime_allocation_frame >> strip_tac >>
  qexistsl_tac [`out`, `d`, `u with vs_inst_idx := SUC s.vs_inst_idx`,
    `G1`, `tn1`, `t`, `H`, `tt`] >>
  simp[] >> conj_tac >- (drule_all gas_path_ptr_then >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!aid off sz. _` drule_all >> decide_tac) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!name pos len. local_region _ _ _ _ _ _ ==> _` drule_all >>
      decide_tac) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!b len. _ ==> mem_bytes_at _ _ t.vs_memory = _`
    (qspecl_then [`b`, `len`] mp_tac) >> simp[]
QED

Finalise ifexp_runtime_allocated_execution
