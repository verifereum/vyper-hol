Theory bodyPtrIntCallAllocRun
Ancestors
  bodyPtrHashBuiltinsAllocFrame bodyPtrStructLitAllocationBridge
  bodyPtrIntCallStagingFrame assignBasePtrAllocSeparate
  ghostPcTransportPtr bodyPtrDefs exprSimProps exprSimAlloc
  venomState loweringPosts

(* Allocation leaves memory untouched even when the instruction's site is reused.
   Its whole site, not its address relative to the old frontier, is separated. *)
Theorem intcall_alloc_buffer_run:
  compile_alloc_buffer n sa = (buf,sb) /\ fn_has_code sa sb fn /\
  stmt_state_rel ctx fn ce cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved ce sa /\ n < dimword (:256) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ghost_inv d ce cx es G tn s /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) ==>
  ?t w p H un.
    gas_path_ptr_edge D 0 ctx fn PG G tn s 0 H un (OK t) /\
    stmt_state_rel ctx fn ce cx es t /\ ghost_inv d ce cx es H un t /\
    ghost_kept ce es sa G tn s H un /\ pure_frame ce fn es sa s t /\
    buf.buf_operand = Var p /\ eval_operand buf.buf_operand t = SOME w /\
    ptr_covers H un p t n /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,n) /\
    w2n w+n < dimword (:256) /\ sa.cs_next_id < sb.cs_next_id /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_memory = s.vs_memory /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid site. FLOOKUP s.vs_allocas aid = SOME site ==>
      FLOOKUP t.vs_allocas aid = SOME site) /\
    intcall_site_outside (intcall_protected ce es sa s) (w2n w,n)
Proof
  strip_tac >> drule_all buffer_alloc_code >> strip_tac >>
  drule_all hash_literal_alloc_buffer_frame >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  drule_all structlit_alloc_buffer_ptr_entry >> strip_tac >>
  gvs[] >>
  first_x_assum (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl [`t with vs_inst_idx := SUC (LENGTH sa.cs_current_insts)`, `w`] >>
  goal_assum (drule_at Any) >>
  simp[lookup_var_def] >>
  conj_tac >- metis_tac[lookup_var_def] >>
  irule intcall_separated_site_outside >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!name b k. _` irule >>
      qexists `name` >> irule local_region_frame_fwd >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED
