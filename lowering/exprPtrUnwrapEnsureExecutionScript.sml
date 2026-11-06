(* Common ordinary endpoint: no loop-counter invariant in the public post. *)
Theory exprPtrUnwrapEnsureExecution
Ancestors
  exprPtrUnwrapEnsureSingle exprPtrUnwrapEnsureLoop exprPtrUnwrapRuntimeFrame
  exprPtrUnwrapLoopEntry createMemoryInterface slotCopyExecution
  bodyPtrDefs compileEnv context venomState venomInst words arithmetic

Theorem unwrap_ensure_slot_execution:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_ensure_in_memory src loc nb n ctor imm sa = (op,sb) /\
  fn_has_code sa sb func /\ stmt_state_rel ctx func cenv cx es s /\
  nb < dimword (:256) /\ 32*n <= nb /\ n < 2**256 /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME p /\ op_taint tn src = {} /\
  create_memory_snapshot regions s /\
  EVERY (\(off,bs). off+LENGTH bs <= LENGTH s.vs_memory /\
    (off+LENGTH bs <= buffer_allocation_base s sa.cs_next_id \/
      buffer_allocation_base s sa.cs_next_id+32*n <= off)) regions ==>
  ?root d a G0 tn0 Gf tnf t sm buf.
    op = Var root /\ (d:bytes32) = n2w (buffer_allocation_base s sa.cs_next_id) /\
    compile_alloc_buffer nb sa = (buf,sm) /\ buf.buf_operand = Var root /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G0 tn0 (OK a) /\
    gas_path_ptr D 0 ctx func PG G0 tn0 a 0 Gf tnf (OK t) /\
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK t) /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ptr_covers Gf tnf root t nb /\ lookup_var root a = SOME d /\
    tnf.t_imm = tn.t_imm /\
    (!x k. slot_copy_external sm (Var x) ==>
      (ptr_covers Gf tnf x t k <=> ptr_covers G0 tn0 x a k)) /\
    slot_copy_runtime_frame sm d n a t /\
    a.vs_memory = s.vs_memory /\ a.vs_accounts = s.vs_accounts /\
    a.vs_transient = s.vs_transient /\ a.vs_call_ctx = s.vs_call_ctx /\
    a.vs_immutables = s.vs_immutables /\
    tn0.t_stor = tn.t_stor /\ tn0.t_trans = tn.t_trans /\ tn0.t_imm = tn.t_imm /\
    (!j. j < n ==> mem_word_at (w2n d+32*j) t.vs_memory =
      slot_copy_word (if loc=LocStorage then SLOAD else TLOAD) s (p+n2w j)) /\
    (!j b. j < n /\ b < 32 /\ w2n d+32*j+b IN tnf.t_mem ==>
      b IN key_taint (if loc=LocStorage then tn.t_stor else tn.t_trans) (p+n2w j)) /\
    copy_static t = copy_static a /\ LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    (!x k. x+k <= w2n d \/ w2n d+32*n <= x ==>
      mem_bytes_at x k t.vs_memory = mem_bytes_at x k s.vs_memory)
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  Cases_on `n=1`
  >- (qpat_x_assum `n=1` SUBST_ALL_TAC >>
      `32 <= nb` by fs[] >> drule_all unwrap_ensure_slot_single >>
      disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
      qexistsl [`root`, `d`, `a`, `G0`, `tn0`, `Gf`, `tnf`, `t`, `sm`, `buf`] >>
      qpat_x_assum `t = _` kall_tac >>
      gvs[slot_copy_runtime_frame_def, WORD_ADD_0] >> metis_tac[ADD_COMM]) >>
  drule_all unwrap_ensure_slot_loop >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  qexistsl [`root`, `d`, `a`, `G0`, `tn0`, `Gf`, `tnf`, `t`, `sm`, `buf`] >>
  asm_rewrite_tac[]
QED
