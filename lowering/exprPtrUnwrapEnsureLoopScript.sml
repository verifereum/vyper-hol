(* Execute the allocation and actual non-singleton ensure-memory loop together. *)
Theory exprPtrUnwrapEnsureLoop
Ancestors
  exprPtrUnwrapLoopEntry exprPtrUnwrapCompiledLoop exprPtrUnwrapEnsureShape
  exprPtrUnwrapRuntimeFrame exprPtrUnwrapLoopInvariant slotCopyExecution
  exprPtrUnwrapAllocSeparation
  createMemoryInterface bodyPtrDefs compileEnv context fragGasPathPtr
  venomState venomInst words arithmetic createSourceCallback ptrSafeRun ptrDiscipline

Theorem unwrap_ensure_slot_loop:
  (loc = LocStorage \/ loc = LocTransient) /\ n <> 1 /\
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
  ?root d a G0 tn0 Gf tnf t sm buf u.
    fn_has_code sa sm func /\ fn_has_code sm sb func /\
    u = update_var root d (buffer_allocation_fields s sa.cs_next_id nb) /\
    step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
    a = u with vs_inst_idx := SUC s.vs_inst_idx /\
    G0 = step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) u /\
    tn0 = step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s u tn /\
    op = Var root /\ (d:bytes32) = n2w (buffer_allocation_base s sa.cs_next_id) /\
    compile_alloc_buffer nb sa = (buf,sm) /\ buf.buf_operand = Var root /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G0 tn0 (OK a) /\
    gas_path_ptr D 0 ctx func PG G0 tn0 a 0 Gf tnf (OK t) /\
    lookup_var root a = SOME d /\
    tnf.t_imm = tn.t_imm /\
    (!x k. slot_copy_external sm (Var x) ==>
      (ptr_covers Gf tnf x t k <=> ptr_covers G0 tn0 x a k)) /\
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK t) /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ptr_covers Gf tnf root t nb /\
    slot_copy_inv sm (if loc=LocStorage then SLOAD else TLOAD) a p d n regions n t /\
    slot_copy_ghost_inv sm (if loc=LocStorage then SLOAD else TLOAD)
      p d root n G0 tn0 n Gf tnf t /\
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
  drule_all ensure_slot_memory_loop_code >> strip_tac >>
  drule_all unwrap_alloc_site_bound >> strip_tac >>
  `buffer_allocation_base s sa.cs_next_id < dimword (:256)` by decide_tac >>
  drule_all unwrap_alloc_loop_entry >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  `compile_slot_to_memory src (Var root) n loc sm = (lab,sb)` by metis_tac[] >>
  `create_memory_snapshot regions a` by metis_tac[create_memory_snapshot_def] >>
  `EVERY (\(off,bs). off+LENGTH bs <= LENGTH a.vs_memory /\
    (off+LENGTH bs <= w2n d \/ w2n d+32*n <= off)) regions` by
    (qpat_x_assum `EVERY _ regions` mp_tac >> simp[]) >>
  `allocas_from 0 a /\ (ctx_has_dalloca ctx ==> allocas_below_fmp a)` by
    simp[allocas_from_def] >>
  drule_all unwrap_compiled_slot_loop >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK t)` by
    metis_tac[gas_path_ptr_then, ADD_0] >>
  qexistsl [`root`, `d`, `a`, `G0`, `tn0`, `Gf`, `tnf`, `t`, `sm`, `buf`, `u`] >>
  `!key. slot_copy_word (if loc=LocStorage then SLOAD else TLOAD) a key =
    slot_copy_word (if loc=LocStorage then SLOAD else TLOAD) s key` by
    simp[slot_copy_word_def, sload_def, tload_def, contract_storage_def,
      contract_transient_def] >>
  asm_rewrite_tac[] >> metis_tac[]
QED
