Theory bodyPtrBytestringBuiltinsUintReady
Ancestors
  bodyPtrBytestringBuiltinsUintAlloc bodyPtrBytestringBuiltinsBuffer
  exprSimUint2Str exprLoweringProps loweringHalt loweringPosts exprSimPtrLiteralBuffer
  ptrDiscipline venomState venomExecSemantics venomInst finite_map
  compileEnv contextCodegenRel codegenRel words list arithmetic

Theorem u2s_alloc_concrete_ptr:
  compile_alloc_buffer sz sa = (ba,a) /\
  u2s_layout a op ba.buf_operand n sb /\ fn_has_code sa sb fn /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ sz < dimword(:256) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ghost_inv d cenv cx es G tn s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?p b sr inst G1 tn1.
    ba.buf_operand = Var p /\
    inst = mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p] /\
    step_inst_base inst s = OK sr /\
    G1 = step_prov PG G inst sr /\ tn1 = step_taint inst s sr tn /\
    gas_path_ptr_edge D 0 ctx fn PG G tn s 0 G1 tn1
      (OK (sr with vs_inst_idx := SUC s.vs_inst_idx)) /\
    u2s_safe ctx fn cenv cx es a (Var p) b sz inst sr sr /\
    ghost_inv d cenv cx es G1 tn1 sr /\ ghost_kept cenv es sa G tn s G1 tn1 /\
    FLOOKUP G1 p = SOME (b,sz) /\ lookup_var p sr = SOME (n2w b) /\
    op_taint tn1 (Var p) = {} /\ b+sz < dimword(:256) /\
    wb_frame cenv es sa s sr /\
    (!x. not_fresh_at sa x ==> lookup_var x sr = lookup_var x s) /\
    (!aid off len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (off,len) ==>
      off+len <= b \/ b+sz <= off) /\
    (!name off len. local_region cenv es.scopes sr name off len ==>
      b+sz <= off \/ off+len <= b) /\
    FLOOKUP sr.vs_allocas sa.cs_next_id = SOME (b,sz)
Proof
  strip_tac >> drule_all u2s_alloc_layout_code >> strip_tac >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
    [STRING #"%" (toString sa.cs_next_var)]` >>
  `inst = mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
    [STRING #"%" (toString sa.cs_next_var)]` by simp[Abbr `inst`] >>
  `MEM inst (fn_insts fn)` by simp[Abbr `inst`] >>
  drule_all u2s_alloc_safe >> strip_tac >>
  `p = STRING #"%" (toString sa.cs_next_var)` by
    (qpat_x_assum `ba.buf_operand = Var p` mp_tac >> simp[]) >>
  qpat_x_assum `p = _` SUBST_ALL_TAC >>
  `step_inst_base inst s = OK t` by
    (simp[Abbr `inst`] >> irule u2s_alloc_step >> goal_assum drule >> simp[]) >>
  qexistsl_tac [`STRING #"%" (toString sa.cs_next_var)`, `w2n w`, `t`, `inst`,
    `step_prov PG G inst t`, `step_taint inst s t tn`] >>
  pure_asm_rewrite_tac [] >> simp[NoAsms] >>
  conj_tac >- suspend "edge" >>
  conj_tac >- suspend "ghost" >>
  suspend "site"
QED

Resume u2s_alloc_concrete_ptr[edge]:
  qpat_x_assum `inst = _` SUBST_ALL_TAC >>
  drule_all compile_alloc_buffer_counted_edge_covers >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] mp_tac) >> simp[]
QED

Resume u2s_alloc_concrete_ptr[ghost]:
  qpat_x_assum `u2s_safe _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[Abbr `inst`]
QED

Resume u2s_alloc_concrete_ptr[site]:
  `FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,sz)` by
    (qpat_x_assum `u2s_safe _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[u2s_safe_def, Abbr `inst`, mk_inst_def]) >>
  qpat_x_assum `inst = _` SUBST_ALL_TAC >>
  drule_all alloca_step_state_fields >> strip_tac >>
  `!name off len. local_region cenv es.scopes s name off len ==>
    off+len <= w2n w \/ w2n w+sz <= off` by
    (drule_all old_local_region_transport >>
     disch_then (qspec_then `es.scopes` assume_tac) >>
     rpt strip_tac >>
     `local_region cenv es.scopes t name off len` by metis_tac[] >>
     first_x_assum drule >> decide_tac) >>
  drule_all alloca_step_ghost_frame >>
  disch_then (qspec_then `PG` strip_assume_tac) >> simp[] >>
  drule_all literal_ptr_alloca_ghost >>
  disch_then (qspecl_then [`tn`, `PG`, `G`] strip_assume_tac) >>
  gvs[op_taint_def, FLOOKUP_UPDATE]
QED

Finalise u2s_alloc_concrete_ptr

Theorem u2s_alloc_compiler_control:
  compile_alloc_buffer sz sa = (ba,a) ==>
  a.cs_current_bb = sa.cs_current_bb /\
  LENGTH a.cs_current_insts = SUC (LENGTH sa.cs_current_insts) /\
  sa.cs_next_var <= a.cs_next_var
Proof
  simp[contextTheory.compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
    comp_bind_def, comp_ignore_bind_def,
    comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[]
QED

Theorem u2s_alloc_ready_ptr:
  compile_alloc_buffer sz sa = (ba,a) /\
  u2s_layout a op ba.buf_operand n sb /\ fn_has_code sa sb fn /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ sz < dimword(:256) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ghost_inv d cenv cx es G tn s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  eval_operand op s = SOME (n2w X) /\ op_prov G op = NONE /\ op_taint tn op = {} ==>
  ?p b sr ready inst G1 tn1.
    ba.buf_operand = Var p /\
    inst = mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p] /\
    ready = sr with vs_inst_idx := LENGTH a.cs_current_insts /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK ready) /\
    u2s_safe ctx fn cenv cx es a (Var p) b sz inst sr ready /\
    ghost_inv d cenv cx es G1 tn1 ready /\ ghost_kept cenv es sa G tn s G1 tn1 /\
    FLOOKUP G1 p = SOME (b,sz) /\ lookup_var p ready = SOME (n2w b) /\
    op_taint tn1 (Var p) = {} /\ b+sz < dimword(:256) /\
    ready.vs_current_bb = a.cs_current_bb /\
    ready.vs_inst_idx = LENGTH a.cs_current_insts /\ ~ready.vs_halted /\
    eval_operand op ready = SOME (n2w X) /\ op_prov G1 op = NONE /\ op_taint tn1 op = {} /\
    (!k. op <> Var (u2s_var a k)) /\ not_fresh_at a p /\ local_ptrs_reserved cenv a /\
    (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
    (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
    inst.inst_outputs = [p] /\ not_local_ptr cenv es.scopes p /\
    MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
    (!bb. MEM bb (u2s_blocks a op (Var p) n) ==>
      lookup_block bb.bb_label fn.fn_blocks = SOME bb) /\
    lookup_block a.cs_current_bb fn.fn_blocks = SOME
      <|bb_label := a.cs_current_bb;
        bb_instructions := a.cs_current_insts ++ u2s_setup a op (Var p)|> /\
    (!out. u2s_safe ctx fn cenv cx es a (Var p) b sz inst sr out ==>
      stmt_state_rel ctx fn cenv cx es out /\ wb_frame cenv es sa s out /\
      FLOOKUP out.vs_allocas sa.cs_next_id = SOME (b,sz))
Proof
  strip_tac >> drule_all u2s_alloc_concrete_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  drule u2s_alloc_compiler_control >> strip_tac >>
  drule_all u2s_alloc_layout_code >> strip_tac >>
  qabbrev_tac `ready = sr with vs_inst_idx := LENGTH a.cs_current_insts` >>
  qexistsl_tac [`p`, `b`, `sr`, `ready`, `inst`, `G1`, `tn1`] >>
  suspend "ready"
QED

Resume u2s_alloc_ready_ptr[ready]:
  `p = STRING #"%" (toString sa.cs_next_var)` by
    (qpat_x_assum `ba.buf_operand = Var p` mp_tac >> simp[]) >>
  `~not_fresh_at sa p /\ not_fresh_at a p` by metis_tac[] >>
  `local_ptrs_reserved cenv a` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `!k. op <> Var (u2s_var a k)` by
    (rpt strip_tac >> `not_fresh_at a (u2s_var a k)` by metis_tac[] >>
     metis_tac[u2s_var_fresh]) >>
  `!x. op = Var x ==> x <> p` by metis_tac[] >>
  `eval_operand op sr = SOME (n2w X)` by
    (qpat_x_assum `inst = _` SUBST_ALL_TAC >>
     drule_all allocationPtrTheory.alloca_step_operand_preserved >> simp[]) >>
  `op_prov G1 op = NONE /\ op_taint tn1 op = {}` by
    (qpat_x_assum `inst = _` SUBST_ALL_TAC >>
     metis_tac[alloca_step_old_operand_ghost]) >>
  `sr.vs_current_bb = s.vs_current_bb /\ sr.vs_halted = s.vs_halted` by
    (qpat_x_assum `inst = _` SUBST_ALL_TAC >>
     drule_all alloca_step_state_fields >> simp[]) >>
  `not_local_ptr cenv es.scopes p` by
    metis_tac[exprSimOperandsTheory.fresh_not_local_ptr] >>
  `ghost_inv d cenv cx es G1 tn1 ready` by
    (simp[Abbr `ready`, SRULE [] (Q.INST [`gs` |-> `es.gas_obs`]
       literal_ptr_ghost_inv_normalize)]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK ready)` by
    (simp[Abbr `ready`] >>
     `~(sr with vs_inst_idx := SUC s.vs_inst_idx).vs_halted` by simp[] >>
     metis_tac[fragGasPathPtrTheory.gas_path_ptr_rules, ADD_CLAUSES]) >>
  simp[Abbr `ready`, u2s_safe_index, IgnAsm `G1 = _`, IgnAsm `tn1 = _`,
       IgnAsm `inst = _`, IgnAsm `p = _`] >>
  conj_tac >- suspend "blocks" >>
  conj_tac >- suspend "lookup" >> suspend "tail"
QED

Resume u2s_alloc_ready_ptr[blocks]:
  qpat_x_assum `p = _` SUBST_ALL_TAC >> gvs[] >>
  first_assum ACCEPT_TAC
QED

Resume u2s_alloc_ready_ptr[lookup]:
  qpat_x_assum `p = _` SUBST_ALL_TAC >> gvs[]
QED

Resume u2s_alloc_ready_ptr[tail]:
  qpat_x_assum `p = _` SUBST_ALL_TAC >> gvs[lookup_var_def, mk_inst_def] >>
  gen_tac >> disch_tac >> irule u2s_safe_wb_tail >>
  simp[] >> (conj_tac >- first_assum ACCEPT_TAC) >>
  goal_assum (drule_at Any) >> simp[] >>
  rpt strip_tac >> first_x_assum drule >> decide_tac
QED

Finalise u2s_alloc_ready_ptr
