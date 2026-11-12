(* Actual registered cursor allocation, followed by its literal initialization. *)
Theory logCursorAllocPtr
Ancestors
  logDataAllocPtr logCursorInitPtr logInstSeqPtr abiBuiltinAllocation bodyPtrDefs
  abiBuiltinPrefix emitHelperProps emitHelper exprLoweringProps compileEnv
  context venomMemProps fragGasSeqPtr fragExec venomState venomInst
  venomExecSemantics ptrDiscipline words list arithmetic finite_map instIdxIndep

Theorem log_cursor_allocate_init_seq_ptr:
  compile_alloc_buffer 32 sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand;Lit w] sm = ((),sb) /\
  fn_has_code sa sm func /\ stmt_state_rel ctx func ce cx es s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  sm.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  ~ctx_has_dalloca ctx ==>
  ?u t p Gf tk tm out.
    run_inst_seq (emitted_insts sa sm ++ emitted_insts sm sb) s = OK t /\
    inst_seq_ptr D 0 ctx func PG G tn
      (emitted_insts sa sm ++ emitted_insts sm sb) s Gf tm /\
    buf.buf_operand = Var out /\ buf.buf_size = 32 /\
    lookup_var out t = SOME (n2w p) /\ ptr_covers Gf tm out t 32 /\
    p+32 < dimword(:256) /\ FLOOKUP t.vs_allocas sa.cs_next_id = SOME (p,32) /\
    mload p t = w /\
    mem_agree_outside {i | p <= i /\ i < p+32} t.vs_memory s.vs_memory /\
    (!i. p <= i /\ i < p+32 ==> i NOTIN tm.t_mem) /\
    (!i. ~(p <= i /\ i < p+32) ==> (i IN tm.t_mem <=> i IN tk.t_mem)) /\
    tm.t_var = tk.t_var /\ tm.t_stor = tk.t_stor /\
    tm.t_trans = tk.t_trans /\ tm.t_imm = tk.t_imm /\
    (!op. abi_decoder_operand_live sa.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    (!id b sz. id <> sa.cs_next_id /\ FLOOKUP t.vs_allocas id = SOME (b,sz) ==>
      p+32 <= b \/ b+sz <= p) /\
    abi_builtin_allocation_frame sa.cs_next_var sa.cs_next_id 32 s u /\
    t.vs_allocas = u.vs_allocas /\
    ptr_covers Gf tk out u 32 /\ u.vs_memory = s.vs_memory /\
    inst_extends sa sm /\ inst_extends sm sb
Proof
  strip_tac >> `32 < dimword(:256)` by simp[dimword_def] >>
  drule_all log_buffer_seq_ptr >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`D`]
    (qx_choose_then `u` (qx_choose_then `p` (qx_choose_then `Gf`
    (qx_choose_then `tk` (qx_choose_then `out` strip_assume_tac)))))) >>
  qpat_x_assum `buf.buf_operand = _` SUBST_ALL_TAC >>
  qabbrev_tac `u1 = u with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sm)` >>
  `ptr_covers Gf tk out u1 32 /\ lookup_var out u1 = SOME (n2w p)` by
    gvs[Abbr `u1`, ptr_covers_def, eval_operand_def, lookup_var_def] >>
  drule_all emit_literal_cursor_init_seq_ptr >>
  disch_then (qspecl_then [`func`,`PG`,`D`]
    (qx_choose_then `tm` (qx_choose_then `v` strip_assume_tac))) >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sm) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb)` by
    simp[mk_inst_def, is_terminator_def] >>
  `run_inst_seq (emitted_insts sa sm ++ emitted_insts sm sb) s =
     OK (v with vs_inst_idx := u.vs_inst_idx) /\
   inst_seq_ptr D 0 ctx func PG G tn
     (emitted_insts sa sm ++ emitted_insts sm sb) s Gf tm` by
    (irule successful_seq_ptr_append >> qunabbrev_tac `u1` >>
     asm_simp_tac bool_ss [] >> qexistsl_tac [`Gf`,`tk`] >> gvs[]) >>
  `mload p v = w` by simp[w2n_n2w, mload_mstore_same] >>
  `inst_extends sm sb` by
    (qpat_x_assum `emit_void _ _ sm = _` mp_tac >>
     simp[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, emit_def, inst_extends_def]) >>
  `(!op. eval_operand op v = eval_operand op u) /\ v.vs_allocas = u.vs_allocas` by
    (conj_tac >- simp[Abbr `u1`, eval_operand_mstore, eval_op_inst_idx] >>
     simp[Abbr `u1`, mstore_def]) >>
  `lookup_var out v = lookup_var out u` by
    (qpat_x_assum `!op. eval_operand op v = _` (qspec_then `Var out` mp_tac) >>
     fs[eval_operand_def]) >>
  `!q k. mload q (v with vs_inst_idx := k) = mload q v` by simp[mload_def] >>
  qpat_x_assum `v = mstore _ _ _` kall_tac >>
  qexistsl_tac [`u`,`v with vs_inst_idx := u.vs_inst_idx`,`p`,`Gf`,`tk`,`tm`,`out`] >>
  conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
  gvs[Abbr `u1`, ptr_covers_def, eval_operand_def, lookup_var_def,
      op_taint_def, w2n_n2w, eval_op_inst_idx] >> metis_tac[]
QED

(* Separation comes from the actual registered sites, not fresh variable names.
   The two old sites need not be distinct from each other. *)
Theorem log_cursor_registered_buffers_separate:
  abi_builtin_allocation_frame next site 32 s u /\ t.vs_allocas = u.vs_allocas /\
  (!id b sz. id <> site /\ FLOOKUP t.vs_allocas id = SOME (b,sz) ==>
    p+32 <= b \/ b+sz <= p) /\
  srcid <> site /\ dstid <> site /\
  FLOOKUP s.vs_allocas srcid = SOME (src,scap) /\
  FLOOKUP s.vs_allocas dstid = SOME (dst,dcap) ==>
  FLOOKUP t.vs_allocas srcid = SOME (src,scap) /\
  FLOOKUP t.vs_allocas dstid = SOME (dst,dcap) /\
  (p+32 <= src \/ src+scap <= p) /\ (p+32 <= dst \/ dst+dcap <= p)
Proof
  strip_tac >>
  `FLOOKUP t.vs_allocas srcid = SOME (src,scap) /\
   FLOOKUP t.vs_allocas dstid = SOME (dst,dcap)` by
    metis_tac[abi_builtin_allocation_frame_outside] >>
  metis_tac[]
QED
