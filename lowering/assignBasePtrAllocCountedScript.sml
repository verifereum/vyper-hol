(* All allocation posts refer to the same operational endpoint. *)
Theory assignBasePtrAllocCounted
Ancestors assignBasePtrAllocSource assignBasePtrLiteralSource
  assignBasePtrLiteralGhost fragGasSeqPtr exprSimAlloc exprLowering
  emitHelper emitHelperProps context compileEnv bodyPtrDefs allocationPtr exprLoweringProps
  ghostPcTransportPtr decoderGhostFramePtr instIdxIndep fragExec
  assignBasePtrLiteralOutcome rich_list
  venomInst venomExecSemantics venomState ptrDiscipline list words fragExecPtr

Theorem assign_base_ptr_alloc_buffer_sequence_full:
  !ctx func d cenv cx es sa sm buf sz s PG G tn D frame_sa
    ty va vb v op tv w.
    compile_alloc_buffer sz sa = (buf,sm) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ sz < dimword (:256) /\
    ~ctx_has_dalloca ctx /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) /\
    ghost_inv d cenv cx es G tn s /\
    not_local_ptr cenv es.scopes (STRING #"%" (toString sa.cs_next_var)) /\
    (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==>
      x <> STRING #"%" (toString sa.cs_next_var)) /\
    (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==>
      x <> STRING #"%" (toString sa.cs_next_var)) /\
    (!x. not_fresh_at frame_sa x ==>
      x <> STRING #"%" (toString sa.cs_next_var)) /\
    expr_val_at cenv cx ty va vb es v op s /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
    eval_operand op s = SOME w /\ op <> buf.buf_operand /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory tv v (w2n w) m) ==>
    ?t a G' tn'.
      run_inst_seq (emitted_insts sa sm) s = OK t /\
      inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sm) s G' tn' /\
      stmt_state_rel ctx func cenv cx es t /\
      eval_operand buf.buf_operand t = SOME a /\
      FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n a,sz) /\
      w2n a + sz < dimword (:256) /\
      (?p. buf.buf_operand = Var p /\ ptr_covers G' tn' p t sz) /\
      (!p k. buf.buf_operand <> Var p /\ ptr_covers G tn p s k ==>
        ptr_covers G' tn' p t k) /\
      (!q. q <> buf.buf_operand ==> eval_operand q t = eval_operand q s) /\
      ghost_inv d cenv cx es G' tn' t /\
      ghost_kept cenv es frame_sa G tn s G' tn' /\
      eval_operand op t = SOME w /\
      (!m. mem_agree_outside tn'.t_mem t.vs_memory m ==>
        val_in_memory tv v (w2n w) m)
Proof
  rpt strip_tac >> drule_all assign_base_ptr_alloc_buffer_sequence >>
  disch_then (qspecl_then [`PG`, `G`, `tn`, `D`] strip_assume_tac) >>
  qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
  simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  drule emitted_insts_emit_op >> strip_tac >>
  gvs[run_inst_seq_def, AllCaseEqs(), inst_seq_ptr_def] >>
  conj_tac
  >- (irule assign_base_ptr_alloca_inv >> simp[] >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (irule assign_base_ptr_alloca_kept >> simp[] >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `sz < dimword (:256)` by decide_tac >>
  drule_all assign_base_ptr_alloca_robust_source >> simp[]
QED

Theorem assign_base_ptr_alloc_buffer_counted_full:
  !ctx func d cenv cx es sa sm buf sz s PG G tn D frame_sa
    ty va vb v op tv w.
    compile_alloc_buffer sz sa = (buf,sm) /\ fn_has_code sa sm func /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ sz < dimword (:256) /\
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    ghost_inv d cenv cx es G tn s /\
    not_local_ptr cenv es.scopes (STRING #"%" (toString sa.cs_next_var)) /\
    (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==>
      x <> STRING #"%" (toString sa.cs_next_var)) /\
    (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==>
      x <> STRING #"%" (toString sa.cs_next_var)) /\
    (!x. not_fresh_at frame_sa x ==>
      x <> STRING #"%" (toString sa.cs_next_var)) /\
    expr_val_at cenv cx ty va vb es v op s /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
    eval_operand op s = SOME w /\ op <> buf.buf_operand /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory tv v (w2n w) m) ==>
    ?u a G' tn'.
      gas_path_ptr D 0 ctx func PG G tn s 0 G' tn' (OK u) /\
      stmt_state_rel ctx func cenv cx es u /\
      eval_operand buf.buf_operand u = SOME a /\
      FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n a,sz) /\
      w2n a + sz < dimword (:256) /\
      u.vs_current_bb = sm.cs_current_bb /\
      u.vs_inst_idx = LENGTH sm.cs_current_insts /\
      (?p. buf.buf_operand = Var p /\ ptr_covers G' tn' p u sz) /\
      (!p k. buf.buf_operand <> Var p /\ ptr_covers G tn p s k ==>
        ptr_covers G' tn' p u k) /\
      (!q. q <> buf.buf_operand ==> eval_operand q u = eval_operand q s) /\
      ghost_inv d cenv cx es G' tn' u /\
      ghost_kept cenv es frame_sa G tn s G' tn' /\
      eval_operand op u = SOME w /\
      (!m. mem_agree_outside tn'.t_mem u.vs_memory m ==>
        val_in_memory tv v (w2n w) m)
Proof
  rpt strip_tac >> drule_all buffer_alloc_code >> strip_tac >>
  drule_all assign_base_ptr_alloc_buffer_sequence_full >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
  simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  drule emitted_insts_emit_op >> strip_tac >>
  `cs'.cs_current_bb = sa.cs_current_bb` by
    (gvs[emit_op_def, comp_bind_def, comp_return_def, comp_ignore_bind_def,
         fresh_id_def, fresh_var_def, emit_def]) >>
  `t.vs_current_bb = s.vs_current_bb` by suspend "control" >>
  gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  `isPREFIX (emitted_insts sa cs') (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[DROP_APPEND1] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa cs')` by simp[mk_inst_def, is_terminator_def] >>
  drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`)
    run_inst_seq_gas_path_ptr >>
  disch_then (qspecl_then [`t`, `bb`] mp_tac) >>
  simp[mk_inst_def, stmt_state_rel_inst_idx, DROP_APPEND1, is_terminator_def] >>
  strip_tac >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH sa.cs_current_insts + 1`,
               `a`, `G'`, `tn'`] >>
  simp[stmt_state_rel_inst_idx, assign_base_ptr_ghost_index]
QED

Resume assign_base_ptr_alloc_buffer_counted_full[control]:
  gvs[run_inst_seq_def, AllCaseEqs()] >>
  `step_inst 0 ctx
     (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
       [STRING #"%" (toString sa.cs_next_var)]) s = OK t` by
    simp[step_inst_non_invoke, mk_inst_def] >>
  drule venomInstProofsTheory.step_preserves_control_flow >>
  simp[mk_inst_def, is_terminator_def]
QED

Finalise assign_base_ptr_alloc_buffer_counted_full
