Theory bodyPtrPopNestedLiveRun
Ancestors
  bodyPtrPopNestedLiveHandoff bodyPtrPopLengthGuard
  assignTuplePtrLoadStep fragGasPathPtr bodyPtrDefs emitHelperProps
  emitHelper compileEnv stmtFragPtr ptrDiscipline venomState venomInst finite_map

Theorem pop_memory_header_guard_path:
  emit_op MLOAD [Var src] sa = (len,sm) /\
  emit_op ISZERO [len] sm = (nz,sb) /\
  emit_op ISZERO [nz] sb = (valid,sc) /\
  emit_void ASSERT [valid] sc = ((),sd) /\
  emit_op SUB [len; Lit 1w] sd = (new_len,se) /\
  fn_has_code sa sm fn /\ fn_has_code sm se fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME a /\
  (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) /\
  mload (w2n a) s <> 0w ==>
  ?t H tf. gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK t) /\
    eval_operand new_len t = SOME (mload (w2n a) s - 1w) /\
    op_taint tf new_len = {} /\ op_prov H new_len = NONE /\
    ~t.vs_halted /\ t.vs_current_bb = se.cs_current_bb /\
    t.vs_inst_idx = LENGTH se.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!v. not_fresh_at sa v ==> lookup_var v t = lookup_var v s /\
      FLOOKUP H v = FLOOKUP G v /\ op_taint tf (Var v) = op_taint tn (Var v))
Proof
  strip_tac >> drule_all emit_mload_member_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `sa.cs_next_var <= sm.cs_next_var` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
        fresh_id_def, emit_def, comp_return_def] >>
  `eval_operand (Var out) t = SOME (mload (w2n a) s)` by simp[eval_operand_def] >>
  `t.vs_current_bb = sm.cs_current_bb` by simp[] >>
  qpat_x_assum `len = Var out` SUBST_ALL_TAC >>
  qpat_assum `emit_op ISZERO [Var out] sm = (nz,sb)`
    (mp_then Any mp_tac pop_length_guard_path) >>
  simp[] >> disch_then drule_all >>
  simp[] >> disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG G' tn' t 0 H tf (OK u)` >>
  qexistsl_tac [`u`, `H`, `tf`] >> simp[] >> conj_tac
  >- (drule_all gas_path_ptr_then >> simp[]) >>
  rpt strip_tac >>
  `not_fresh_at sm v` by metis_tac[not_fresh_at_mono] >>
  metis_tac[]
QED

Theorem pop_memory_header_empty_path:
  emit_op MLOAD [Var src] sa = (len,sm) /\
  emit_op ISZERO [len] sm = (nz,sb) /\
  emit_op ISZERO [nz] sb = (valid,sc) /\
  emit_void ASSERT [valid] sc = ((),sd) /\
  emit_op SUB [len; Lit 1w] sd = (new_len,se) /\
  fn_has_code sa sm fn /\ fn_has_code sm se fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME a /\
  (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) /\
  mload (w2n a) s = 0w ==>
  ?t H tf. gas_path_ptr D 0 ctx fn PG G tn s 0 H tf
    (Abort Revert_abort (revert_state (set_returndata [] t))) /\
    t.vs_current_bb = sc.cs_current_bb /\
    t.vs_inst_idx = LENGTH sc.cs_current_insts
Proof
  strip_tac >> drule_all emit_mload_member_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qpat_x_assum `len = Var out` SUBST_ALL_TAC >>
  `eval_operand (Var out) t = SOME 0w` by simp[eval_operand_def] >>
  qpat_assum `emit_op ISZERO [Var out] sm = (nz,sb)`
    (mp_then Any mp_tac pop_length_guard_empty_path) >>
  simp[] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `G'`, `D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG G' tn' t 0 H tf (Abort _ _)` >>
  goal_assum (drule_at Any) >> simp[] >>
  drule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  qexistsl_tac [`H`, `tf`] >> simp[]
QED
