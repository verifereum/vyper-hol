Theory bodyPtrPopNestedLiveSuffix
Ancestors
  bodyPtrPopNestedLiveCompiler bodyPtrPopNestedLiveRun bodyPtrPopNestedLiveAddress
  fragGasPathPtr bodyPtrDefs stmtFragPtr emitHelperProps emitHelper compileEnv
  ptrDiscipline venomState venomInst words finite_map

Theorem pop_memory_suffix_positive_path:
  compile_dynarray_pop (Var src) 32 scale ctor imm LocMemory sa = (dst,sz) /\
  fn_has_code sa sz fn /\ not_fresh_at sa src /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ptr_covers G tn src s span /\ lookup_var src s = SOME a /\
  (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) /\
  mload (w2n a) s = n2w len_n /\ 0 < len_n /\ len_n < dimword(:256) /\
  32+(len_n-1)*scale+n <= span /\ w2n a+span < dimword(:256) ==>
  ?out t H tf.
    dst = Var out /\ gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK t) /\
    lookup_var out t = SOME (n2w (w2n a+32+(len_n-1)*scale)) /\
    ptr_covers H tf out t n /\ not_fresh_at sz out /\
    ~t.vs_halted /\ t.vs_current_bb = sz.cs_current_bb /\
    t.vs_inst_idx = LENGTH sz.cs_current_insts /\
    t.vs_memory = (mstore (w2n a) (n2w (len_n-1)) s).vs_memory /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!v. not_fresh_at sa v ==> lookup_var v t = lookup_var v s /\
      FLOOKUP H v = FLOOKUP G v /\ op_taint tf (Var v) = op_taint tn (Var v))
Proof
  strip_tac >> drule pop_memory_compile_stages >> strip_tac >>
  drule_all pop_memory_stage_code >> strip_tac >>
  `32 <= span /\ mload (w2n a) s <> 0w` by simp[] >>
  drule_all pop_memory_length_update_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `not_fresh_at sf src` by metis_tac[not_fresh_at_mono] >>
  `eval_operand new_len t = SOME (n2w (len_n-1))` by
    simp[n2w_sub] >>
  drule_all pop_element_address_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG H tf t 0 H2 tf2 (OK vstate)` >>
  qexistsl_tac [`out`, `vstate`, `H2`, `tf2`] >> simp[] >> conj_tac
  >- (drule_all gas_path_ptr_then >> simp[]) >>
  conj_tac
  >- gvs[mstore_def, n2w_sub] >>
  rpt strip_tac >>
  `not_fresh_at sf v` by metis_tac[not_fresh_at_mono] >> metis_tac[]
QED

Theorem pop_memory_suffix_empty_path:
  compile_dynarray_pop (Var src) 32 scale ctor imm LocMemory sa = (dst,sz) /\
  fn_has_code sa sz fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME a /\
  (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) /\
  mload (w2n a) s = 0w ==>
  ?t H tf. gas_path_ptr D 0 ctx fn PG G tn s 0 H tf
    (Abort Revert_abort (revert_state (set_returndata [] t)))
Proof
  strip_tac >> drule pop_memory_compile_stages >> strip_tac >>
  drule_all pop_memory_stage_code >> strip_tac >>
  drule_all pop_memory_header_empty_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
