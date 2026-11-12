Theory bodyPtrPopNestedLiveAddress
Ancestors
  bodyPtrPopInteriorPointer bodyPtrPopNestedLiveArithmetic bodyPtrAttributeAdd
  typedCopyLoopHeaderPtr bodyPtrDefs emitHelperProps emitHelper compileEnv loweringStateRelDefs
  ptrDiscipline venomState venomInst words finite_map pred_set stmtFragPtr fragGasPathPtr

(* Unlike the strict-interior toolkit lemma this permits zero-byte values
   at the end of an allocation.  No memory access is made by ADD. *)
Theorem pop_dynamic_offset_endpoint_covers:
  lookup_var root s = SOME a /\
  eval_operand offset s = SOME (n2w off) /\
  op_taint tn offset = {} /\ ptr_covers G tn root s span /\
  off+n <= span /\ w2n a+off < dimword(:256) ==>
  ptr_covers
    (step_prov PG G (mk_inst id ADD [Var root;offset] [out])
      (update_var out (a+n2w off) s))
    (step_taint (mk_inst id ADD [Var root;offset] [out]) s
      (update_var out (a+n2w off) s) tn)
    out (update_var out (a+n2w off) s) n
Proof
  strip_tac >>
  `op_taint tn (Var root) = {}` by gvs[ptr_covers_def] >>
  `op_taint (step_taint (mk_inst id ADD [Var root;offset] [out]) s
    (update_var out (a+n2w off) s) tn) (Var out) = {}` by
    simp[typedCopyPtrTheory.copy_len_binop_ghost_frame] >>
  gvs[ptr_covers_def] >>
  `off < dimword(:256)` by decide_tac >>
  simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
       op_prov_def, mk_inst_def, FLOOKUP_UPDATE, lookup_var_def,
       update_var_def, w2n_add_2, w2n_n2w, arithmeticTheory.LESS_MOD] >>
  decide_tac
QED

Theorem pop_emit_offset_endpoint_path:
  !sa sb dst root offset fn ctx s a off tn G span n D PG.
  emit_op ADD [Var root;offset] sa = (dst,sb) /\ fn_has_code sa sb fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  not_fresh_at sa root /\ lookup_var root s = SOME a /\
  eval_operand offset s = SOME (n2w off) /\ op_taint tn offset = {} /\
  ptr_covers G tn root s span /\ off+n <= span /\
  w2n a+off < dimword(:256) ==>
  ?out t H tf. dst = Var out /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK t) /\
    lookup_var out t = SOME (n2w (w2n a+off)) /\
    ptr_covers H tf out t n /\ not_fresh_at sb out /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_labels = s.vs_labels /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!v. not_fresh_at sa v ==> lookup_var v t = lookup_var v s /\
      FLOOKUP H v = FLOOKUP G v /\ op_taint tf (Var v) = op_taint tn (Var v))
Proof
  rpt gen_tac >> strip_tac >>
  `op_taint tn (Var root) = {}` by gvs[ptr_covers_def] >>
  `?out H tf t.
    dst = Var out /\ gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK t) /\
    t = (update_var out (a+n2w off) s with vs_inst_idx := SUC s.vs_inst_idx) /\
    H = step_prov PG G (mk_inst sa.cs_next_id ADD [Var root;offset] [out])
      (update_var out (a+n2w off) s) /\
    tf = step_taint (mk_inst sa.cs_next_id ADD [Var root;offset] [out]) s
      (update_var out (a+n2w off) s) tn /\
    tf.t_imm = tn.t_imm /\ op_taint tf (Var out) = {} /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!v. v <> out ==> FLOOKUP H v = FLOOKUP G v /\
      op_taint tf (Var v) = op_taint tn (Var v))` by
    (irule attribute_emit_binop_path_ptr >> simp[eval_operand_def] >>
     qexistsl_tac [`Var root`, `offset`, `sb`] >> simp[]) >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts) /\
   not_fresh_at sb out /\ (!v. not_fresh_at sa v ==> v <> out)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `ptr_covers H tf out (update_var out (a+n2w off) s) n` by
    (simp[] >> irule pop_dynamic_offset_endpoint_covers >> metis_tac[]) >>
  `a+n2w off = n2w (w2n a+off)` by simp[GSYM word_add_n2w] >>
  `ptr_covers H tf out t n` by
    gvs[ptr_covers_def, update_var_def, lookup_var_def] >>
  qexistsl_tac [`out`, `t`, `H`, `tf`] >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> `v <> out` by metis_tac[] >>
  gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem pop_scaled_offset_path:
  emit_op MUL [ix;Lit (n2w scale)] sa = (offset,sb) /\
  emit_op ADD [Var root;offset] sb = (dst,sc) /\
  fn_has_code sa sb fn /\ fn_has_code sb sc fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  not_fresh_at sa root /\ lookup_var root s = SOME a /\
  eval_operand ix s = SOME (n2w index) /\
  op_prov G ix = NONE /\ op_taint tn ix = {} /\
  ptr_covers G tn root s span /\ index*scale+n <= span /\
  w2n a+index*scale < dimword(:256) ==>
  ?out t H tf. dst = Var out /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK t) /\
    lookup_var out t = SOME (n2w (w2n a+index*scale)) /\
    ptr_covers H tf out t n /\ not_fresh_at sc out /\
    ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\
    t.vs_inst_idx = LENGTH sc.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_labels = s.vs_labels /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!v. not_fresh_at sa v ==> lookup_var v t = lookup_var v s /\
      FLOOKUP H v = FLOOKUP G v /\ op_taint tf (Var v) = op_taint tn (Var v))
Proof
  strip_tac >>
  `eval_operand (Lit (n2w scale)) s = SOME (n2w scale) /\
   op_prov G (Lit (n2w scale)) = NONE /\
   op_taint tn (Lit (n2w scale)) = {}` by
    simp[eval_operand_def, op_prov_def, op_taint_def] >>
  drule_all pop_scalar_mul_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `sa.cs_next_var <= sb.cs_next_var` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
        fresh_id_def, emit_def, comp_return_def] >>
  `not_fresh_at sb root` by metis_tac[not_fresh_at_mono] >>
  `lookup_var root t = SOME a /\ ptr_covers H tf root t span` by
    (fs[ptr_covers_def] >> gvs[]) >>
  `eval_operand offset t = SOME (n2w (index*scale))` by simp[word_mul_n2w] >>
  qpat_x_assum `offset = Var out` SUBST_ALL_TAC >>
  drule_all pop_emit_offset_endpoint_path >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG H tf t 0 H2 tf2 (OK u)` >>
  qexistsl_tac [`out'`, `u`, `H2`, `tf2`] >> simp[] >> conj_tac
  >- (drule_all gas_path_ptr_then >> simp[]) >>
  rpt strip_tac >>
  `not_fresh_at sb v` by metis_tac[not_fresh_at_mono] >> metis_tac[]
QED

Theorem pop_element_address_path:
  emit_op ADD [Var root;Lit 32w] sa = (data,sb) /\
  emit_op MUL [ix;Lit (n2w scale)] sb = (offset,sc) /\
  emit_op ADD [data;offset] sc = (dst,sd) /\
  fn_has_code sa sb fn /\ fn_has_code sb sc fn /\ fn_has_code sc sd fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  not_fresh_at sa root /\ lookup_var root s = SOME a /\
  (!v. ix = Var v ==> not_fresh_at sa v) /\
  eval_operand ix s = SOME (n2w index) /\
  op_prov G ix = NONE /\ op_taint tn ix = {} /\
  ptr_covers G tn root s span /\ 32+index*scale+n <= span /\
  w2n a+span < dimword(:256) ==>
  ?out t H tf. dst = Var out /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK t) /\
    lookup_var out t = SOME (n2w (w2n a+32+index*scale)) /\
    ptr_covers H tf out t n /\ not_fresh_at sd out /\
    ~t.vs_halted /\ t.vs_current_bb = sd.cs_current_bb /\
    t.vs_inst_idx = LENGTH sd.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_labels = s.vs_labels /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!v. not_fresh_at sa v ==> lookup_var v t = lookup_var v s /\
      FLOOKUP H v = FLOOKUP G v /\ op_taint tf (Var v) = op_taint tn (Var v))
Proof
  strip_tac >>
  `eval_operand (Lit 32w) s = SOME (n2w 32) /\ op_taint tn (Lit 32w) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  `32+(span-32) <= span /\ w2n a+32 < dimword(:256)` by decide_tac >>
  drule_all pop_emit_offset_endpoint_path >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  `sa.cs_next_var <= sb.cs_next_var` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
        fresh_id_def, emit_def, comp_return_def] >>
  `eval_operand ix t = SOME (n2w index) /\ op_prov H ix = NONE /\
   op_taint tf ix = {}` by
    (Cases_on `ix` >> gvs[eval_operand_def, op_prov_def, op_taint_def]) >>
  `index*scale+n <= span-32 /\
   w2n (n2w (w2n a+32):bytes32)+index*scale < dimword(:256)` by
    (simp[w2n_n2w, arithmeticTheory.LESS_MOD] >> decide_tac) >>
  qpat_x_assum `data = Var out` SUBST_ALL_TAC >>
  drule_all pop_scaled_offset_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG H tf t 0 H2 tf2 (OK u)` >>
  qexistsl_tac [`out'`, `u`, `H2`, `tf2`] >>
  simp[w2n_n2w, arithmeticTheory.LESS_MOD] >> conj_tac
  >- (drule_all gas_path_ptr_then >> simp[]) >>
  rpt strip_tac >>
  `not_fresh_at sb v` by metis_tac[not_fresh_at_mono] >> metis_tac[]
QED
