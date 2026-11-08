Theory bodyPtrPopLocalRootAddressFrame
Ancestors
  bodyPtrPopLocalRootFrame bodyPtrDefs
  emitHelperProps emitHelper compileEnv venomState ptrDiscipline
  finite_map words list fragGasPathPtr

Theorem pop_local_mul_add_exact:
  emit_op MUL [new_len; Lit (n2w esz)] sa = (offset,sb) /\
  emit_op ADD [Var data;offset] sb = (dst,sc) /\
  fn_has_code sa sb fn /\ fn_has_code sb sc fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  not_fresh_at sa data /\ lookup_var data s = SOME a /\
  ptr_covers G tn data s bytes /\
  eval_operand new_len s = SOME (n2w k) /\ op_taint tn new_len = {} /\
  k*esz < bytes /\ k*esz+esz <= bytes /\
  w2n a+bytes <= dimword(:256) ==>
  ?out t G' tn'. dst = Var out /\ not_fresh_at sc out /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
    lookup_var out t = SOME (n2w (w2n a+k*esz)) /\
    ptr_covers G' tn' out t esz /\
    ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\
    t.vs_inst_idx = LENGTH sc.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_labels = s.vs_labels /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!v. not_fresh_at sa v ==> lookup_var v t = lookup_var v s /\
      FLOOKUP G' v = FLOOKUP G v /\ op_taint tn' (Var v) = op_taint tn (Var v))
Proof
  strip_tac >>
  `eval_operand (Lit (n2w esz)) s = SOME (n2w esz) /\
   op_taint tn (Lit (n2w esz)) = {}` by simp[eval_operand_def, op_taint_def] >>
  drule_all pop_local_mul_exact >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  `not_fresh_at sb data /\
   (!v. not_fresh_at sa v ==> not_fresh_at sb v)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_SUC_REFL]) >>
  `lookup_var data t = SOME a /\ ptr_covers G' tn' data t bytes` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  `eval_operand offset t = SOME (n2w (k*esz)) /\
   w2n a+k*esz < dimword(:256)` by
    (simp[GSYM word_mul_n2w] >> decide_tac) >>
  drule_all (Q.INST [`off` |-> `k*esz`, `n` |-> `esz`]
    (SPEC_ALL pop_local_interior_exact)) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`out'`, `t'`, `G''`, `tn''`] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  conj_tac >- (drule_all gas_path_ptr_then >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `t' = t with <|vs_vars := _; vs_inst_idx := _|>` SUBST1_TAC >>
      qpat_x_assum `t = s with <|vs_vars := _; vs_inst_idx := _|>` SUBST1_TAC >> simp[]) >>
  simp[] >> metis_tac[]
QED

Theorem pop_local_address_suffix_exact:
  emit_op ADD [Var root; Lit 32w] sa = (data,sb) /\
  emit_op MUL [new_len; Lit (n2w esz)] sb = (offset,sc) /\
  emit_op ADD [data;offset] sc = (dst,sd) /\
  fn_has_code sa sb fn /\ fn_has_code sb sc fn /\ fn_has_code sc sd fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  not_fresh_at sa root /\ lookup_var root s = SOME a /\
  ptr_covers G tn root s bytes /\
  (!v. new_len = Var v ==> not_fresh_at sa v) /\
  eval_operand new_len s = SOME (n2w k) /\ op_taint tn new_len = {} /\
  32+k*esz < bytes /\ 32+k*esz+esz <= bytes /\
  w2n a+bytes <= dimword(:256) ==>
  ?out t G' tn'. dst = Var out /\ not_fresh_at sd out /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
    lookup_var out t = SOME (n2w (w2n a+32+k*esz)) /\
    ptr_covers G' tn' out t esz /\
    ~t.vs_halted /\ t.vs_current_bb = sd.cs_current_bb /\
    t.vs_inst_idx = LENGTH sd.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_labels = s.vs_labels /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!v. not_fresh_at sa v ==> lookup_var v t = lookup_var v s /\
      FLOOKUP G' v = FLOOKUP G v /\ op_taint tn' (Var v) = op_taint tn (Var v))
Proof
  strip_tac >>
  `eval_operand (Lit 32w) s = SOME (n2w 32) /\
   op_taint tn (Lit 32w) = {} /\ 32 < bytes /\
   32+(bytes-32) <= bytes /\ w2n a+32 < dimword(:256)` by
    (simp[eval_operand_def, op_taint_def] >> decide_tac) >>
  drule_all (Q.INST [`off` |-> `32`, `n` |-> `bytes-32`]
    (SPEC_ALL pop_local_interior_exact)) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `!v. not_fresh_at sa v ==> not_fresh_at sb v` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_SUC_REFL]) >>
  `eval_operand new_len t = SOME (n2w k) /\ op_taint tn' new_len = {}` by
    (Cases_on `new_len` >> gvs[eval_operand_def, op_taint_def]) >>
  `w2n a+32 < dimword(:256)` by decide_tac >>
  `w2n (n2w (w2n a+32):bytes32) = w2n a+32` by simp[] >>
  `k*esz < bytes-32 /\ k*esz+esz <= bytes-32 /\
   w2n (n2w (w2n a+32):bytes32)+(bytes-32) <= dimword(:256)` by
    (simp[] >> decide_tac) >>
  qpat_x_assum `data = Var out` SUBST_ALL_TAC >>
  drule_all pop_local_mul_add_exact >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`out'`, `t'`, `G''`, `tn''`] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  conj_tac >- (drule_all gas_path_ptr_then >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `t' = t with <|vs_vars := _; vs_inst_idx := _|>` SUBST1_TAC >>
      qpat_x_assum `t = s with <|vs_vars := _; vs_inst_idx := _|>` SUBST1_TAC >> simp[]) >>
  simp[] >> metis_tac[]
QED
