(* Zero-span-safe indexed address arithmetic for typed array copies. *)
Theory typedCopyReturnIndexAddressPtr
Ancestors typedCopyReturnControlPtr bodyPtrPopLocalRootFrame
  bodyPtrPopNestedLiveAddressFrame typedCopyLoopHeaderPtr bodyPtrDefs
  fragGasPathPtr fragExec emitHelperProps emitHelper compileEnv
  ptrDiscipline venomState venomInst words finite_map list

Theorem typed_copy_conditional_offset_counted[local]:
  emit_op ADD [Var root;offset] sa = (dst,sb) /\ fn_has_code sa sb fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  not_fresh_at sa root /\ lookup_var root s = SOME a /\
  eval_operand offset s = SOME (n2w off) /\
  op_taint tn (Var root) = {} /\ op_taint tn offset = {} /\
  (span <> 0 ==> ptr_covers G tn root s span) /\
  off+n <= span /\ w2n a+span < dimword(:256) ==>
  ?out t H tf. dst = Var out /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK t) /\
    lookup_var out t = SOME (n2w (w2n a+off)) /\
    op_taint tf (Var out) = {} /\
    (n <> 0 ==> ptr_covers H tf out t n) /\ not_fresh_at sb out /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!v. not_fresh_at sa v ==> lookup_var v t = lookup_var v s /\
      FLOOKUP H v = FLOOKUP G v /\ op_taint tf (Var v) = op_taint tn (Var v))
Proof
  strip_tac >> Cases_on `n = 0`
  >- (drule_all typed_copy_clean_address_counted >>
      disch_then (qspecl_then [`PG`,`G`,`D`] strip_assume_tac) >>
      qexistsl_tac [`out`,`t`,`H`,`tf`] >>
      simp[GSYM word_add_n2w]) >>
  `ptr_covers G tn root s span /\ w2n a+off < dimword(:256)` by
    (conj_tac >- (first_x_assum irule >> decide_tac) >> decide_tac) >>
  drule_all pop_emit_offset_endpoint_framed_path >>
  disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`out`,`t`,`H`,`tf`] >>
  gvs[ptr_covers_def]
QED

Theorem typed_copy_index_address_counted:
  emit_op MUL [Var ctr;Lit (n2w ss)] sb = (Var so,c1) /\
  emit_op MUL [Var ctr;Lit (n2w ds)] c1 = (Var doff,c2) /\
  emit_op ADD [Var src;Var so] c2 = (Var sp,c3) /\
  emit_op ADD [Var dst;Var doff] c3 = (Var dp,si) /\
  fn_has_code sb c1 fn /\ fn_has_code c1 c2 fn /\
  fn_has_code c2 c3 fn /\ fn_has_code c3 si fn /\
  not_fresh_at sb ctr /\ not_fresh_at sb src /\ not_fresh_at sb dst /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  lookup_var ctr s = SOME (n2w i) /\ op_taint tn (Var ctr) = {} /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  op_taint tn (Var src) = {} /\ op_taint tn (Var dst) = {} /\
  (src_span <> 0 ==> ptr_covers G tn src s src_span) /\
  (dst_span <> 0 ==> ptr_covers G tn dst s dst_span) /\
  i*ss+ss <= src_span /\ i*ds+ds <= dst_span /\
  w2n a+src_span < dimword(:256) /\ w2n b+dst_span < dimword(:256) ==>
  ?t H tf. gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK t) /\
    lookup_var sp t = SOME (n2w (w2n a+i*ss)) /\
    lookup_var dp t = SOME (n2w (w2n b+i*ds)) /\
    op_taint tf (Var sp) = {} /\ op_taint tf (Var dp) = {} /\
    (ss <> 0 ==> ptr_covers H tf sp t ss) /\
    (ds <> 0 ==> ptr_covers H tf dp t ds) /\
    not_fresh_at si sp /\ not_fresh_at si dp /\
    ~t.vs_halted /\ t.vs_current_bb = si.cs_current_bb /\
    t.vs_inst_idx = LENGTH si.cs_current_insts /\
    t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!v. not_fresh_at sb v ==> lookup_var v t = lookup_var v s /\
      FLOOKUP H v = FLOOKUP G v /\ op_taint tf (Var v) = op_taint tn (Var v))
Proof
  strip_tac >>
  `eval_operand (Var ctr) s = SOME (n2w i) /\
   eval_operand (Lit (n2w ss)) s = SOME (n2w ss) /\
   op_taint tn (Lit (n2w ss)) = {}` by simp[eval_operand_def,op_taint_def] >>
  qpat_x_assum `emit_op MUL _ sb = _` assume_tac >> drule_all pop_local_mul_exact >>
  disch_then (qspecl_then [`PG`,`G`,`D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK s1)` >>
  `sb.cs_next_var <= c1.cs_next_var /\ c1.cs_next_var <= c2.cs_next_var /\
   c2.cs_next_var <= c3.cs_next_var /\ c3.cs_next_var <= si.cs_next_var` by
    metis_tac[emitted_insts_emit_op,arithmeticTheory.LESS_EQ_ADD] >>
  `not_fresh_at c1 ctr` by metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
  `eval_operand (Var ctr) s1 = SOME (n2w i) /\ op_taint tn1 (Var ctr) = {} /\
   eval_operand (Lit (n2w ds)) s1 = SOME (n2w ds) /\
   op_taint tn1 (Lit (n2w ds)) = {}` by simp[eval_operand_def,op_taint_def] >>
  qpat_x_assum `emit_op MUL _ c1 = _` assume_tac >>
  qpat_x_assum `emit_op MUL _ sb = _` kall_tac >> drule_all pop_local_mul_exact >>
  disch_then (qspecl_then [`PG`,`G1`,`D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG G1 tn1 s1 0 G2 tn2 (OK s2)` >>
  `not_fresh_at c1 src /\ not_fresh_at c1 dst /\
   not_fresh_at c2 src /\ not_fresh_at c2 dst /\ not_fresh_at c1 so` by
    (gvs[] >> fs[not_fresh_at_def] >> decide_tac) >>
  `lookup_var src s2 = SOME a /\ op_taint tn2 (Var src) = {} /\
   eval_operand (Var so) s2 = SOME (n2w (i*ss)) /\
   op_taint tn2 (Var so) = {} /\
   (src_span <> 0 ==> ptr_covers G2 tn2 src s2 src_span)` by
    gvs[eval_operand_def,word_mul_n2w,ptr_covers_def] >>
  drule_all typed_copy_conditional_offset_counted >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG G2 tn2 s2 0 G3 tn3 (OK s3)` >>
  `not_fresh_at c2 doff /\ not_fresh_at c3 dst` by
    (gvs[] >> fs[not_fresh_at_def] >> decide_tac) >>
  `lookup_var dst s3 = SOME b /\ op_taint tn3 (Var dst) = {} /\
   eval_operand (Var doff) s3 = SOME (n2w (i*ds)) /\
   op_taint tn3 (Var doff) = {} /\
   (dst_span <> 0 ==> ptr_covers G3 tn3 dst s3 dst_span)` by
    gvs[eval_operand_def,word_mul_n2w,ptr_covers_def] >>
  qpat_x_assum `emit_op ADD _ c2 = _` kall_tac >> drule_all typed_copy_conditional_offset_counted >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG G3 tn3 s3 0 G4 tn4 (OK s4)` >>
  qexistsl_tac [`s4`,`G4`,`tn4`] >> (conj_tac >- metis_tac[gas_path_ptr_then,arithmeticTheory.ADD]) >>
  `not_fresh_at si sp` by (gvs[] >> fs[not_fresh_at_def] >> decide_tac) >>
  gvs[ptr_covers_def] >>
  reverse conj_tac >- (gen_tac >> strip_tac >>
    `not_fresh_at c1 v /\ not_fresh_at c2 v /\ not_fresh_at c3 v` by
      (fs[not_fresh_at_def] >> decide_tac) >> simp[]) >>
  qpat_x_assum `s4 = _` (fn th => once_rewrite_tac[th]) >>
  qpat_x_assum `s3 = _` (fn th => once_rewrite_tac[th]) >>
  qpat_x_assum `s2 = _` (fn th => once_rewrite_tac[th]) >>
  qpat_x_assum `s1 = _` (fn th => once_rewrite_tac[th]) >> simp[]
QED
