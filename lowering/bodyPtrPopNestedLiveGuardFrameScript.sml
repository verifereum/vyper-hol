Theory bodyPtrPopNestedLiveGuardFrame
Ancestors
  bodyPtrPopLengthGuard fragGasPathPtr bodyPtrDefs emitHelperProps emitHelper
  compileEnv venomState ptrDiscipline finite_map words list stmtFragPtr venomExecSemantics

(* Companion boundary retaining the concrete register/index-only frame. *)
Theorem pop_double_iszero_framed_path:
  emit_op ISZERO [a] sa = (nz,sb) /\
  emit_op ISZERO [nz] sb = (valid,sc) /\
  fn_has_code sa sb fn /\ fn_has_code sb sc fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand a s = SOME w /\ op_taint tn a = {} ==>
  ?t H tf. gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK t) /\
    eval_operand valid t = SOME (bool_to_word (w <> 0w)) /\
    op_taint tf valid = {} /\ op_prov H valid = NONE /\
    ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\
    t.vs_inst_idx = LENGTH sc.cs_current_insts /\
    t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!v. not_fresh_at sa v ==> lookup_var v t = lookup_var v s /\
      FLOOKUP H v = FLOOKUP G v /\ op_taint tf (Var v) = op_taint tn (Var v))
Proof
  strip_tac >> drule_all pop_emit_iszero_path >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  qabbrev_tac `u = (update_var out (bool_to_word (w = 0w)) s) with
    vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `G1 = DRESTRICT G (COMPL {out})` >>
  qabbrev_tac `tn1 = tn with t_var := tn.t_var |+ (out,{})` >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sc.cs_current_bb = sb.cs_current_bb /\
   LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts) /\
   LENGTH sc.cs_current_insts = SUC (LENGTH sb.cs_current_insts) /\
   sa.cs_next_var <= sb.cs_next_var` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
        fresh_id_def, emit_def, comp_return_def] >>
  `?out2. valid = Var out2 /\ out2 = STRING #"%" (toString sb.cs_next_var) /\
    gas_path_ptr D 0 ctx fn PG G1 tn1 u 0
      (DRESTRICT G1 (COMPL {out2})) (tn1 with t_var := tn1.t_var |+ (out2,{}))
      (OK ((update_var out2 (bool_to_word (bool_to_word (w = 0w) = 0w)) u) with
        vs_inst_idx := SUC u.vs_inst_idx)) /\
    (!v. not_fresh_at sb v ==> v <> out2)` by
    (irule pop_emit_iszero_path >> simp[Abbr `u`, update_var_def] >>
     qexistsl_tac [`nz`, `sc`] >>
     simp[Abbr `tn1`, update_var_def, eval_operand_def,
          lookup_var_def, op_taint_def, FLOOKUP_UPDATE]) >>
  qexistsl_tac
    [`(update_var out2 (bool_to_word (bool_to_word (w = 0w) = 0w)) u) with
        vs_inst_idx := SUC u.vs_inst_idx`,
     `DRESTRICT G1 (COMPL {out2})`, `tn1 with t_var := tn1.t_var |+ (out2,{})`] >>
  conj_tac >- (drule_all gas_path_ptr_then >> simp[]) >>
  simp[Abbr `u`, Abbr `G1`, Abbr `tn1`, update_var_def, eval_operand_def,
       lookup_var_def, op_prov_def, op_taint_def, FLOOKUP_DRESTRICT,
       FLOOKUP_UPDATE, bool_to_word_def] >>
  rpt strip_tac >> `v <> out /\ v <> out2` by
    metis_tac[not_fresh_at_mono] >> gvs[]
QED

Theorem pop_nonempty_guard_framed_path:
  emit_op ISZERO [a] sa = (nz,sb) /\
  emit_op ISZERO [nz] sb = (valid,sc) /\
  emit_void ASSERT [valid] sc = ((),sd) /\
  fn_has_code sa sb fn /\ fn_has_code sb sc fn /\ fn_has_code sc sd fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand a s = SOME w /\ op_taint tn a = {} /\ w <> 0w ==>
  ?t H tf. gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK t) /\
    ~t.vs_halted /\ t.vs_current_bb = sd.cs_current_bb /\
    t.vs_inst_idx = LENGTH sd.cs_current_insts /\
    t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!v. not_fresh_at sa v ==> lookup_var v t = lookup_var v s /\
      FLOOKUP H v = FLOOKUP G v /\ op_taint tf (Var v) = op_taint tn (Var v))
Proof
  strip_tac >> drule_all pop_double_iszero_framed_path >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  `sd.cs_current_bb = sc.cs_current_bb /\
   LENGTH sd.cs_current_insts = SUC (LENGTH sc.cs_current_insts)` by
    gvs[emit_void_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
        fresh_id_def, emit_def, comp_return_def] >>
  `gas_path_ptr D 0 ctx fn PG H tf t 0 H tf
     (OK (t with vs_inst_idx := SUC t.vs_inst_idx))` by
    (irule pop_emit_assert_ok_path >> simp[] >>
     qexistsl_tac [`valid`, `sc`, `sd`, `1w`] >> simp[bool_to_word_def]) >>
  qexistsl_tac [`t with vs_inst_idx := SUC t.vs_inst_idx`, `H`, `tf`] >>
  conj_tac >- (drule_all gas_path_ptr_then >> simp[]) >>
  simp[lookup_var_def] >>
  conj_tac
  >- (qpat_x_assum `t = s with <|vs_vars := _; vs_inst_idx := _|>`
        (fn th => once_rewrite_tac[th]) >> simp[]) >>
  metis_tac[lookup_var_def]
QED

Theorem pop_length_guard_framed_path:
  emit_op ISZERO [a] sa = (nz,sb) /\
  emit_op ISZERO [nz] sb = (valid,sc) /\
  emit_void ASSERT [valid] sc = ((),sd) /\
  emit_op SUB [a; Lit 1w] sd = (new_len,se) /\ fn_has_code sa se fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand a s = SOME w /\ op_taint tn a = {} /\ op_prov G a = NONE /\
  (!v. a = Var v ==> not_fresh_at sa v) /\ w <> 0w ==>
  ?t H tf. gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK t) /\
    eval_operand new_len t = SOME (w-1w) /\
    op_taint tf new_len = {} /\ op_prov H new_len = NONE /\
    ~t.vs_halted /\ t.vs_current_bb = se.cs_current_bb /\
    t.vs_inst_idx = LENGTH se.cs_current_insts /\
    t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!v. not_fresh_at sa v ==> lookup_var v t = lookup_var v s /\
      FLOOKUP H v = FLOOKUP G v /\ op_taint tf (Var v) = op_taint tn (Var v))
Proof
  strip_tac >> drule_all pop_length_guard_code >> strip_tac >>
  drule_all pop_nonempty_guard_framed_path >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  `t.vs_labels = s.vs_labels` by
    (qpat_x_assum `t = s with <|vs_vars := _; vs_inst_idx := _|>`
      (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `eval_operand a t = SOME w /\ op_taint tf a = {} /\ op_prov H a = NONE` by
    (Cases_on `a` >> gvs[eval_operand_def, op_taint_def, op_prov_def] >>
     metis_tac[]) >>
  `?out. new_len = Var out /\ out = STRING #"%" (toString sd.cs_next_var) /\
    gas_path_ptr D 0 ctx fn PG H tf t 0
      (DRESTRICT H (COMPL {out})) (tf with t_var := tf.t_var |+ (out,{}))
      (OK ((update_var out (w-1w) t) with vs_inst_idx := SUC t.vs_inst_idx)) /\
    (!v. not_fresh_at sd v ==> v <> out)` by
    (irule pop_emit_sub_path >> simp[] >>
     qexistsl_tac [`a`, `Lit 1w`, `se`] >>
     simp[eval_operand_def, op_taint_def, op_prov_def]) >>
  `se.cs_current_bb = sd.cs_current_bb /\
   LENGTH se.cs_current_insts = SUC (LENGTH sd.cs_current_insts)` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
        fresh_id_def, emit_def, comp_return_def] >>
  qexistsl_tac [`(update_var out (w-1w) t) with vs_inst_idx := SUC t.vs_inst_idx`,
    `DRESTRICT H (COMPL {out})`, `tf with t_var := tf.t_var |+ (out,{})`] >>
  conj_tac >- (drule_all gas_path_ptr_then >> simp[]) >>
  simp[eval_operand_def, lookup_var_def, update_var_def,
       op_taint_def, op_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  conj_tac
  >- (qpat_x_assum `t = s with <|vs_vars := _; vs_inst_idx := _|>`
        (fn th => once_rewrite_tac[th]) >> simp[]) >>
  rpt strip_tac >> `v <> out` by metis_tac[not_fresh_at_mono] >>
  qpat_x_assum `!v. not_fresh_at sa v ==> _ /\ _ /\ _`
    (qspec_then `v` mp_tac) >> gvs[lookup_var_def, op_taint_def]
QED
