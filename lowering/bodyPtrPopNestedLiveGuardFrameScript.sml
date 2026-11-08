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
