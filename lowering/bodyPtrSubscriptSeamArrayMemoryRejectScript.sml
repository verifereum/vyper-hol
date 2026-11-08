Theory bodyPtrSubscriptSeamArrayMemoryReject
Ancestors
  bodyPtrSubscriptSeamArrayMemoryBounds bodyPtrSubscriptBoundsOutcome
  bodyPtrSubscriptSeamArrayMemoryNumeric
  bodyPtrSubscriptMarkedEndpoint bodyPtrSubscriptReadOnly bodyPtrSubscriptBounds
  bodyPtrSubscriptSignedEdge emitHelperProps exprLoweringProps freshWrites
  emitHelper compileEnv ptrDiscipline bodyPtrDefs venomState venomInst
  fragGasPathPtr fragExec venomExecSemantics words integer_word

Theorem literal_bounds_flag_counted:
  emit_op LT [idx;Lit len] sa = (Var lt,sm) /\
  emit_op ISZERO [Var lt] sm = (Var oob,sn) /\
  emit_op OR [negflag;Var oob] sn = (Var invalid,sp) /\
  emit_op ISZERO [Var invalid] sp = (Var valid,sb) /\ fn_has_code sa sb func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand idx s = SOME a /\ eval_operand negflag s = SOME n /\
  op_taint tn idx = {} /\ op_taint tn negflag = {} /\ op_prov G negflag = NONE /\
  (!q. negflag = Var q ==> not_fresh_at sa q) /\ (!l. negflag <> Label l) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    eval_operand (Var valid) sf = SOME (bool_to_word (n = 0w /\ w2n a < w2n len)) /\
    op_taint tnf (Var valid) = {} /\ op_prov Gf (Var valid) = NONE /\
    sf.vs_memory = s.vs_memory /\ sf.vs_allocas = s.vs_allocas /\
    sf.vs_fmp = s.vs_fmp /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    sf.vs_requests = s.vs_requests /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn sp /\ ci_mono sp sb` by
    metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `cs_extends sa sn /\ cs_extends sn sb` by
    metis_tac[ci_mono_def, cs_extends_trans] >>
  `fn_has_code sa sn func /\ fn_has_code sn sb func` by
    metis_tac[fn_has_code_split] >>
  drule_all literal_lt_iszero_counted >>
  disch_then (qspecl_then [`PG`, `G`, `D`] mp_tac) >>
  disch_then (qx_choosel_then [`G1`, `tn1`, `s1`] strip_assume_tac) >>
  `eval_operand negflag s1 = SOME n /\ op_taint tn1 negflag = {} /\
   op_prov G1 negflag = NONE` by (drule_all reserved_operand_read_only >> simp[]) >>
  `eval_operand (Var oob) s1 = SOME (bool_to_word (~(w2n a < w2n len)))` by
    simp[eval_operand_def] >>
  drule_all (binary_iszero_counted_read_only |>
    Q.INST [`opc` |-> `OR`, `f` |-> `word_or`] |> SIMP_RULE (srw_ss()) []) >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >>
  disch_then (qx_choosel_then [`G2`, `tn2`, `s2`] strip_assume_tac) >>
  `bool_to_word (n || bool_to_word (~(w2n a < w2n len)) = 0w) =
   (bool_to_word (n = 0w /\ w2n a < w2n len):bytes32)` by
    (Cases_on `w2n a < w2n len` >> simp[bool_to_word_def, WORD_OR_CLAUSES] >>
     POP_ASSUM_LIST (K ALL_TAC) >> wordsLib.WORD_DECIDE_TAC) >>
  qexistsl_tac [`G2`, `tn2`, `s2`] >> simp[] >> conj_tac
  >- (drule_all gas_path_ptr_then >> simp[]) >>
  rpt strip_tac >> `not_fresh_at sn p` by
    metis_tac[ci_mono_def, not_fresh_at_mono] >> metis_tac[]
QED

Theorem literal_bounds_rejects_counted:
  emit_op LT [idx;Lit len] sa = (Var lt,sm) /\
  emit_op ISZERO [Var lt] sm = (Var oob,sn) /\
  emit_op OR [negflag;Var oob] sn = (Var invalid,sp) /\
  emit_op ISZERO [Var invalid] sp = (Var valid,sq) /\
  emit_void ASSERT [Var valid] sq = ((),sb) /\ fn_has_code sa sb func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand idx s = SOME a /\ eval_operand negflag s = SOME n /\
  ~(n = 0w /\ w2n a < w2n len) /\
  op_taint tn idx = {} /\ op_taint tn negflag = {} /\ op_prov G negflag = NONE /\
  (!q. negflag = Var q ==> not_fresh_at sa q) /\ (!l. negflag <> Label l) ==>
  ?Gf tnf t.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf
      (Abort Revert_abort (revert_state (set_returndata [] t))) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_fmp = s.vs_fmp /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_requests = s.vs_requests /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn sp /\ ci_mono sp sq` by
    metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `ci_mono sq sb` by metis_tac[ci_mono_emit_void, pairTheory.SND] >>
  `cs_extends sa sq` by metis_tac[ci_mono_def, cs_extends_trans] >>
  `fn_has_code sa sq func /\ fn_has_code sq sb func` by
    metis_tac[ci_mono_def, fn_has_code_split] >>
  drule_all literal_bounds_flag_counted >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >>
  disch_then (qx_choosel_then [`G1`, `tn1`, `t`] strip_assume_tac) >>
  `eval_operand (Var valid) t = SOME 0w` by simp[bool_to_word_def] >>
  drule_all emitted_selector_assert_rejects_ptr >>
  disch_then (qspecl_then [`PG`, `G1`, `D`] mp_tac) >> strip_tac >>
  qexistsl_tac [`G1`, `tn1`, `t`] >> simp[] >>
  drule_all gas_path_ptr_then >> simp[]
QED

Theorem signed_literal_bounds_rejects_counted:
  emit_op SLT [idx;Lit 0w] sa = (Var negflag,sk) /\
  emit_op LT [idx;Lit len] sk = (Var lt,sm) /\
  emit_op ISZERO [Var lt] sm = (Var oob,sn) /\
  emit_op OR [Var negflag;Var oob] sn = (Var invalid,sp) /\
  emit_op ISZERO [Var invalid] sp = (Var valid,sq) /\
  emit_void ASSERT [Var valid] sq = ((),sb) /\ fn_has_code sa sb func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand idx s = SOME a /\ ~(0 <= w2i a /\ w2n a < w2n len) /\
  op_taint tn idx = {} /\
  (!q. idx = Var q ==> not_fresh_at sa q) /\ (!l. idx <> Label l) ==>
  ?Gf tnf t.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf
      (Abort Revert_abort (revert_state (set_returndata [] t))) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_fmp = s.vs_fmp /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_requests = s.vs_requests /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `ci_mono sa sk /\ ci_mono sk sm /\ ci_mono sm sn /\
   ci_mono sn sp /\ ci_mono sp sq` by metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `ci_mono sq sb` by metis_tac[ci_mono_emit_void, pairTheory.SND] >>
  `cs_extends sk sb` by metis_tac[ci_mono_def, cs_extends_trans] >>
  `fn_has_code sa sk func /\ fn_has_code sk sb func` by
    metis_tac[ci_mono_def, fn_has_code_split] >>
  `!dst. step_inst_base (mk_inst sa.cs_next_id SLT [idx;Lit 0w] [dst]) s =
     OK (update_var dst (bool_to_word (w2i a < 0)) s)` by
    (gen_tac >> irule (slt_step |> Q.INST [`right` |-> `Lit 0w`, `b` |-> `0w`] |>
       SIMP_RULE (srw_ss()) [WORD_LTi, word_0_w2i]) >> simp[eval_operand_def]) >>
  drule_all (literal_numeric_counted_read_only |> Q.INST [`opc` |-> `SLT`] |>
    SIMP_RULE (srw_ss()) []) >>
  disch_then (qspecl_then [`PG`, `G`, `D`] mp_tac) >>
  disch_then (qx_choosel_then [`G1`, `tn1`, `s1`] strip_assume_tac) >>
  `eval_operand idx s1 = SOME a /\ op_taint tn1 idx = {}` by
    (Cases_on `idx` >> gvs[eval_operand_def, op_taint_def]) >>
  `(!q. Var negflag = Var q ==> not_fresh_at sk q) /\
   (!l. Var negflag <> Label l)` by (simp[] >> metis_tac[emitted_operand_reserved]) >>
  `eval_operand (Var negflag) s1 = SOME (bool_to_word (w2i a < 0))` by
    simp[eval_operand_def] >>
  `~(bool_to_word (w2i a < 0) = (0w:bytes32) /\ w2n a < w2n len)` by
    (gvs[bool_to_word_def] >> intLib.COOPER_TAC) >>
  drule_all literal_bounds_rejects_counted >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >>
  disch_then (qx_choosel_then [`G2`, `tn2`, `s2`] strip_assume_tac) >>
  qexistsl_tac [`G2`, `tn2`, `s2`] >> simp[] >> conj_tac
  >- (drule_all gas_path_ptr_then >> simp[]) >>
  rpt strip_tac >> `not_fresh_at sk p` by
    metis_tac[ci_mono_def, not_fresh_at_mono] >> metis_tac[]
QED
