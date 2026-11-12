(* Bounds flags without assuming that the subsequent ASSERT succeeds. *)
Theory bodyPtrSubscriptBoundsOutcome
Ancestors
  bodyPtrSubscriptSignedEdge bodyPtrSubscriptBoundsRun bodyPtrSubscriptReadOnly
  bodyPtrSubscriptBounds exprLoweringProps emitHelperProps freshWrites
  emitHelper compileEnv ptrDiscipline bodyPtrDefs venomState venomInst
  fragGasPathPtr fragExec venomExecSemantics words integer_word

Theorem binary_iszero_counted_read_only:
  (opc = SUB /\ f = word_sub \/ opc = MUL /\ f = word_mul \/
   opc = OR /\ f = word_or \/
   opc = LT /\ f = (\a b. bool_to_word (w2n a < w2n b))) /\
  emit_op opc [left;right] sa = (Var tmp,sm) /\
  emit_op ISZERO [Var tmp] sm = (Var out,sb) /\ fn_has_code sa sb func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  op_prov G left = NONE /\ op_prov G right = NONE ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    eval_operand (Var out) sf = SOME (bool_to_word (f a b = 0w)) /\
    op_taint tnf (Var out) = {} /\ op_prov Gf (Var out) = NONE /\
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
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  `ci_mono sa sm /\ ci_mono sm sb` by
    metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[ci_mono_def, fn_has_code_split] >>
  drule_all binary_counted_read_only >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >>
  disch_then (qx_choosel_then [`G1`, `tn1`, `s1`] strip_assume_tac) >>
  `eval_operand (Var tmp) s1 = SOME (f a b)` by simp[eval_operand_def] >>
  drule_all iszero_counted_read_only >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >>
  disch_then (qx_choosel_then [`G2`, `tn2`, `s2`] strip_assume_tac) >>
  qexistsl_tac [`G2`, `tn2`, `s2`] >> simp[eval_operand_def] >> conj_tac
  >- (drule_all gas_path_ptr_then >> simp[]) >>
  rpt strip_tac >>
  `not_fresh_at sm p` by
    metis_tac[ci_mono_def, freshWritesTheory.not_fresh_at_mono] >> metis_tac[]
QED

Theorem bounds_flag_counted_read_only:
  emit_op LT [idx;len] sa = (Var lt,sm) /\
  emit_op ISZERO [Var lt] sm = (Var oob,sn) /\
  emit_op OR [negflag;Var oob] sn = (Var invalid,sp) /\
  emit_op ISZERO [Var invalid] sp = (Var valid,sb) /\ fn_has_code sa sb func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand idx s = SOME a /\ eval_operand len s = SOME b /\
  eval_operand negflag s = SOME n /\
  op_taint tn idx = {} /\ op_taint tn len = {} /\ op_taint tn negflag = {} /\
  op_prov G idx = NONE /\ op_prov G len = NONE /\ op_prov G negflag = NONE /\
  (!q. negflag = Var q ==> not_fresh_at sa q) /\ (!l. negflag <> Label l) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    eval_operand (Var valid) sf = SOME (bool_to_word (n = 0w /\ w2n a < w2n b)) /\
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
  drule_all (binary_iszero_counted_read_only |>
    Q.INST [`opc` |-> `LT`, `f` |-> `(\a b. bool_to_word (w2n a < w2n b))`] |>
    SIMP_RULE (srw_ss()) []) >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >>
  disch_then (qx_choosel_then [`G1`, `tn1`, `s1`] strip_assume_tac) >>
  `eval_operand negflag s1 = SOME n /\ op_taint tn1 negflag = {} /\
   op_prov G1 negflag = NONE` by (drule_all reserved_operand_read_only >> simp[]) >>
  drule_all (binary_iszero_counted_read_only |>
    Q.INST [`opc` |-> `OR`, `f` |-> `word_or`] |> SIMP_RULE (srw_ss()) []) >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >>
  disch_then (qx_choosel_then [`G2`, `tn2`, `s2`] strip_assume_tac) >>
  `bool_to_word (n || bool_to_word (~(w2n a < w2n b)) = 0w) =
   (bool_to_word (n = 0w /\ w2n a < w2n b):bytes32)` by
    (Cases_on `w2n a < w2n b` >> simp[bool_to_word_def, WORD_OR_CLAUSES] >>
     POP_ASSUM_LIST (K ALL_TAC) >> wordsLib.WORD_DECIDE_TAC) >>
  qexistsl_tac [`G2`, `tn2`, `s2`] >> simp[] >> conj_tac
  >- (drule_all gas_path_ptr_then >> simp[]) >>
  rpt strip_tac >> `not_fresh_at sn p` by
    metis_tac[ci_mono_def, freshWritesTheory.not_fresh_at_mono] >> metis_tac[]
QED

Theorem signed_bounds_flag_counted_read_only:
  emit_op SLT [idx;Lit 0w] sa = (Var negflag,sk) /\
  emit_op LT [idx;len] sk = (Var lt,sm) /\
  emit_op ISZERO [Var lt] sm = (Var oob,sn) /\
  emit_op OR [Var negflag;Var oob] sn = (Var invalid,sp) /\
  emit_op ISZERO [Var invalid] sp = (Var valid,sb) /\ fn_has_code sa sb func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand idx s = SOME a /\ eval_operand len s = SOME b /\
  op_taint tn idx = {} /\ op_taint tn len = {} /\
  op_prov G idx = NONE /\ op_prov G len = NONE /\
  (!q. idx = Var q \/ len = Var q ==> not_fresh_at sa q) /\
  (!l. idx <> Label l /\ len <> Label l) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    eval_operand (Var valid) sf = SOME (bool_to_word (0 <= w2i a /\ w2n a < w2n b)) /\
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
  `ci_mono sa sk /\ ci_mono sk sm /\ ci_mono sm sn /\
   ci_mono sn sp /\ ci_mono sp sb` by metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `cs_extends sk sb` by metis_tac[ci_mono_def, cs_extends_trans] >>
  `fn_has_code sa sk func /\ fn_has_code sk sb func` by
    metis_tac[ci_mono_def, fn_has_code_split] >>
  `!dst. step_inst_base (mk_inst sa.cs_next_id SLT [idx;Lit 0w] [dst]) s =
     OK (update_var dst (bool_to_word (w2i a < 0)) s)` by
    (gen_tac >> irule (slt_step |> Q.INST [`right` |-> `Lit 0w`, `b` |-> `0w`] |>
       SIMP_RULE (srw_ss()) [WORD_LTi, word_0_w2i]) >>
     simp[eval_operand_def]) >>
  `op_taint tn (Lit 0w) = {}` by simp[op_taint_def] >>
  drule_all slt_counted_read_only >>
  disch_then (qspecl_then [`PG`, `G`, `D`] mp_tac) >>
  disch_then (qx_choosel_then [`G1`, `tn1`, `s1`] strip_assume_tac) >>
  `(!l. idx <> Label l) /\ (!l. len <> Label l) /\
   (!q. idx = Var q ==> not_fresh_at sa q) /\
   (!q. len = Var q ==> not_fresh_at sa q)` by metis_tac[] >>
  `eval_operand idx s1 = SOME a /\ op_taint tn1 idx = {} /\ op_prov G1 idx = NONE` by
    metis_tac[reserved_operand_read_only] >>
  `eval_operand len s1 = SOME b /\ op_taint tn1 len = {} /\ op_prov G1 len = NONE` by
    metis_tac[reserved_operand_read_only] >>
  `(!q. Var negflag = Var q ==> not_fresh_at sk q) /\
   (!l. Var negflag <> Label l)` by (simp[] >> metis_tac[emitted_operand_reserved]) >>
  `eval_operand (Var negflag) s1 = SOME (bool_to_word (w2i a < 0))` by
    simp[eval_operand_def] >>
  drule_all bounds_flag_counted_read_only >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >>
  disch_then (qx_choosel_then [`G2`, `tn2`, `s2`] strip_assume_tac) >>
  fs[integerTheory.INT_NOT_LT] >>
  qexistsl_tac [`G2`, `tn2`, `s2`] >> simp[] >> conj_tac
  >- (drule_all gas_path_ptr_then >> simp[]) >>
  rpt strip_tac >> `not_fresh_at sk p` by
    metis_tac[ci_mono_def, freshWritesTheory.not_fresh_at_mono] >> metis_tac[]
QED
