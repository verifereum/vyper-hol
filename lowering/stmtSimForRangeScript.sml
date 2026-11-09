(*
 * Statement simulation: For over a range whose ends are not both literals
 * (#637)
 *
 * The ends are forced with read_result and lowered as values (expr_sim),
 * then the loop variable's
 * ALLOCA and the entry block, which with nonliteral ends computes the
 * number of rounds and checks the range (compile_range_bound_checks):
 * start <= end, signed or unsigned, and rounds <= the loop's bound, each
 * an ASSERT.  The source raises a runtime error in the same two cases
 * ("no range", "For too long"), which an ASSERT's revert exits as.  From
 * the condition block on the loop is stmtSimForLoop's for_loop.
 *
 * TOP-LEVEL:
 *   compile_for_range_checked_frag_active — the statement fragment of For over
 *                                    such a range
 *   eval_stmt_for_range_cases      — the source outcomes of a range over
 *                                    expressions
 *   range_end_words                — the range's words: the order check
 *                                    and the rounds
 *
 * Helper: range_outcome, for_entry_checked_block, for_range_checked_code,
 *   compile_stmt_for_range_checked, for_range_checked_parts
 *)

Theory stmtSimForRange
Ancestors
  stmtSimProps
  exprSimProps
  stmtSimDefs
  exprSimDefs
  loweringPosts
   stmtSimForParts stmtSimForLoop exprWordOperand
  list rich_list finite_map pred_set
  fragExec localPtrsProps  loweringSlice freshWrites
  vyperEvalExprPreservesScopesDom
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding
  vyperInterpreter vyperState vyperValue vyperTyping vyperEvalPreservesScopes
  vyperExprNoControl vyperValueOperation
  gasOutcome gasContext gasExemptCert gasSummary gasSummaryCompose stmtSimForRounds vyperArith
  stmtSimDeclGas stmtSimDeclCompose
  fragGasSeq fragGasSeqAbort fragGasPath fragGasMode gasCount instIdxIndep
  venomExecSemantics venomExecProofs venomInst venomState integer_word
Libs
  monadsyntax intLib

(* ===== The source ===== *)

(* An expression's result in a statement whose outcome stmt_frag speaks
   of: an exception it raises is no control exception, nor a type error. *)
Theorem expr_res_ok_of_exn[local]:
  !cx e es ex es1 lctx.
    (do raw <- eval_expr cx e; read_result cx raw od) es = (INR ex, es1) /\
    stmt_res_ok lctx (INR ex : unit + exception) ==>
    expr_res_ok (INR ex : value + exception)
Proof
  rpt strip_tac >>
  qpat_x_assum `(do raw <- _; _ od) _ = _` mp_tac >>
  simp[bind_def] >> Cases_on `eval_expr cx e es` >>
  rename1 `_ = (raw, est)` >> Cases_on `raw` >> simp[] >> strip_tac >>
  imp_res_tac read_result_no_control >>
  imp_res_tac (cj 1 eval_expr_no_control) >>
  Cases_on `ex` >> gvs[no_control_exc_def, expr_res_ok_def, stmt_res_ok_def]
QED

(* Reassociate the iterator at the same forced-value boundary as expr_sim.
   This includes captured places and exceptions raised by read_result. *)
Theorem eval_iterator_range_forced[local]:
  !cx e1 e2.
    eval_iterator cx (Range e1 e2) =
    do v1 <- (do raw <- eval_expr cx e1; read_result cx raw od);
       v2 <- (do raw <- eval_expr cx e2; read_result cx raw od);
       rl <- lift_sum (get_range_limits v1 v2);
       return (GENLIST (\j. IntV (FST rl + &j)) (SND rl))
    od
Proof
  rpt gen_tac >> simp[Once evaluate_def, FUN_EQ_THM, bind_def] >>
  qx_gen_tac `es` >> Cases_on `eval_expr cx e1 es` >>
  rename1 `_ = (raw1, es1)` >> Cases_on `raw1` >> simp[] >>
  rename1 `read_result cx tv1 es1` >>
  Cases_on `read_result cx tv1 es1` >> rename1 `_ = (r1, es2)` >>
  Cases_on `r1` >> simp[] >>
  Cases_on `eval_expr cx e2 es2` >> rename1 `_ = (raw2, es3)` >>
  Cases_on `raw2` >> simp[] >>
  rename1 `read_result cx tv2 es3` >>
  Cases_on `read_result cx tv2 es3` >> rename1 `_ = (r2, es4)` >>
  Cases_on `r2` >> simp[]
QED

Theorem eval_stmt_for_range_forced[local]:
  !cx fty tyv id e1 e2 bound body.
  evaluate_type (get_tenv cx) fty = SOME tyv ==>
  eval_stmt cx (For id fty (Range e1 e2) bound body) =
  do v1 <- (do raw <- eval_expr cx e1; read_result cx raw od);
     v2 <- (do raw <- eval_expr cx e2; read_result cx raw od);
     rl <- lift_sum (get_range_limits v1 v2);
     check (compatible_bound (Dynamic bound) (SND rl)) "For too long";
     eval_for cx tyv id body
       (GENLIST (\j. IntV (FST rl + &j)) (SND rl))
  od
Proof
  rpt gen_tac >> strip_tac >> pure_once_rewrite_tac[Once evaluate_def] >>
  simp[LET_THM, lift_option_type_def, eval_iterator_range_forced,
       bind_assoc, bind_return, LENGTH_GENLIST]
QED

(* The result predicate of a whole statement rules out a forced end's
   type error; other expression exceptions cannot be loop control. *)
Theorem forced_endpoint_admissible[local]:
  !cx e next lctx es.
  gas_admissible (bind (bind (eval_expr cx e) (read_result cx)) next)
    (stmt_res_ok lctx) es ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  rpt gen_tac >> strip_tac >> rw[gas_admissible_def] >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  rename1 `INR ex` >> irule expr_res_ok_of_exn >>
  conj_tac >- (qexistsl_tac [`cx`, `e`, `es with gas_obs := gs`, `ee`] >>
               simp[SF ETA_ss]) >>
  qexists_tac `lctx` >>
  qpat_x_assum `gas_admissible _ _ _` mp_tac >>
  simp[gas_admissible_def] >>
  disch_then (qspec_then `gs` mp_tac) >> simp[bind_def]
QED

Theorem forced_endpoint_error_cert[local]:
  !memory tops ctx func cx e next es s0 marks err ee leaf finish.
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (bind (eval_expr cx e) (read_result cx)) (return ()))
    (es,s0) marks (err,ee) (leaf,finish) ==>
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (bind (bind (eval_expr cx e) (read_result cx)) next)
      (return ())) (es,s0) marks (err,ee) (leaf,finish)
Proof
  rpt strip_tac >> pure_once_rewrite_tac[ignore_bind_def] >>
  pure_once_rewrite_tac[bind_assoc] >>
  irule gas_exempt_cert_error_value >> simp[]
QED
(* A marked prefix supplies the frozen endpoint hypotheses at exactly the
   canonical state used by bind composition, even for gas-sensitive H. *)
Theorem marked_endpoint_normalized[local]:
  !memory ctx func source es s0 marks v mid t H.
  gas_marked_exec memory (ctx,func) source (es,s0) marks (INL v) mid (OK t) /\
  (!gs v ee. source (es with gas_obs := gs) = (INL v,ee) ==> H v ee) ==>
  H v (mid with gas_obs := [])
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!gs v ee. _` irule >>
  qexists_tac `gas_explicit marks s0.vs_gas_readings` >>
  fs[gas_marked_exec_def] >>
  first_x_assum (qspec_then `[]` mp_tac) >> simp[]
QED

Theorem forced_endpoint_tail_cert[local]:
  !memory tops ctx func cx e next es s0 left v mid t right err ee leaf finish.
  gas_marked_exec memory (ctx,func)
    (bind (eval_expr cx e) (read_result cx))
    (es,s0) left (INL v) mid (OK t) /\
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (next v) (return ()))
    (mid with gas_obs := [],t) right (err,ee) (leaf,finish) ==>
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (bind (bind (eval_expr cx e) (read_result cx)) next)
      (return ())) (es,s0) (left ++ right) (err,ee) (leaf,finish)
Proof
  rpt strip_tac >> pure_once_rewrite_tac[ignore_bind_def] >>
  pure_once_rewrite_tac[bind_assoc] >>
  drule gas_exempt_cert_bind_value >> disch_then irule >>
  simp[GSYM ignore_bind_def]
QED

Theorem checked_range_tail[local]:
  !cx tyv id body bound n1 n2.
  (do rl <- lift_sum (get_range_limits (IntV n1) (IntV n2));
      check (compatible_bound (Dynamic bound) (SND rl)) "For too long";
      eval_for cx tyv id body
        (GENLIST (\j. IntV (FST rl + &j)) (SND rl)) od) =
  if n1 <= n2 then
    if Num (n2 - n1) <= bound then
      eval_for cx tyv id body
        (GENLIST (\j. IntV (n1 + &j)) (Num (n2 - n1)))
    else raise (Error (RuntimeError "For too long"))
  else raise (Error (RuntimeError "no range"))
Proof
  rpt gen_tac >>
  simp[get_range_limits_def, lift_sum_def, check_def, assert_def,
       compatible_bound_def] >>
  Cases_on `n1 <= n2` >>
  simp[FUN_EQ_THM, bind_def, ignore_bind_def, return_def, raise_def, assert_def] >>
  Cases_on `Num (n2 - n1) <= bound` >> simp[return_def, raise_def]
QED


(* What a range loop over [n1, n2) does after its ends, from es2: the
   range's runtime errors (start above end, more rounds than the bound), or
   the loop over its values. *)
Definition range_outcome_def:
  range_outcome cx tyv id body bound n1 n2 es2 res es' <=>
    (n2 < n1 /\ res = INR (Error (RuntimeError "no range")) /\ es' = es2) \/
    (n1 <= n2 /\ bound < Num (n2 - n1) /\
     res = INR (Error (RuntimeError "For too long")) /\ es' = es2) \/
    (n1 <= n2 /\ Num (n2 - n1) <= bound /\
     eval_for cx tyv id body (GENLIST (\j. IntV (n1 + &j)) (Num (n2 - n1)))
       es2 = (res, es'))
End

(* A range over two expressions whose values are integers, for the outcomes
   stmt_frag speaks of: the start's error, the end's error, the range's
   runtime errors (start above end, more rounds than the bound), or the
   loop over its values. *)
Theorem eval_stmt_for_range_cases:
  !cx id fty e1 e2 bound body es res es' tyv lctx.
    eval_stmt cx (For id fty (Range e1 e2) bound body) es = (res, es') /\
    evaluate_type (get_tenv cx) fty = SOME tyv /\ stmt_res_ok lctx res /\
    (!tv es1. (do raw <- eval_expr cx e1; read_result cx raw od) es = (INL tv, es1) ==>
       ?n1. tv = IntV n1 /\
            !tv2 es2. (do raw <- eval_expr cx e2; read_result cx raw od) es1 = (INL tv2, es2) ==>
                      ?n2. tv2 = IntV n2) ==>
    ?r1 es1.
      (do raw <- eval_expr cx e1; read_result cx raw od) es = (r1, es1) /\ expr_res_ok r1 /\
      ((?ex. r1 = INR ex /\ res = INR ex /\ es' = es1) \/
       ?n1 r2 es2.
         r1 = INL (IntV n1) /\
         (do raw <- eval_expr cx e2; read_result cx raw od) es1 = (r2, es2) /\ expr_res_ok r2 /\
         ((?ex. r2 = INR ex /\ res = INR ex /\ es' = es2) \/
          ?n2. r2 = INL (IntV n2) /\
               range_outcome cx tyv id body bound n1 n2 es2 res es'))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  pure_rewrite_tac[Once evaluate_def, eval_iterator_range_forced] >>
  simp[LET_THM, lift_option_type_def, return_def, Once bind_def] >>
  Cases_on `(do raw <- eval_expr cx e1; read_result cx raw od) es` >>
  rename1 `_ = (r1, es1)` >>
  simp[Once bind_def] >> simp[Once bind_def] >>
  reverse (Cases_on `r1`) >> simp[raise_def]
  >- (strip_tac >> gvs[] >> irule expr_res_ok_of_exn >> metis_tac[]) >>
  rename1 `INL tv1` >>
  qpat_x_assum `!tv es1. _ ==> ?n1. _` (qspecl_then [`tv1`, `es1`] mp_tac) >>
  simp[] >> strip_tac >>
  gvs[return_def, expr_res_ok_def] >>
  Cases_on `(do raw <- eval_expr cx e2; read_result cx raw od) es1` >>
  rename1 `_ = (r2, es2)` >> simp[Once bind_def] >>
  reverse (Cases_on `r2`) >> simp[raise_def]
  >- (strip_tac >> gvs[] >> drule expr_res_ok_of_exn >>
      disch_then drule >> simp[expr_res_ok_def]) >>
  rename1 `INL tv2` >>
  qpat_x_assum `!tv2 es2. _ ==> ?n2. _` (qspecl_then [`tv2`, `es2`] mp_tac) >>
  simp[] >> strip_tac >>
  gvs[bind_def, ignore_bind_def, return_def, expr_res_ok_def,
      get_range_limits_def, range_outcome_def] >>
  Cases_on `n1 <= n2` >>
  gvs[lift_sum_def, raise_def, return_def, check_def, assert_def,
      compatible_bound_def]
  >- (Cases_on `Num (n2 - n1) <= bound` >>
      gvs[raise_def, return_def] >> rw[] >> intLib.ARITH_TAC) >>
  rw[] >> intLib.ARITH_TAC
QED

(* ===== The range's words ===== *)

(* end - start of a range that fits a word, as a word: the rounds. *)
Theorem rounds_word[local]:
  !n1 n2. n1 <= n2 /\ n2 - n1 < &dimword (:256) ==>
          Num (n2 - n1) < dimword (:256) /\
          w2n (i2w n2 - i2w n1 : bytes32) = Num (n2 - n1)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `N = Num (n2 - n1)` >>
  `&N = n2 - n1` by (simp[Abbr `N`] >> intLib.ARITH_TAC) >>
  `N < dimword (:256)` by intLib.ARITH_TAC >>
  `(i2w n2 : bytes32) = i2w n1 + n2w N` by
    (`n2 = n1 + &N` by intLib.ARITH_TAC >> pop_assum SUBST1_TAC >>
     simp[GSYM word_i2w_add, i2w_pos]) >>
  `i2w n1 + n2w N - i2w n1 = (n2w N : bytes32)` by
    metis_tac[wordsTheory.WORD_ADD_SUB, wordsTheory.WORD_ADD_COMM] >>
  simp[wordsTheory.w2n_n2w]
QED

Theorem is_int_type_cases[local]:
  !t. is_int_type t <=> (?m. t = BaseT (UintT m)) \/ (?m. t = BaseT (IntT m))
Proof
  Cases >> simp[] >> rename1 `BaseT bt` >> Cases_on `bt` >> simp[]
QED

(* The ends' words, for ends of the loop variable's integer type: the
   comparison compile_range_bound_checks makes (signed for a signed type)
   says start > end exactly when the source has no range, and the rounds
   end - start is the range's length. *)
Theorem range_end_words:
  !tenv fty tyv n1 n2.
    is_int_type fty /\ evaluate_type tenv fty = SOME tyv /\
    value_has_type tyv (IntV n1) /\ value_has_type tyv (IntV n2) ==>
    ((if is_signed_type fty then word_gt (i2w n1 : bytes32) (i2w n2)
      else w2n (i2w n1 : bytes32) > w2n (i2w n2 : bytes32)) <=> n2 < n1) /\
    (n1 <= n2 ==>
     Num (n2 - n1) < dimword (:256) /\
     w2n (i2w n2 - i2w n1 : bytes32) = Num (n2 - n1))
Proof
  rpt gen_tac >> REWRITE_TAC [is_int_type_cases] >> strip_tac >>
  gvs[evaluate_type_def, AllCaseEqs(), value_has_type_def,
      is_signed_type_def]
  >- (`2 ** m <= dimword (:256)` by
        simp[wordsTheory.dimword_def, arithmeticTheory.EXP_BASE_LE_MONO] >>
      `?k1 k2. n1 = &k1 /\ n2 = &k2` by
        metis_tac[integerTheory.NUM_POSINT_EXISTS] >>
      gvs[] >>
      `k1 < dimword (:256) /\ k2 < dimword (:256)` by decide_tac >>
      conj_tac
      >- (simp[i2w_pos, wordsTheory.w2n_n2w] >> intLib.ARITH_TAC) >>
      strip_tac >> irule rounds_word >> intLib.ARITH_TAC) >>
  `INT_MIN (:256) <= n1 /\ n1 <= INT_MAX (:256) /\
   INT_MIN (:256) <= n2 /\ n2 <= INT_MAX (:256)` by
    metis_tac[vyperArithTheory.within_int_bound_in_word_range] >>
  `w2i (i2w n1 : bytes32) = n1 /\ w2i (i2w n2 : bytes32) = n2` by
    metis_tac[vyperArithTheory.w2i_i2w_within_signed] >>
  conj_tac >- (simp[WORD_GTi] >> intLib.ARITH_TAC) >>
  strip_tac >> irule rounds_word >>
  fs[integer_wordTheory.INT_MIN_def, integer_wordTheory.INT_MAX_def,
     wordsTheory.INT_MIN_def, wordsTheory.dimword_def] >>
  intLib.ARITH_TAC
QED

(* ===== The checked entry block ===== *)

Theorem eval_operand_update_other_op[local]:
  !op x w s. (!y. op = Var y ==> y <> x) ==>
             eval_operand op (update_var x w s) = eval_operand op s
Proof
  Cases >> simp[eval_operand_def, lookup_var_update_var, update_var_def]
QED

Theorem exec_alloca_frame[local]:
  !inst s n s1 p.
    inst.inst_outputs = [p] /\ exec_alloca inst s n = OK s1 ==>
    s1.vs_current_bb = s.vs_current_bb /\ s1.vs_inst_idx = s.vs_inst_idx /\
    s1.vs_halted = s.vs_halted /\
    (!x. x <> p ==> lookup_var x s1 = lookup_var x s) /\
    (!a b. FLOOKUP s.vs_allocas a = SOME b ==>
           FLOOKUP s1.vs_allocas a = SOME b)
Proof
  rpt gen_tac >> simp[exec_alloca_def] >> BasicProvers.every_case_tac >>
  rw[] >> fs[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >> rw[] >>
  fs[FLOOKUP_DEF] >> metis_tac[]
QED

Theorem eval_operand_jump_to_frame[local]:
  !op s s' l v.
    eval_operand op s = SOME v /\ (!l. op <> Label l) /\
    (!x. op = Var x ==> lookup_var x s' = lookup_var x s) ==>
    eval_operand op (jump_to l s') = SOME v
Proof
  Cases >> simp[eval_operand_def, lookup_var_def, jump_to_def]
QED

Theorem step_ASSIGN_op[local]:
  !op v id out s.
    eval_operand op s = SOME v ==>
    step_inst_base (mk_inst id ASSIGN [op] [out]) s = OK (update_var out v s)
Proof
  rw[step_inst_base_def, venomInstTheory.mk_inst_def]
QED

Theorem run_from_prefix_abort[local]:
  !ctx func s bb pre a t.
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    s.vs_inst_idx = 0 /\ isPREFIX pre bb.bb_instructions /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) pre /\
    run_inst_seq pre s = Abort a t ==>
    ?t'. run_from 0 ctx func s = Abort a t'
Proof
  rpt strip_tac >>
  qspecl_then [`pre`, `s`, `0`, `ctx`, `bb`] mp_tac exec_block_run_inst_seq >>
  simp[] >> strip_tac >> simp[run_from_def]
QED

Theorem run_from_prefix_ok[local]:
  !ctx func s bb pre t.
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    s.vs_inst_idx = 0 /\ isPREFIX pre bb.bb_instructions /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) pre /\
    run_inst_seq pre s = OK t ==>
    t.vs_current_bb = s.vs_current_bb /\
    !fuel. run_from fuel ctx func s =
           run_from fuel ctx func (t with vs_inst_idx := LENGTH pre)
Proof
  rpt gen_tac >> strip_tac >>
  `!fuel. t.vs_current_bb = s.vs_current_bb /\
          exec_block fuel ctx bb s =
          exec_block fuel ctx bb (t with vs_inst_idx := LENGTH pre)` by
    (gen_tac >>
     qspecl_then [`pre`, `s`, `fuel`, `ctx`, `bb`] mp_tac
       exec_block_run_inst_seq >>
     simp[]) >>
  simp[run_from_def]
QED

(* The entry block of a range loop with nonliteral ends, from its start with
   the ends' operands at a and b: start > end (cmp, signed or not) or more
   rounds than the bound reverts at its ASSERT; otherwise the run goes to the
   condition block with the counter cv at a and the end ev at a + (b - a),
   having written only the block's own outputs. *)
Theorem for_entry_checked_path:
  !ctx func ee lbl cond_lbl op1 op2 a b cmp cv rv g1 z1 g2 z2 ev bound i.
    lookup_block lbl func.fn_blocks =
      SOME <| bb_label := lbl;
              bb_instructions :=
                [mk_inst i ASSIGN [op1] [cv];
                 mk_inst (i + 1) SUB [op2; op1] [rv];
                 mk_inst (i + 2) cmp [op1; op2] [g1];
                 mk_inst (i + 3) ISZERO [Var g1] [z1];
                 mk_inst (i + 4) ASSERT [Var z1] [];
                 mk_inst (i + 5) GT [Var rv; Lit (n2w bound)] [g2];
                 mk_inst (i + 6) ISZERO [Var g2] [z2];
                 mk_inst (i + 7) ASSERT [Var z2] [];
                 mk_inst (i + 8) ADD [op1; Var rv] [ev];
                 mk_inst (i + 9) JMP [Label cond_lbl] []] |> /\
    MEM cmp [SGT; GT] /\
    ee.vs_current_bb = lbl /\ ee.vs_inst_idx = 0 /\ ~ee.vs_halted /\
    eval_operand op1 ee = SOME a /\ eval_operand op2 ee = SOME b /\
    ALL_DISTINCT [cv; rv; g1; z1; g2; z2; ev] /\
    (!x. op1 = Var x \/ op2 = Var x ==> ~MEM x [cv; rv; g1; z1; g2; z2; ev]) ==>
    (((if cmp = SGT then word_gt a b else w2n a > w2n b) \/
      w2n (b - a) > w2n (n2w bound : bytes32)) ==>
     ?t. gas_marked_path F ctx func ee 0 (Abort Revert_abort t)) /\
    (~(if cmp = SGT then word_gt a b else w2n a > w2n b) /\
     ~(w2n (b - a) > w2n (n2w bound : bytes32)) ==>
     ?vs. lookup_var cv (ee with vs_vars := vs) = SOME a /\
          lookup_var ev (ee with vs_vars := vs) = SOME (a + (b - a)) /\
          (!x. ~MEM x [cv; rv; g1; z1; g2; z2; ev] ==>
               lookup_var x (ee with vs_vars := vs) = lookup_var x ee) /\
          gas_marked_path F ctx func ee 0
            (OK (jump_to cond_lbl (ee with vs_vars := vs))))
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `bad1 = if cmp = SGT then word_gt a b else w2n a > w2n b` >>
  qmatch_goalsub_abbrev_tac `bad1 \/ bad2 ==> _` >>
  qabbrev_tac `bb = <| bb_label := lbl;
              bb_instructions :=
                [mk_inst i ASSIGN [op1] [cv];
                 mk_inst (i + 1) SUB [op2; op1] [rv];
                 mk_inst (i + 2) cmp [op1; op2] [g1];
                 mk_inst (i + 3) ISZERO [Var g1] [z1];
                 mk_inst (i + 4) ASSERT [Var z1] [];
                 mk_inst (i + 5) GT [Var rv; Lit (n2w bound)] [g2];
                 mk_inst (i + 6) ISZERO [Var g2] [z2];
                 mk_inst (i + 7) ASSERT [Var z2] [];
                 mk_inst (i + 8) ADD [op1; Var rv] [ev];
                 mk_inst (i + 9) JMP [Label cond_lbl] []] |>` >>
  qabbrev_tac `s1 = update_var cv a ee` >>
  qabbrev_tac `s2 = update_var rv (b - a) s1` >>
  qabbrev_tac `s3 = update_var g1 (bool_to_word bad1) s2` >>
  qabbrev_tac `s4 = update_var z1 (bool_to_word (bool_to_word bad1 = 0w)) s3` >>
  qabbrev_tac `s5 = update_var g2 (bool_to_word bad2) s4` >>
  qabbrev_tac `s6 = update_var z2 (bool_to_word (bool_to_word bad2 = 0w)) s5` >>
  qabbrev_tac `s7 = update_var ev (a + (b - a)) s6` >>
  `!x w s. MEM x [cv; rv; g1; z1; g2; z2; ev] ==>
           eval_operand op1 (update_var x w s) = eval_operand op1 s /\
           eval_operand op2 (update_var x w s) = eval_operand op2 s` by
    (rpt strip_tac >> irule eval_operand_update_other_op >> metis_tac[]) >>
  `!s. (s = s1 \/ s = s2 \/ s = s3 \/ s = s4 \/ s = s5 \/ s = s6) ==>
       eval_operand op1 s = SOME a /\ eval_operand op2 s = SOME b` by
    (rpt strip_tac >> first_x_assum SUBST1_TAC >>
     simp[Abbr `s6`, Abbr `s5`, Abbr `s4`, Abbr `s3`, Abbr `s2`,
          Abbr `s1`]) >>
  `eval_operand (Var rv) s2 = SOME (b - a) /\
   eval_operand (Var rv) s6 = SOME (b - a) /\
   eval_operand (Var g1) s3 = SOME (bool_to_word bad1) /\
   eval_operand (Var z1) s4 = SOME (bool_to_word (bool_to_word bad1 = 0w)) /\
   eval_operand (Var g2) s5 = SOME (bool_to_word bad2) /\
   eval_operand (Var z2) s6 = SOME (bool_to_word (bool_to_word bad2 = 0w))` by
    (gvs[markerTheory.Abbrev_def, ALL_DISTINCT, eval_operand_def,
         lookup_var_update_var]) >>
  suspend "steps"
QED

Resume for_entry_checked_path[steps]:
  `step_inst_base (mk_inst (i + 2) cmp [op1; op2] [g1]) s2 = OK s3` by
    (simp[Abbr `s3`, Abbr `bad1`] >> Cases_on `cmp = SGT`
     >- (gvs[] >> irule step_SGT >> metis_tac[]) >>
     gvs[] >> irule step_GT >> metis_tac[]) >>
  `step_inst_base (mk_inst i ASSIGN [op1] [cv]) ee = OK s1` by
    simp[Abbr `s1`, step_ASSIGN_op] >>
  `step_inst_base (mk_inst (i + 1) SUB [op2; op1] [rv]) s1 = OK s2` by
    (qunabbrev_tac `s2` >> irule step_SUB >> metis_tac[]) >>
  `step_inst_base (mk_inst (i + 3) ISZERO [Var g1] [z1]) s3 = OK s4` by
    (qunabbrev_tac `s4` >> irule step_ISZERO >> fs[]) >>
  `run_inst_seq (TAKE 4 bb.bb_instructions) ee = OK s4` by
    simp[Abbr `bb`, run_inst_seq_def] >>
  suspend "runs"
QED

Resume for_entry_checked_path[runs]:
  `lookup_block ee.vs_current_bb func.fn_blocks = SOME bb` by
    simp[Abbr `bb`] >>
  `!k. k <= 9 ==>
       isPREFIX (TAKE k bb.bb_instructions) bb.bb_instructions /\
       EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
         (TAKE k bb.bb_instructions)` by
    (rpt strip_tac
     >- (simp[IS_PREFIX_APPEND] >> qexists `DROP k bb.bb_instructions` >>
         simp[TAKE_DROP]) >>
     `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
        (TAKE 9 bb.bb_instructions)` by
       (simp[Abbr `bb`, venomInstTheory.mk_inst_def, is_terminator_def] >>
        gvs[is_terminator_def]) >>
     `TAKE k bb.bb_instructions = TAKE k (TAKE 9 bb.bb_instructions)` by
       (simp[TAKE_TAKE_MIN, arithmeticTheory.MIN_DEF] >> rw[] >>
        `k = 9` by decide_tac >> simp[]) >>
     pop_assum SUBST1_TAC >> irule EVERY_TAKE >> simp[]) >>
  Cases_on `bad1` >> simp[]
  >- suspend "first_abort" >>
  suspend "first_ok"
QED

Resume for_entry_checked_path[first_abort]:
  (`step_inst_base (mk_inst (i + 4) ASSERT [Var z1] []) s4 =
         Abort Revert_abort (revert_state (set_returndata [] s4))` by
        (irule step_ASSERT_revert >> gvs[bool_to_word_def]) >>
      `run_inst_seq (TAKE 5 bb.bb_instructions) ee =
         Abort Revert_abort (revert_state (set_returndata [] s4))` by
        (`TAKE 5 bb.bb_instructions =
            TAKE 4 bb.bb_instructions ++ [mk_inst (i + 4) ASSERT [Var z1] []]`
           by simp[Abbr `bb`] >>
         pop_assum SUBST1_TAC >>
         qpat_assum `run_inst_seq (TAKE 4 _) _ = _`
           (mp_tac o MATCH_MP run_inst_seq_append) >>
         simp[run_inst_seq_def]) >>
      drule_at (Pat `run_inst_seq _ _ = Abort _ _`) run_inst_seq_abort_zero_path >>
      disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >> simp[] >>
      impl_tac
      >- (simp[Abbr `bb`, mk_inst_def, is_terminator_def] >>
          gvs[is_terminator_def]) >>
      metis_tac[])
QED

Resume for_entry_checked_path[first_ok]:
  `step_inst_base (mk_inst (i + 4) ASSERT [Var z1] []) s4 = OK s4` by
    (irule step_ASSERT_ok >> gvs[bool_to_word_def]) >>
  `step_inst_base (mk_inst (i + 5) GT [Var rv; Lit (n2w bound)] [g2]) s4 =
     OK s5` by
    (qunabbrev_tac `s5` >> qunabbrev_tac `bad2` >> irule step_GT >>
     gvs[markerTheory.Abbrev_def, eval_operand_def, lookup_var_update_var,
         ALL_DISTINCT]) >>
  `step_inst_base (mk_inst (i + 6) ISZERO [Var g2] [z2]) s5 = OK s6` by
    (qunabbrev_tac `s6` >> irule step_ISZERO >> fs[]) >>
  `run_inst_seq (TAKE 7 bb.bb_instructions) ee = OK s6` by
    (`TAKE 7 bb.bb_instructions =
        TAKE 4 bb.bb_instructions ++
        [mk_inst (i + 4) ASSERT [Var z1] [];
         mk_inst (i + 5) GT [Var rv; Lit (n2w bound)] [g2];
         mk_inst (i + 6) ISZERO [Var g2] [z2]]` by simp[Abbr `bb`] >>
     pop_assum SUBST1_TAC >>
     qpat_assum `run_inst_seq (TAKE 4 _) _ = _`
       (mp_tac o MATCH_MP run_inst_seq_append) >>
     simp[run_inst_seq_def]) >>
  Cases_on `bad2` >> simp[]
  >- suspend "second_abort" >>
  suspend "second_ok"
QED

Resume for_entry_checked_path[second_abort]:
  (`step_inst_base (mk_inst (i + 7) ASSERT [Var z2] []) s6 =
         Abort Revert_abort (revert_state (set_returndata [] s6))` by
        (irule step_ASSERT_revert >> gvs[bool_to_word_def]) >>
      `run_inst_seq (TAKE 8 bb.bb_instructions) ee =
         Abort Revert_abort (revert_state (set_returndata [] s6))` by
        (`TAKE 8 bb.bb_instructions =
            TAKE 7 bb.bb_instructions ++ [mk_inst (i + 7) ASSERT [Var z2] []]`
           by simp[Abbr `bb`] >>
         pop_assum SUBST1_TAC >>
         qpat_assum `run_inst_seq (TAKE 7 _) _ = _`
           (mp_tac o MATCH_MP run_inst_seq_append) >>
         simp[run_inst_seq_def]) >>
      drule_at (Pat `run_inst_seq _ _ = Abort _ _`) run_inst_seq_abort_zero_path >>
      disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >> simp[] >>
      impl_tac
      >- (simp[Abbr `bb`, mk_inst_def, is_terminator_def] >>
          gvs[is_terminator_def]) >>
      metis_tac[])
QED

Resume for_entry_checked_path[second_ok]:
  `step_inst_base (mk_inst (i + 7) ASSERT [Var z2] []) s6 = OK s6` by
    (irule step_ASSERT_ok >> gvs[bool_to_word_def]) >>
  `step_inst_base (mk_inst (i + 8) ADD [op1; Var rv] [ev]) s6 = OK s7` by
    (simp[Abbr `s7`] >> irule step_ADD >> metis_tac[]) >>
  `run_inst_seq (TAKE 9 bb.bb_instructions) ee = OK s7` by
    (`TAKE 9 bb.bb_instructions =
        TAKE 7 bb.bb_instructions ++
        [mk_inst (i + 7) ASSERT [Var z2] [];
         mk_inst (i + 8) ADD [op1; Var rv] [ev]]` by simp[Abbr `bb`] >>
     pop_assum SUBST1_TAC >>
     qpat_assum `run_inst_seq (TAKE 7 _) _ = _`
       (mp_tac o MATCH_MP run_inst_seq_append) >>
     simp[run_inst_seq_def]) >>
  `LENGTH bb.bb_instructions = 10` by simp[Abbr `bb`] >>
  `gas_path ctx func ee 0 (OK (s7 with vs_inst_idx := 9))` by
    (drule_at (Pos last) tuple_run_inst_seq_gas_path >>
     disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
     impl_tac
     >- (simp[] >> first_x_assum (qspec_then `9` mp_tac) >> simp[]) >>
     simp[Abbr `bb`, mk_inst_def] >> gvs[]) >>
  `ee with vs_vars := s7.vs_vars = s7` by
    simp[Abbr `s7`, Abbr `s6`, Abbr `s5`, Abbr `s4`, Abbr `s3`, Abbr `s2`,
         Abbr `s1`, update_var_def, venom_state_component_equality] >>
  `~s7.vs_halted` by
    gvs[markerTheory.Abbrev_def, update_var_def] >>
  suspend "normal_finish"
QED

Resume for_entry_checked_path[normal_finish]:
  qexists_tac `s7.vs_vars` >> asm_rewrite_tac[] >>
  rpt conj_tac
  >- gvs[markerTheory.Abbrev_def, lookup_var_update_var, ALL_DISTINCT]
  >- gvs[markerTheory.Abbrev_def, lookup_var_update_var]
  >- (rpt strip_tac >>
      gvs[markerTheory.Abbrev_def, lookup_var_update_var]) >>
  rewrite_tac[gas_marked_path_def] >>
  `s7.vs_current_bb = lbl` by
    simp[Abbr `s7`, Abbr `s6`, Abbr `s5`, Abbr `s4`, Abbr `s3`,
         Abbr `s2`, Abbr `s1`, update_var_def] >>
  `gas_path_edge ctx func (s7 with vs_inst_idx := 9) 0
     (OK (jump_to cond_lbl s7))` by
    (rewrite_tac[gas_path_edge_def] >> simp[] >> qexists_tac `0` >>
     qexists_tac `mk_inst (i + 9) JMP [Label cond_lbl] []` >>
     simp[Abbr `bb`, get_instruction_def, mk_inst_def,
          step_inst_non_invoke, step_jmp_behavior, jump_to_def,
          gas_count_step_def, is_terminator_def] >>
     disj2_tac >> disj1_tac >> qexists_tac `cond_lbl` >> simp[]) >>
  `gas_path ctx func (s7 with vs_inst_idx := 9) 0
     (OK (jump_to cond_lbl s7))` by
    (drule (cj 2 gas_path_rules) >> disch_then (qspec_then `0` mp_tac) >>
     simp[] >> disch_then irule >> irule (cj 1 gas_path_rules) >>
     simp[jump_to_def]) >>
  drule_all gas_path_then >> simp[]
QED

Finalise for_entry_checked_path
Theorem for_entry_checked_block:
  !ctx func ee lbl cond_lbl op1 op2 a b cmp cv rv g1 z1 g2 z2 ev bound i.
    lookup_block lbl func.fn_blocks =
      SOME <| bb_label := lbl;
              bb_instructions :=
                [mk_inst i ASSIGN [op1] [cv];
                 mk_inst (i + 1) SUB [op2; op1] [rv];
                 mk_inst (i + 2) cmp [op1; op2] [g1];
                 mk_inst (i + 3) ISZERO [Var g1] [z1];
                 mk_inst (i + 4) ASSERT [Var z1] [];
                 mk_inst (i + 5) GT [Var rv; Lit (n2w bound)] [g2];
                 mk_inst (i + 6) ISZERO [Var g2] [z2];
                 mk_inst (i + 7) ASSERT [Var z2] [];
                 mk_inst (i + 8) ADD [op1; Var rv] [ev];
                 mk_inst (i + 9) JMP [Label cond_lbl] []] |> /\
    MEM cmp [SGT; GT] /\
    ee.vs_current_bb = lbl /\ ee.vs_inst_idx = 0 /\ ~ee.vs_halted /\
    eval_operand op1 ee = SOME a /\ eval_operand op2 ee = SOME b /\
    ALL_DISTINCT [cv; rv; g1; z1; g2; z2; ev] /\
    (!x. op1 = Var x \/ op2 = Var x ==> ~MEM x [cv; rv; g1; z1; g2; z2; ev]) ==>
    (((if cmp = SGT then word_gt a b else w2n a > w2n b) \/
      w2n (b - a) > w2n (n2w bound : bytes32)) ==>
     ?fuel t. run_from fuel ctx func ee = Abort Revert_abort t) /\
    (~(if cmp = SGT then word_gt a b else w2n a > w2n b) /\
     ~(w2n (b - a) > w2n (n2w bound : bytes32)) ==>
     ?vs. lookup_var cv (ee with vs_vars := vs) = SOME a /\
          lookup_var ev (ee with vs_vars := vs) = SOME (a + (b - a)) /\
          (!x. ~MEM x [cv; rv; g1; z1; g2; z2; ev] ==>
               lookup_var x (ee with vs_vars := vs) = lookup_var x ee) /\
          !fuel rr.
            run_from fuel ctx func (jump_to cond_lbl (ee with vs_vars := vs)) =
              rr /\ (!e. rr <> Error e) ==>
            ?fuel'. run_from fuel' ctx func ee = rr)
Proof
  rpt gen_tac >> strip_tac >> drule_all for_entry_checked_path >>
  disch_then (qspec_then `ctx` mp_tac) >>
  simp[gas_marked_path_def] >> strip_tac >> conj_tac
  >- (disch_tac >> first_x_assum drule >> strip_tac >>
      drule gas_path_exit >> simp[exit_result_def] >> metis_tac[]) >>
  strip_tac >>
  qpat_x_assum `~_ /\ ~_ ==> _` mp_tac >> simp[] >> strip_tac >>
  qexists_tac `vs` >> simp[] >>
  drule gas_path_normal >> simp[]
QED



(* ===== The code ===== *)

Theorem comp_bind_eq[local]:
  !m f st a st'. m st = (a, st') ==> comp_bind m f st = f a st'
Proof
  rw[comp_bind_def]
QED

(* The code compile_stmt emits for a range loop after its ends, when they
   are not both literals: the rounds are computed and the range checked. *)
Definition for_range_checked_code_def:
  for_range_checked_code cenv lctx ty id fty bound body start_op end_op =
    do body_cenv <- declare_local cenv id fty;
       emit_local_alloca body_cenv id;
       entry_lbl <- fresh_label "for_entry";
       cond_lbl <- fresh_label "for_cond";
       body_lbl <- fresh_label "for_body";
       incr_lbl <- fresh_label "for_incr";
       exit_lbl <- fresh_label "for_exit";
       emit_inst JMP [Label entry_lbl] [];
       new_block entry_lbl;
       counter_var <- fresh_var;
       emit_inst ASSIGN [start_op] [counter_var];
       rounds <- emit_op SUB [end_op; start_op];
       compile_range_bound_checks start_op end_op rounds bound
         (is_signed_type fty);
       end_val <- emit_op ADD [start_op; rounds];
       emit_inst JMP [Label cond_lbl] [];
       new_block cond_lbl;
       done_op <- emit_op EQ [Var counter_var; end_val];
       emit_inst JNZ [done_op; Label exit_lbl; Label body_lbl] [];
       new_block body_lbl;
       (case FLOOKUP body_cenv.ce_vars id of
          SOME (MemLoc offset _) =>
            emit_void MSTORE [Lit (n2w offset); Var counter_var]
        | SOME (PtrVar ptr_op _) =>
            emit_void MSTORE [ptr_op; Var counter_var]
        | _ => emit_void INVALID []);
       compile_stmts body_cenv (InLoop exit_lbl incr_lbl) ty body;
       emit_jmp_if_not_terminated incr_lbl;
       new_block incr_lbl;
       new_counter <- emit_op ADD [Var counter_var; Lit 1w];
       emit_inst ASSIGN [new_counter] [counter_var];
       emit_inst JMP [Label cond_lbl] [];
       new_block exit_lbl;
       return ()
    od
End

Theorem compile_stmt_for_range_checked:
  !cenv lctx ty id fty e1 e2 bound body st op1 s1 op2 s2.
    lower_value compile_expr cenv fty e1 st = (op1, s1) /\
    lower_value compile_expr cenv fty e2 s1 = (op2, s2) /\
    ~(?a1 n1 a2 n2. e1 = Literal a1 (IntL n1) /\ e2 = Literal a2 (IntL n2)) ==>
    compile_stmt cenv lctx ty (For id fty (Range e1 e2) bound body) st =
    for_range_checked_code cenv lctx ty id fty bound body op1 op2 s2
Proof
  rpt strip_tac >>
  simp[Once compile_stmt_def, LET_THM] >>
  qpat_assum `lower_value _ _ _ e1 _ = _`
    (fn th => simp[MATCH_MP comp_bind_eq th]) >>
  qpat_assum `lower_value _ _ _ e2 _ = _`
    (fn th => simp[MATCH_MP comp_bind_eq th]) >>
  simp[for_range_checked_code_def] >>
  Cases_on `e1` >> gvs[] >>
  rename1 `Literal a lit` >> Cases_on `lit` >> gvs[] >>
  Cases_on `e2` >> gvs[] >>
  rename1 `Literal a' lit'` >> Cases_on `lit'` >> gvs[]
QED

Theorem emit_op_if[local]:
  !b o1 o2 ops. (if b then emit_op o1 ops else emit_op o2 ops) =
                emit_op (if b then o1 else o2) ops
Proof
  rw[]
QED

(* The code of a range loop after its ends, which are not both literals,
   its locals held through pointers: the loop variable's ALLOCA ending the
   block it starts in, the entry block (the counter, the rounds, the range
   checks and the end), the condition block, the body block (the counter
   stored into the loop variable, then the body), the increment block, and
   the exit block, where the code ends. *)
Theorem for_range_checked_parts:
  !cenv lctx ty id fty bound stmts op1 op2 s0 st st' func.
    for_range_checked_code cenv lctx ty id fty bound stmts op1 op2 st =
      ((), st') /\
    cenv.ce_alloca_locals /\ fn_has_code s0 st' func /\ cs_extends s0 st /\
    (!c lc sa sb. compile_stmts c lc ty stmts sa = ((), sb) ==>
                  cs_extends sa sb) ==>
    ?p cv rv g1 z1 g2 z2 ev dv entry_lbl cond_lbl body_lbl incr_lbl exit_lbl
     bc sb0 sb1 sj nv.
      p = STRING #"%" (toString st.cs_next_var) /\
      cv = STRING #"%" (toString (st.cs_next_var + 1)) /\
      rv = STRING #"%" (toString (st.cs_next_var + 2)) /\
      g1 = STRING #"%" (toString (st.cs_next_var + 3)) /\
      z1 = STRING #"%" (toString (st.cs_next_var + 4)) /\
      g2 = STRING #"%" (toString (st.cs_next_var + 5)) /\
      z2 = STRING #"%" (toString (st.cs_next_var + 6)) /\
      ev = STRING #"%" (toString (st.cs_next_var + 7)) /\
      dv = STRING #"%" (toString (st.cs_next_var + 8)) /\
      entry_lbl = fresh_label_output "for_entry" st.cs_next_label /\
      cond_lbl = fresh_label_output "for_cond" (st.cs_next_label + 1) /\
      body_lbl = fresh_label_output "for_body" (st.cs_next_label + 2) /\
      incr_lbl = fresh_label_output "for_incr" (st.cs_next_label + 3) /\
      exit_lbl = fresh_label_output "for_exit" (st.cs_next_label + 4) /\
      declare_local cenv id fty st =
        (bc, st with cs_next_var := st.cs_next_var + 1) /\
      sb0.cs_current_bb = body_lbl /\
      sb0.cs_current_insts =
        [mk_inst (st.cs_next_id + 14) MSTORE [Var p; Var cv] []] /\
      sb0.cs_next_var = st.cs_next_var + 9 /\ cs_extends st sb0 /\
      st.cs_next_id <= sb0.cs_next_id /\
      compile_stmts bc (InLoop exit_lbl incr_lbl) ty stmts sb0 = ((), sb1) /\
      fn_has_code sb0 sb1 func /\
      lookup_block st.cs_current_bb func.fn_blocks =
        SOME <| bb_label := st.cs_current_bb;
                bb_instructions :=
                  st.cs_current_insts ++
                  [mk_inst st.cs_next_id ALLOCA
                     [Lit (n2w (type_memory_bytes cenv fty))] [p];
                   mk_inst (st.cs_next_id + 1) JMP [Label entry_lbl] []] |> /\
      lookup_block entry_lbl func.fn_blocks =
        SOME <| bb_label := entry_lbl;
                bb_instructions :=
                  [mk_inst (st.cs_next_id + 2) ASSIGN [op1] [cv];
                   mk_inst (st.cs_next_id + 3) SUB [op2; op1] [rv];
                   mk_inst (st.cs_next_id + 4)
                     (if is_signed_type fty then SGT else GT) [op1; op2] [g1];
                   mk_inst (st.cs_next_id + 5) ISZERO [Var g1] [z1];
                   mk_inst (st.cs_next_id + 6) ASSERT [Var z1] [];
                   mk_inst (st.cs_next_id + 7) GT [Var rv; Lit (n2w bound)] [g2];
                   mk_inst (st.cs_next_id + 8) ISZERO [Var g2] [z2];
                   mk_inst (st.cs_next_id + 9) ASSERT [Var z2] [];
                   mk_inst (st.cs_next_id + 10) ADD [op1; Var rv] [ev];
                   mk_inst (st.cs_next_id + 11) JMP [Label cond_lbl] []] |> /\
      lookup_block cond_lbl func.fn_blocks =
        SOME <| bb_label := cond_lbl;
                bb_instructions :=
                  [mk_inst (st.cs_next_id + 12) EQ [Var cv; Var ev] [dv];
                   mk_inst (st.cs_next_id + 13) JNZ
                     [Var dv; Label exit_lbl; Label body_lbl] []] |> /\
      (?bbb. lookup_block body_lbl func.fn_blocks = SOME bbb /\
             get_instruction bbb 0 =
               SOME (mk_inst (st.cs_next_id + 14) MSTORE [Var p; Var cv] [])) /\
      (~block_is_terminated sb1 ==>
       sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
       sj.cs_current_insts =
         sb1.cs_current_insts ++
         [mk_inst sb1.cs_next_id JMP [Label incr_lbl] []] /\
       fn_has_code sb1 sj func) /\
      sj.cs_next_var = sb1.cs_next_var /\
      nv = STRING #"%" (toString sj.cs_next_var) /\
      lookup_block incr_lbl func.fn_blocks =
        SOME <| bb_label := incr_lbl;
                bb_instructions :=
                  [mk_inst sj.cs_next_id ADD [Var cv; Lit 1w] [nv];
                   mk_inst (sj.cs_next_id + 1) ASSIGN [Var nv] [cv];
                   mk_inst (sj.cs_next_id + 2) JMP [Label cond_lbl] []] |> /\
      st'.cs_current_bb = exit_lbl /\ st'.cs_current_insts = [] /\
      cs_extends st st'
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `for_range_checked_code _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[for_range_checked_code_def, compile_range_bound_checks_def,
       emit_op_if, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       LET_THM] >>
  Cases_on `declare_local cenv id fty st` >> rename1 `_ = (bc, st1)` >>
  drule_all declare_local_ptr >> strip_tac >> gvs[] >>
  simp[emit_local_alloca_def, fresh_label_def, emit_inst_def, emit_op_def,
       emit_void_def, fresh_id_def, emit_def, new_block_def, fresh_var_def,
       emit_jmp_if_not_terminated_def, comp_get_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  rename1 `compile_stmts bc _ ty stmts _ = ((), sb1)` >>
  qpat_x_assum `(if block_is_terminated sb1 then _ else _) _ = _`
    (assume_tac o SIMP_RULE (srw_ss()) [comp_bind_def, comp_return_def,
                                         fresh_id_def, emit_def, LET_THM]) >>
  rename1 `_ = ((), sj)` >>
  qmatch_asmsub_abbrev_tac `compile_stmts bc _ ty stmts sb0 = _` >>
  strip_tac >> qexistsl_tac [`sb0`, `sb1`, `sj`] >>
  `cs_extends sb0 sb1` by metis_tac[] >>
  `cs_extends st sb0` by
    (simp[cs_extends_def, Abbr `sb0`] >> qexists_tac `[_; _; _]` >> simp[]) >>
  `sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
   sj.cs_next_var = sb1.cs_next_var /\ cs_extends sb1 sj /\
   (~block_is_terminated sb1 ==>
    sj.cs_current_insts =
      sb1.cs_current_insts ++
      [mk_inst sb1.cs_next_id JMP
         [Label (fresh_label_output "for_incr" (st.cs_next_label + 3))] []])` by
    (Cases_on `block_is_terminated sb1` >>
     fs[comp_return_def, comp_bind_def, fresh_id_def, emit_def, LET_THM] >>
     gvs[cs_extends_refl] >>
     irule cs_extends_same_block >> simp[]) >>
  `cs_extends sj st'` by
    (qpat_x_assum `_ = st'` (SUBST_ALL_TAC o SYM) >> simp[cs_extends_def] >>
     qexists_tac `[_; <| bb_label := sj.cs_current_bb;
                         bb_instructions := sj.cs_current_insts |>]` >>
     simp[]) >>
  `cs_extends st st'` by metis_tac[cs_extends_trans] >>
  `fn_has_code st st' func` by metis_tac[fn_has_code_split] >>
  `?nb. sb1.cs_blocks = nb ++ sb0.cs_blocks` by
    (qpat_x_assum `cs_extends sb0 sb1` mp_tac >> simp[cs_extends_def] >>
     metis_tac[]) >>
  `!l b. MEM b (emitted_blocks st st') /\ b.bb_label = l ==>
         lookup_block l func.fn_blocks = SOME b` by
    (fs[fn_has_code_def] >> metis_tac[]) >>
  `emitted_blocks st st' =
   [HD st'.cs_blocks; HD (TL st'.cs_blocks)] ++ nb ++
   [HD sb0.cs_blocks; HD (TL sb0.cs_blocks); HD (TL (TL sb0.cs_blocks))]` by
    (irule emitted_blocks_append >>
     qpat_x_assum `_ = st'` (SUBST_ALL_TAC o SYM) >> simp[Abbr `sb0`]) >>
  `cs_extends sb1 st' /\ cs_extends sb0 st'` by
    metis_tac[cs_extends_trans] >>
  `fn_has_code sb0 sb1 func /\ fn_has_code sb1 sj func` by
    metis_tac[fn_has_code_mid, cs_extends_trans] >>
  `?bbb. lookup_block sb0.cs_current_bb func.fn_blocks = SOME bbb /\
         isPREFIX sb0.cs_current_insts bbb.bb_instructions` by
    metis_tac[fn_has_code_start] >>
  qpat_x_assum `_ = st'` (assume_tac o SYM) >> rpt conj_tac
  >- simp[Abbr `sb0`]
  >- simp[Abbr `sb0`]
  >- simp[Abbr `sb0`]
  >- first_assum ACCEPT_TAC
  >- simp[Abbr `sb0`]
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- (qpat_assum `!l b. MEM b _ /\ _ ==> _` irule >>
      conj_tac >- simp_tac (srw_ss()) [] >>
      qpat_assum `emitted_blocks _ _ = _` (fn th => REWRITE_TAC [th]) >>
      REWRITE_TAC [MEM_APPEND, MEM] >> disj2_tac >> disj2_tac >> disj2_tac >>
      qunabbrev_tac `sb0` >> simp_tac (srw_ss()) [])
  >- (qpat_assum `!l b. MEM b _ /\ _ ==> _` irule >>
      conj_tac >- simp_tac (srw_ss()) [] >>
      qpat_assum `emitted_blocks _ _ = _` (fn th => REWRITE_TAC [th]) >>
      REWRITE_TAC [MEM_APPEND, MEM] >> disj2_tac >> disj2_tac >> disj1_tac >>
      qunabbrev_tac `sb0` >> simp_tac (srw_ss()) [])
  >- (qpat_assum `!l b. MEM b _ /\ _ ==> _` irule >>
      conj_tac >- simp_tac (srw_ss()) [] >>
      qpat_assum `emitted_blocks _ _ = _` (fn th => REWRITE_TAC [th]) >>
      REWRITE_TAC [MEM_APPEND, MEM] >> disj2_tac >> disj1_tac >>
      qunabbrev_tac `sb0` >> simp_tac (srw_ss()) [])
  >- (qexists_tac `bbb` >>
      qpat_x_assum `lookup_block sb0.cs_current_bb _ = _` mp_tac >>
      qpat_x_assum `isPREFIX sb0.cs_current_insts _` mp_tac >>
      qunabbrev_tac `sb0` >> simp_tac (srw_ss()) [] >> rpt strip_tac >>
      Cases_on `bbb.bb_instructions` >> fs[get_instruction_def])
  >- (strip_tac >>
      qpat_x_assum `~block_is_terminated sb1 ==> _` drule >> strip_tac >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  >- first_assum ACCEPT_TAC
  >- (qpat_assum `!l b. MEM b _ /\ _ ==> _` irule >>
      conj_tac >- simp_tac (srw_ss()) [] >>
      qpat_assum `emitted_blocks _ _ = _` (fn th => REWRITE_TAC [th]) >>
      REWRITE_TAC [MEM_APPEND, MEM] >> disj1_tac >> disj1_tac >> disj1_tac >>
      qpat_assum `st' = _` (fn th => REWRITE_TAC [th]) >>
      simp_tac (srw_ss()) [])
  >- (qpat_assum `st' = _` (fn th => REWRITE_TAC [th]) >>
      simp_tac (srw_ss()) [])
  >- (qpat_assum `st' = _` (fn th => REWRITE_TAC [th]) >>
      simp_tac (srw_ss()) []) >>
  first_assum ACCEPT_TAC
QED

(* ===== For over a range with nonliteral ends ===== *)

(* Keep the checked-range proof independent of the literal-range theory. *)
Theorem reserved_fresh_not_local[local]:
  !cenv st n scs.
    local_ptrs_reserved cenv st /\ st.cs_next_var <= n ==>
    not_local_ptr cenv scs (STRING #"%" (toString n))
Proof
  metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_fresh]
QED

(* The operand-shape boundary used here does not need operator simulation. *)
Theorem lower_value_word_shape[local]:
  !cenv env ty e sa op sb.
    lower_value compile_expr cenv ty e sa = (op, sb) /\
    well_typed_expr env e /\
    (!id t. FLOOKUP env.var_types id = SOME t ==>
            well_formed_type env.type_defs t) /\
    is_word_type (expr_type e) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    (!z. op = Var z ==> not_fresh_at sb z) /\ (!l. op <> Label l)
Proof
  rpt gen_tac >> strip_tac >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  drule lower_value_word_safe_operand >>
  disch_then (qspec_then `env` mp_tac) >>
  disch_then drule_all >> simp[exprSafeOperandTheory.safe_operand_def]
QED

Theorem is_int_type_memory_size[local]:
  !tenv t tv. is_int_type t /\ evaluate_type tenv t = SOME tv ==>
              type_memory_size tv = 32
Proof
  rw[is_int_type_cases] >>
  gvs[evaluate_type_def, AllCaseEqs(), type_memory_size_def]
QED

Theorem value_has_type_int_between[local]:
  !tyv i1 i2 i.
    value_has_type tyv (IntV i1) /\ value_has_type tyv (IntV i2) /\
    i1 <= i /\ i <= i2 ==>
    value_has_type tyv (IntV i)
Proof
  Cases >> simp[value_has_type_def] >> rename1 `BaseTV bt` >>
  Cases_on `bt` >> simp[value_has_type_def, within_int_bound_def] >>
  rw[] >> intLib.ARITH_TAC
QED

Theorem range_value_has_type:
  !tyv n1 n2.
    value_has_type tyv (IntV n1) /\ value_has_type tyv (IntV n2) /\
    n1 <= n2 ==>
    !j. j < Num (n2 - n1) ==> value_has_type tyv (IntV (n1 + &j))
Proof
  rpt strip_tac >>
  qspecl_then [`tyv`, `n1`, `n2`, `n1 + &j`] mp_tac
    value_has_type_int_between >>
  impl_tac >- (simp[] >> intLib.ARITH_TAC) >> simp[]
QED

(* The exit of an expression's fragment is the statement's, where the
   statement raises what the expression does. *)
Theorem expr_exit_stmt_exit[local]:
  !r1 res RetQ es' rr.
    expr_exit (r1 : value + exception) rr /\
    (!ex. r1 = INR ex ==> res = INR ex) ==>
    stmt_exit RetQ es' res rr
Proof
  Cases_on `r1` >> simp[] >> rpt strip_tac >> gvs[stmt_exit_def] >>
  disj1_tac >>
  ONCE_REWRITE_TAC [INST_TYPE [beta |-> ``:value``]
                      expr_exit_INR_type] >>
  first_assum ACCEPT_TAC
QED

Theorem range_expr_val_rel_int_operand[local]:
  expr_val_rel cx t (IntV n) op s /\ is_word_type t /\
  evaluate_type (get_tenv cx) t = SOME tv ==>
  eval_operand op s = SOME (i2w n)
Proof
  rw[expr_val_rel_def] >>
  first_x_assum (qspec_then `tv` mp_tac) >>
  simp[typed_val_to_w256_word_value, word_value_def, val_to_w256_def]
QED

Theorem range_expr_post_int_operand[local]:
  expr_post ctx func cenv cx e es sa sb s0 es' (IntV n) op s /\
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
  eval_operand op s = SOME (i2w n)
Proof
  rw[expr_post_def] >> gvs[] >> drule_all range_expr_val_rel_int_operand >> simp[]
QED

Theorem forced_endpoint_bind_outcome[local]:
  expr_sim ctx func cenv cx fty e es /\
  lower_value compile_expr cenv fty e sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  gas_admissible (bind (bind (eval_expr cx e) (read_result cx)) next)
    (stmt_res_ok lctx) es /\
  (!marks v mid t.
    gas_marked_exec F (ctx,func) (bind (eval_expr cx e) (read_result cx))
      (es,s0) marks (INL v) mid (OK t) /\
    expr_post ctx func cenv cx e es sa sb s0 mid v op t /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    gas_admissible (next v) (stmt_res_ok lctx) (mid with gas_obs := []) ==>
    gas_outcome F (cx_tops cx) (ctx,func) (next v)
      (mid with gas_obs := [],t) Post
      (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (bind (eval_expr cx e) (read_result cx)) next) (es,s0) Post
    (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  strip_tac >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (irule forced_endpoint_admissible >> goal_assum (drule_at Any)) >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_def] >>
  disch_then (qspecl_then [`sa`, `sb`, `op`, `s0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >> strip_tac
  >- suspend "normal"
  >- suspend "exception" >>
  qexists_tac `marks` >> disj2_tac >>
  irule_at Any forced_endpoint_error_cert >> goal_assum (drule_at Any)
QED

Resume forced_endpoint_bind_outcome[normal]:
  gvs[] >>
  `gas_admissible (next v) (stmt_res_ok lctx) (es_end with gas_obs := [])` by
    (irule gas_admissible_bind_tail >> goal_assum (drule_at Any) >>
     qexists_tac `gas_explicit marks s0.vs_gas_readings` >>
     fs[gas_marked_exec_def]) >>
  `gas_marked_exec F (ctx,func) (bind (eval_expr cx e) (read_result cx))
     (es,s0) marks (INL v) (es_end with gas_obs := []) (OK t)` by
    fs[gas_marked_exec_def] >>
  qpat_x_assum `!marks v mid t. _` drule_all >>
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >> strip_tac
  >- suspend "bind_finish"
  >- suspend "bind_finish" >>
  qexists_tac `marks ++ marks'` >> disj2_tac >>
  irule_at Any forced_endpoint_tail_cert >> goal_assum (drule_at Any) >> simp[]
QED

Resume forced_endpoint_bind_outcome[exception]:
  gvs[] >> Cases_on `res` >- fs[] >>
  rename1 `INR ex` >> qexists_tac `marks` >> disj1_tac >>
  qexistsl_tac [`INR ex`, `es_end`, `r`] >>
  conj_tac
  >- (irule gas_marked_exec_bind_exception >> simp[]) >>
  disj2_tac >> simp[] >> gen_tac >>
  irule expr_exit_stmt_exit >> qexists_tac `INR ex` >> simp[]
QED

Resume forced_endpoint_bind_outcome[bind_finish]:
  markerLib.RESUME_TAC >>
  (qexists_tac `marks ++ marks'` >> disj1_tac >>
   qexistsl_tac [`res`, `es_end'`, `r`] >>
   conj_tac
   >- (irule gas_marked_exec_bind_normal >> goal_assum (drule_at Any) >> simp[]) >>
   gvs[])
QED

Finalise forced_endpoint_bind_outcome

Theorem for_range_checked_tail_outcome[local]:
  for_range_checked_code cenv lctx ty id fty bound stmts op1 op2 st =
    ((), sf) /\
  fn_has_code st sf func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv st /\ ret_pc_ok cenv st t0 /\
  t0.vs_current_bb = st.cs_current_bb /\
  t0.vs_inst_idx = LENGTH st.cs_current_insts /\ ~t0.vs_halted /\
  stmt_state_rel ctx func cenv cx es t0 /\
  is_int_type fty /\ evaluate_type (get_tenv cx) fty = SOME tyv /\
  32 <= type_memory_bytes cenv fty /\
  type_memory_bytes cenv fty < dimword (:256) /\
  bound < dimword (:256) /\ cenv.ce_alloca_locals /\
  lookup_scopes id es.scopes = NONE /\
  (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
  (!c lc sa sb. compile_stmts c lc ty stmts sa = ((), sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
  eval_operand op1 t0 = SOME (i2w n1) /\
  eval_operand op2 t0 = SOME (i2w n2) /\
  (!l. op1 <> Label l /\ op2 <> Label l) /\
  (!x. op1 = Var x \/ op2 = Var x ==> not_fresh_at st x) /\
  value_has_type tyv (IntV n1) /\ value_has_type tyv (IntV n2) /\
  P (es with gas_obs := []) /\
  (!c st1 ex inc ei j.
     declare_local cenv id fty st = (c, st1) /\
     n1 <= n2 /\ Num (n2 - n1) <= bound /\
     P ei /\ lookup_scopes id ei.scopes = NONE /\
     j < Num (n2 - n1) ==>
     stmt_frag ctx func cx (InLoop ex inc) RetQ c
       (stmts_env c (InLoop ex inc) ty stmts) (eval_stmts cx stmts)
       (ei with scopes :=
         (FEMPTY |+ (id, <| assignable := F; type := tyv;
            value := IntV (n1 + &j); popped := [] |>)) :: ei.scopes)) /\
  (!ei j gs r2 es2 sc rest.
     n1 <= n2 /\ Num (n2 - n1) <= bound /\
     P ei /\ lookup_scopes id ei.scopes = NONE /\
     j < Num (n2 - n1) /\
     eval_stmts cx stmts
       (ei with <| scopes :=
         (FEMPTY |+ (id, <| assignable := F; type := tyv;
            value := IntV (n1 + &j); popped := [] |>)) :: ei.scopes;
         gas_obs := gs |>) = (r2, es2) /\
     (r2 = INL () \/ r2 = INR ContinueException) /\
     es2.scopes = sc :: rest ==> P (es2 with scopes := rest)) /\
  gas_admissible
    (do rl <- lift_sum (get_range_limits (IntV n1) (IntV n2));
        check (compatible_bound (Dynamic bound) (SND rl)) "For too long";
        eval_for cx tyv id stmts
          (GENLIST (\j. IntV (FST rl + &j)) (SND rl)) od)
    (stmt_res_ok lctx) es ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (do rl <- lift_sum (get_range_limits (IntV n1) (IntV n2));
        check (compatible_bound (Dynamic bound) (SND rl)) "For too long";
        eval_for cx tyv id stmts
          (GENLIST (\j. IntV (FST rl + &j)) (SND rl)) od)
    (es,t0)
    (stmt_post ctx func cx lctx cenv cenv st sf es t0)
    (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  strip_tac >>
  `cs_extends st st` by simp[cs_extends_refl] >>
  drule_at (Pat `for_range_checked_code _ _ _ _ _ _ _ _ _ _ = _`)
    for_range_checked_parts >>
  disch_then (qspecl_then [`st`, `func`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  disch_then (qx_choosel_then
    [`p`, `cv`, `rv`, `g1`, `z1`, `g2`, `z2`, `ev`, `dv`, `entry_lbl`,
     `cond_lbl`, `body_lbl`, `incr_lbl`, `exit_lbl`, `bc`, `sb0`, `sb1`,
     `sj`, `nv`] strip_assume_tac) >>
  suspend "allocation"
QED

Resume for_range_checked_tail_outcome[allocation]:
  qabbrev_tac `sz = type_memory_bytes cenv fty` >>
  qabbrev_tac `A = mk_inst st.cs_next_id ALLOCA [Lit (n2w sz)] [p]` >>
  `MEM A (fn_insts func)` by
    (qpat_assum `lookup_block st.cs_current_bb _ = _`
       (mp_tac o MATCH_MP
          (REWRITE_RULE [GSYM AND_IMP_INTRO] lookup_block_fn_insts)) >>
     disch_then irule >> simp[Abbr `A`]) >>
  `not_local_ptr cenv es.scopes p` by
    (qpat_assum `p = _` SUBST1_TAC >> irule reserved_fresh_not_local >>
     qexists_tac `st` >> simp[]) >>
  `A.inst_opcode = ALLOCA /\ A.inst_operands = [Lit (n2w sz)] /\
   A.inst_outputs = [p] /\ A.inst_id = st.cs_next_id` by
    simp[Abbr `A`, mk_inst_def] >>
  `?sA. exec_alloca A t0 (n2w sz : bytes32) = OK sA` by
    (Cases_on `FLOOKUP t0.vs_allocas A.inst_id`
     >- simp[exec_alloca_def] >>
     rename1 `_ = SOME entry` >> PairCases_on `entry` >> simp[exec_alloca_def]) >>
  `step_inst_base A t0 = exec_alloca A t0 (n2w sz : bytes32)` by
    simp[step_inst_base_def, eval_operand_def] >>
  `step_inst_base A t0 = OK sA` by simp[] >>
  drule_all stmt_state_rel_exec_alloca >> strip_tac >>
  drule_all exec_alloca_frame >> strip_tac >>
  `w2n (n2w sz : bytes32) = sz` by simp[Abbr `sz`] >>
  `gas_marked_path F ctx func t0 0 (OK (jump_to entry_lbl sA))` by
    (irule for_start_zero_path >> simp[] >>
     qexists_tac `st.cs_next_id + 1` >> simp[]) >>
  suspend "checked_entry"
QED

Resume for_range_checked_tail_outcome[checked_entry]:
  `!k. ~not_fresh_at st (STRING #"%" (toString (st.cs_next_var + k)))` by
    (rw[not_fresh_at_def] >> qexists_tac `st.cs_next_var + k` >> simp[]) >>
  `!x. op1 = Var x \/ op2 = Var x ==>
       x <> p /\ ~MEM x [cv; rv; g1; z1; g2; z2; ev]` by
    (rpt gen_tac >> strip_tac >>
     `not_fresh_at st x` by metis_tac[] >>
     fs[not_fresh_at_def] >> rw[] >> first_x_assum irule >> simp[]) >>
  `eval_operand op1 (jump_to entry_lbl sA) = SOME (i2w n1) /\
   eval_operand op2 (jump_to entry_lbl sA) = SOME (i2w n2)` by
    (conj_tac >> irule eval_operand_jump_to_frame >>
     simp[] >> metis_tac[]) >>
  drule_at (Pat `lookup_block _ _ = _`)
    (for_entry_checked_path |> SPEC_ALL |>
     Q.INST [`i` |-> `st.cs_next_id + 2`] |> SRULE [GSYM arithmeticTheory.ADD_ASSOC]) >>
  disch_then (qspecl_then [`jump_to entry_lbl sA`, `ctx`, `i2w n2`, `i2w n1`] mp_tac) >>
  (impl_tac >-
    (simp[jump_to_def, ASCIInumbersTheory.toString_inj] >>
     Cases_on `is_signed_type fty` >> simp[] >>
     gen_tac >> disch_tac >>
     qpat_x_assum `!x. op1 = Var x \/ op2 = Var x ==> x <> p /\ _`
       (qspec_then `x` mp_tac) >>
     qpat_x_assum `op1 = Var x \/ op2 = Var x` (fn th => REWRITE_TAC [th]) >>
     rpt (qpat_x_assum `_ = STRING #"%" (toString _)` SUBST1_TAC) >>
     simp[])) >>
  strip_tac >>
  suspend "checked_tests"
QED

Resume for_range_checked_tail_outcome[checked_tests]:
  qspecl_then [`get_tenv cx`, `fty`, `tyv`, `n1`, `n2`] mp_tac range_end_words >>
  (impl_tac >- simp[]) >> strip_tac >>
  `((if (if is_signed_type fty then SGT else GT) = SGT
       then word_gt (i2w n1 : bytes32) (i2w n2)
       else w2n (i2w n1 : bytes32) > w2n (i2w n2 : bytes32)) <=> n2 < n1)` by
    (qpat_x_assum `(if is_signed_type fty then _ else _) <=> _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Cases_on `is_signed_type fty` >> simp[]) >>
  fs[] >>
  Cases_on `n1 <= n2`
  >- suspend "valid_order" >>
  suspend "bad_order"
QED

Resume for_range_checked_tail_outcome[valid_order]:
  fs[checked_range_tail] >>
  Cases_on `Num (n2 - n1) <= bound`
  >- suspend "loop_setup" >>
  suspend "bad_bound"
QED

Resume for_range_checked_tail_outcome[loop_setup]:
  fs[] >>
  qpat_x_assum `~(_ < _) /\ ~(_ > _) ==> _` mp_tac >>
  simp[integerTheory.INT_NOT_LT] >>
  disch_then (qx_choose_then `vs` strip_assume_tac) >>
  suspend "loop_state"
QED

Resume for_range_checked_tail_outcome[loop_state]:
  qabbrev_tac `cc = jump_to cond_lbl (jump_to entry_lbl sA with vs_vars := vs)` >>
  `!q. not_fresh_at st q ==> ~MEM q [cv; rv; g1; z1; g2; z2; ev] /\ q <> p` by
    (rpt strip_tac >> fs[not_fresh_at_def] >> rw[] >>
     first_x_assum irule >> simp[]) >>
  `!x. ~MEM x [cv; rv; g1; z1; g2; z2; ev] ==>
       lookup_var x cc = lookup_var x sA` by
    (gen_tac >> strip_tac >> simp[Abbr `cc`] >>
     qpat_x_assum `!x. _ ==> lookup_var x (_ with vs_vars := vs) = _`
       (qspec_then `x` mp_tac) >>
     gvs[lookup_var_def, jump_to_def]) >>
  `!q. not_fresh_at st q ==> FLOOKUP vs q = FLOOKUP sA.vs_vars q` by
    (rpt strip_tac >>
     `~MEM q [cv; rv; g1; z1; g2; z2; ev]` by metis_tac[] >>
     qpat_assum `!x. ~MEM x _ ==> lookup_var x cc = _`
       (qspec_then `q` mp_tac) >>
     (impl_tac >- simp[]) >> disch_tac >>
     gvs[Abbr `cc`, lookup_var_def, jump_to_def]) >>
  `stmt_state_rel ctx func cenv cx es (sA with vs_vars := vs)` by
    (irule stmt_state_rel_vars_frame >> simp[] >> conj_tac
     >- (rpt strip_tac >> simp[lookup_var_def] >>
         first_x_assum irule >>
         qpat_assum `local_ptrs_reserved cenv st`
           (mp_tac o CONJUNCT1 o CONJUNCT2 o PURE_REWRITE_RULE [local_ptrs_reserved_def]) >>
         disch_then (qspecl_then [`name`, `name`, `p'`, `sz'`, `sz'`] mp_tac) >>
         simp[]) >>
     rpt strip_tac >> simp[lookup_var_def] >>
     first_x_assum irule >> metis_tac[local_ptrs_reserved_imm_base]) >>
  `cc = jump_to cond_lbl (jump_to entry_lbl (sA with vs_vars := vs))` by
    simp[Abbr `cc`, jump_to_def] >>
  `stmt_state_rel ctx func cenv cx es cc` by
    metis_tac[stmt_state_rel_jump_to] >>
  suspend "loop_parameters"
QED

Resume for_range_checked_tail_outcome[loop_parameters]:
  `!x v. not_fresh_at st x /\ lookup_var x t0 = SOME v ==>
         lookup_var x cc = SOME v` by
    (rpt strip_tac >> `x <> p /\ ~MEM x [cv; rv; g1; z1; g2; z2; ev]` by
       metis_tac[] >> metis_tac[]) >>
  `ret_pc_ok cenv st cc` by
    (irule ret_pc_ok_frame >> qexistsl_tac [`cenv`, `t0`, `st`] >> simp[]) >>
  `cc.vs_current_bb = cond_lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
   FLOOKUP cc.vs_allocas A.inst_id = SOME (w2n w, sz)` by
    (simp[Abbr `cc`, jump_to_def] >> fs[Abbr `A`, mk_inst_def]) >>
  `lookup_var p cc = SOME w` by
    (`~MEM p [cv; rv; g1; z1; g2; z2; ev]` by
       simp[ASCIInumbersTheory.toString_inj] >> metis_tac[]) >>
  `lookup_var cv cc = SOME (i2w (n1 + &0)) /\
   lookup_var ev cc = SOME (i2w n2)` by
    (gvs[Abbr `cc`, lookup_var_def, jump_to_def, wordsTheory.WORD_SUB_ADD2]) >>
  suspend "loop_code"
QED

Resume for_range_checked_tail_outcome[loop_code]:
  `sb0.cs_next_var <= sb1.cs_next_var` by metis_tac[] >>
  `local_ptrs_reserved bc sb0` by
    (irule local_ptrs_reserved_next_var >>
     qexists_tac `st with cs_next_var := st.cs_next_var + 1` >> simp[] >>
     irule declare_local_reserved >> metis_tac[]) >>
  `type_memory_size tyv = 32` by
    (drule_all is_int_type_memory_size >> simp[]) >>
  `(!scs. not_local_ptr cenv scs cv) /\ (!scs. not_local_ptr cenv scs dv) /\
   (!scs. not_local_ptr cenv scs nv)` by
    (rpt conj_tac >> gen_tac >>
     qpat_assum `cv = _` SUBST1_TAC >> qpat_assum `dv = _` SUBST1_TAC >>
     qpat_assum `nv = _` SUBST1_TAC >>
     irule reserved_fresh_not_local >> qexists_tac `st` >> fs[]) >>
  `for_code func cenv bc ty stmts id tyv p sz A cv ev dv nv
      cond_lbl exit_lbl body_lbl incr_lbl
      (st.cs_next_id+12) (st.cs_next_id+13) (st.cs_next_id+14) bbb
      sj.cs_next_id (sj.cs_next_id+1) (sj.cs_next_id+2) sb0 sb1 sj` by
    (drule_all declare_local_ptr >> strip_tac >>
     simp[for_code_def, block_is_terminated_def,
          mk_inst_def, not_fresh_at_def, is_terminator_def]) >>
  suspend "loop_apply"
QED

Resume for_range_checked_tail_outcome[loop_apply]:
  `!x. not_fresh_at st x ==> x <> dv /\ x <> cv /\ x <> nv` by
    (rpt strip_tac >> fs[not_fresh_at_def] >> rw[] >>
     first_x_assum irule >> fs[]) >>
  `!scs. lookup_scopes id scs = NONE ==> not_local_ptr bc (FEMPTY::scs) p` by
    (rpt strip_tac >>
     `not_local_ptr cenv (FEMPTY::scs) p` by
       (qpat_assum `p = _` SUBST1_TAC >> irule reserved_fresh_not_local >>
        qexists_tac `st` >> simp[]) >>
     irule not_local_ptr_name_update >> qexistsl_tac [`cenv`, `id`] >> simp[] >>
     drule_all declare_local_ptr >> strip_tac >>
     qpat_assum `_ = cenv` (fn th => ONCE_REWRITE_TAC [SYM th]) >> simp[]) >>
  drule (for_loop_alloca |> SPEC_ALL |> Q.INST [`k` |-> `0`] |> SRULE [] |> GEN_ALL) >>
  disch_then (drule_at (Pat `ret_pc_ok _ _ _`)) >>
  disch_then (drule_at (Pat `lookup_var ev _ = _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `gas_admissible _ _ _`)) >>
  disch_then (qspecl_then [`w`, `RetQ`, `P`] mp_tac) >>
  (impl_tac >- (simp[] >>
    qpat_assum `!ei j gs r2 es2 sc rest. _` MATCH_ACCEPT_TAC)) >>
  strip_tac >> suspend "loop_compose"
QED

Resume for_range_checked_tail_outcome[loop_compose]:
  `gas_marked_path F ctx func t0 0 (OK cc)` by
    (irule (gas_marked_path_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexists_tac `jump_to entry_lbl sA` >> simp[Abbr `cc`] >> gvs[]) >>
  qpat_x_assum `gas_outcome _ _ _ _ (es,cc) _ _` mp_tac >>
  rewrite_tac[gas_outcome_def] >>
  strip_tac >> qexists_tac `marks`
  >- suspend "loop_normal" >>
  disj2_tac >>
  irule_at Any gas_exempt_cert_zero_prefix >>
  goal_assum (drule_at Any) >> simp[]
QED

Resume for_range_checked_tail_outcome[loop_normal]:
  disj1_tac >>
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_summary_at_def] >> strip_tac >>
  `gas_marked_exec F (ctx,func)
     (eval_for cx tyv id stmts (GENLIST (\j. IntV (n1 + &j)) (Num (n2-n1))))
     (es,t0) marks res es_end r` by
    (irule gas_marked_exec_zero_prefix >> goal_assum (drule_at Any) >> simp[]) >>
  qexistsl_tac [`res`, `es_end`, `r`] >> simp[] >>
  suspend "loop_post"
QED

Resume for_range_checked_tail_outcome[loop_post]:
  disj1_tac >>
  qpat_x_assum `(\res ee s. _) _ _ _` (strip_assume_tac o BETA_RULE) >>
  simp[stmt_post_def, stmt_lands_def, cenv_top_ext_refl] >>
  suspend "loop_frames"
QED

Resume for_range_checked_tail_outcome[loop_frames]:
  conj_tac >- simp[block_is_terminated_def] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!a b. FLOOKUP t0.vs_allocas a = SOME b ==> _`
        (drule_then assume_tac) >>
      qpat_x_assum `!a b. FLOOKUP _ a = SOME b ==> FLOOKUP t.vs_allocas a = SOME b`
        irule >>
      simp[Abbr `cc`, jump_to_def]) >>
  `alloca_frame cenv es st t0 cenv es cc` by
    (irule alloca_frame_of_mem_frame >>
     simp[] >>
     reverse conj_tac >- metis_tac[] >>
     `sA.vs_memory = t0.vs_memory` by
       metis_tac[stmtSimDeclPathTheory.exec_alloca_memory] >>
     simp[Abbr `cc`, jump_to_def]) >>
  irule alloca_frame_trans >>
  qexistsl_tac [`cenv`, `es`, `cc`, `st`] >>
  simp[] >>
  conj_tac
  >- (rpt strip_tac >> simp[Abbr `cc`, jump_to_def] >> metis_tac[]) >>
  qpat_x_assum `!frame_start. _` (qspec_then `st` mp_tac) >>
  simp[alloca_frame_def]
QED

Resume for_range_checked_tail_outcome[bad_bound]:
  `?t. gas_marked_path F ctx func (jump_to entry_lbl sA) 0
        (Abort Revert_abort t)` by
    (first_x_assum irule >> simp[]) >>
  `gas_marked_path F ctx func t0 0 (Abort Revert_abort t)` by
    (irule (gas_marked_path_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexists_tac `jump_to entry_lbl sA` >> simp[]) >>
  simp[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INR (Error (RuntimeError "For too long"))`, `es`,
                 `Abort Revert_abort t`] >>
  simp[gas_marked_exec_def, raise_def, exit_result_def,
       stmt_exit_def, expr_exit_def]
QED

Resume for_range_checked_tail_outcome[bad_order]:
  `?t. gas_marked_path F ctx func (jump_to entry_lbl sA) 0
        (Abort Revert_abort t)` by
    (qpat_x_assum `_ \/ _ ==> ?t. _` irule >>
     disj1_tac >> intLib.ARITH_TAC) >>
  `gas_marked_path F ctx func t0 0 (Abort Revert_abort t)` by
    (irule (gas_marked_path_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexists_tac `jump_to entry_lbl sA` >> simp[]) >>
  simp[checked_range_tail, gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INR (Error (RuntimeError "no range"))`, `es`,
                 `Abort Revert_abort t`] >>
  simp[gas_marked_exec_def, raise_def, exit_result_def,
       stmt_exit_def, expr_exit_def]
QED

Finalise for_range_checked_tail_outcome

(* Checked source endpoints may still lower to literal operands. The body
   judgment is needed only after successful bound checks and for a nonempty
   iterator, when the endpoint hypothesis supplies Q. The invariant P holds
   after endpoint evaluation and is preserved by continuing iterations. *)
Theorem compile_for_range_checked_frag_active:
  !P Q (ctx, func, cx, lctx, RetQ, cenv, env, ty)
   id fty e1 e2 bound stmts es tyv.
    is_int_type fty /\
    evaluate_type (get_tenv cx) fty = SOME tyv /\
    32 <= type_memory_bytes cenv fty /\
    type_memory_bytes cenv fty < dimword (:256) /\ bound < dimword (:256) /\
    cenv.ce_alloca_locals /\ lookup_scopes id es.scopes = NONE /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    (!c lc sa sb. compile_stmts c lc ty stmts sa = ((), sb) ==>
                  cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
    is_word_type (expr_type e1) /\
    evaluate_type (get_tenv cx) (expr_type e1) = SOME tyv /\
    is_word_type (expr_type e2) /\
    evaluate_type (get_tenv cx) (expr_type e2) = SOME tyv /\
    expr_sim ctx func cenv cx fty e1 es /\
    (!gs tv es1.
       (do raw <- eval_expr cx e1; read_result cx raw od)
         (es with gas_obs := gs) = (INL tv, es1) ==>
       ?n1. tv = IntV n1 /\ value_has_type tyv (IntV n1) /\
            expr_sim ctx func cenv cx fty e2 es1 /\
            !gs2 tv2 es2.
              (do raw <- eval_expr cx e2; read_result cx raw od)
                (es1 with gas_obs := gs2) = (INL tv2, es2) ==>
              ?n2. tv2 = IntV n2 /\ value_has_type tyv (IntV n2) /\
                   P es2) /\
    (!gs n1 es1 n2 es2.
       (do raw <- eval_expr cx e1; read_result cx raw od)
         (es with gas_obs := gs) = (INL (IntV n1), es1) /\
       (do raw <- eval_expr cx e2; read_result cx raw od) es1 =
         (INL (IntV n2), es2) /\
       n1 <= n2 /\ Num (n2 - n1) <= bound /\ 0 < Num (n2 - n1) ==> Q) /\
    well_typed_expr env e1 /\ well_typed_expr env e2 /\
    (!x t. FLOOKUP env.var_types x = SOME t ==>
           well_formed_type env.type_defs t) /\
    ~(?a1 n1 a2 n2. e1 = Literal a1 (IntL n1) /\ e2 = Literal a2 (IntL n2)) /\
    (!st0 c st1 ex inc ei n1 j.
       declare_local cenv id fty st0 = (c, st1) /\
       Q /\ P ei /\ lookup_scopes id ei.scopes = NONE /\
       value_has_type tyv (IntV (n1 + &j)) ==>
       stmt_frag ctx func cx (InLoop ex inc) RetQ c
         (stmts_env c (InLoop ex inc) ty stmts) (eval_stmts cx stmts)
         (ei with scopes :=
            (FEMPTY |+ (id, <| assignable := F; type := tyv;
                               value := IntV (n1 + &j); popped := [] |>)) :: ei.scopes)) /\
    (!ei n1 j gs r2 es2 sc rest.
       Q /\ P ei /\ lookup_scopes id ei.scopes = NONE /\
       value_has_type tyv (IntV (n1 + &j)) /\
       eval_stmts cx stmts
         (ei with <| scopes :=
            (FEMPTY |+ (id, <| assignable := F; type := tyv;
                               value := IntV (n1 + &j); popped := [] |>)) :: ei.scopes;
                     gas_obs := gs |>) =
         (r2, es2) /\
       (r2 = INL () \/ r2 = INR ContinueException) /\
       es2.scopes = sc :: rest ==>
       P (es2 with scopes := rest)) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (For id fty (Range e1 e2) bound stmts))
      (eval_stmt cx (For id fty (Range e1 e2) bound stmts)) es
Proof
  map_every qx_gen_tac [`P`, `Q`] >>
  (* Expose the paired abstraction to ordinary forall rewriting. *)
  CONV_TAC (RAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp_tac (srw_ss()) [pairTheory.FORALL_PROD] >>
  map_every qx_gen_tac [`ctx`, `func`, `cx`, `lctx`, `RetQ`, `cenv`, `env`, `ty`] >>
  rpt gen_tac >>
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  `is_word_type fty` by
    (fs[is_int_type_cases] >> gvs[is_word_type_def]) >>
  REWRITE_TAC [stmt_frag_def, stmt_framed_frag_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  Cases_on `compile_stmt cenv lctx ty (For id fty (Range e1 e2) bound stmts)
              sa` >>
  simp[] >> strip_tac >> gvs[] >>
  rename1 `compile_stmt _ _ _ _ sa = (uu, sb)` >>
  `uu = ()` by simp[oneTheory.one] >> gvs[] >>
  Cases_on `lower_value compile_expr cenv fty e1 sa` >>
  rename1 `_ = (op1, s1)` >>
  Cases_on `lower_value compile_expr cenv fty e2 s1` >>
  rename1 `_ = (op2, s2)` >>
  qspecl_then [`cenv`, `env`, `fty`, `e1`, `sa`, `op1`, `s1`] mp_tac
    lower_value_word_shape >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  qspecl_then [`cenv`, `env`, `fty`, `e2`, `s1`, `op2`, `s2`] mp_tac
    lower_value_word_shape >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  `cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var /\
   cs_extends s1 s2 /\ s1.cs_next_var <= s2.cs_next_var` by
    metis_tac[cj 2 compile_expr_grows] >>
  `for_range_checked_code cenv lctx ty id fty bound stmts op1 op2 s2 =
     ((), sb)` by metis_tac[compile_stmt_for_range_checked] >>
  `cs_extends s2 sb` by
    (drule_at (Pat `for_range_checked_code _ _ _ _ _ _ _ _ _ _ = _`)
       for_range_checked_parts >>
     disch_then (qspecl_then [`sa`, `func`] mp_tac) >>
     simp[] >> metis_tac[cs_extends_trans]) >>
  `cs_extends sa s2` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa s2 func /\ fn_has_code s2 sb func` by
    (qspecl_then [`sa`, `s2`, `sb`, `func`] mp_tac fn_has_code_split >>
     simp[]) >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s2 func` by
    (qspecl_then [`sa`, `s1`, `s2`, `func`] mp_tac fn_has_code_split >>
     simp[]) >>
  `local_ptrs_reserved cenv s1` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
  `local_ptrs_reserved cenv s2` by
    (irule local_ptrs_reserved_next_var >> qexists `s1` >> simp[]) >>
  suspend "endpoints"
QED

Resume compile_for_range_checked_frag_active[endpoints]:
  `eval_stmt cx (For id fty (Range e1 e2) bound stmts) =
   do v1 <- (do raw <- eval_expr cx e1; read_result cx raw od);
      v2 <- (do raw <- eval_expr cx e2; read_result cx raw od);
      rl <- lift_sum (get_range_limits v1 v2);
      check (compatible_bound (Dynamic bound) (SND rl)) "For too long";
      eval_for cx tyv id stmts
        (GENLIST (\j. IntV (FST rl + &j)) (SND rl)) od` by
    (irule eval_stmt_for_range_forced >> simp[]) >>
  qpat_x_assum `gas_admissible _ _ _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  simp[SF ETA_ss] >>
  irule forced_endpoint_bind_outcome >>
  simp[] >> qexistsl_tac [`cenv`, `fty`, `lctx`, `op1`, `sa`, `s1`] >>
  fs[SF ETA_ss] >> rpt gen_tac >> strip_tac >>
  suspend "first_end"
QED

Resume compile_for_range_checked_frag_active[first_end]:
  markerLib.RESUME_TAC >>
  qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_marked_exec_def] >> strip_tac >>
  first_x_assum (qspec_then `[]` mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `!gs tv es1. bind (eval_expr cx e1) _ _ = _ ==> _`
    (drule_then strip_assume_tac) >>
  gvs[] >>
  `stmt_state_rel ctx func cenv cx (mid with gas_obs := []) t` by
    (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[expr_post_def] >> strip_tac >>
     qpat_x_assum `stmt_state_rel _ _ _ _ mid t`
       (mp_tac o Q.INST [`gs` |-> `[]`, `readings` |-> `t.vs_gas_readings`,
                         `k` |-> `t.vs_inst_idx`] o MATCH_MP msg_gas_state_frame) >>
     qpat_x_assum `t.vs_inst_idx = _` kall_tac >> simp[]) >>
  `~t.vs_halted` by
    (fs[gas_marked_path_def] >> metis_tac[gas_path_normal]) >>
  irule forced_endpoint_bind_outcome >> simp[] >>
  qexistsl_tac [`cenv`, `fty`, `lctx`, `op2`, `s1`, `s2`] >>
  simp[] >> rpt gen_tac >> strip_tac >> suspend "second_end"
QED

Resume compile_for_range_checked_frag_active[second_end]:
  qpat_assum `gas_marked_exec _ _ _ _ _ _ _ (OK t')` mp_tac >>
  rewrite_tac[gas_marked_exec_def] >> strip_tac >>
  first_x_assum (qspec_then `[]` mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `!gs2 tv2 es2. bind (eval_expr cx e2) _ _ = _ ==> _`
    (drule_then strip_assume_tac) >> gvs[] >>
  `stmt_state_rel ctx func cenv cx (mid' with gas_obs := []) t'` by
    (qpat_assum `expr_post _ _ _ _ e2 _ _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[expr_post_def] >> strip_tac >>
     qpat_x_assum `stmt_state_rel _ _ _ _ mid' t'`
       (mp_tac o Q.INST [`gs` |-> `[]`, `readings` |-> `t'.vs_gas_readings`,
                         `k` |-> `t'.vs_inst_idx`] o MATCH_MP msg_gas_state_frame) >>
     qpat_x_assum `t'.vs_inst_idx = _` kall_tac >> simp[]) >>
  `~t'.vs_halted` by
    (fs[gas_marked_path_def] >> metis_tac[gas_path_normal]) >>
  `eval_operand op1 t = SOME (i2w n1)` by
    (qpat_x_assum `expr_post _ _ _ _ e2 _ _ _ _ _ _ _ _` kall_tac >>
     drule_all range_expr_post_int_operand >> simp[]) >>
  `eval_operand op2 t' = SOME (i2w n2)` by
    (drule_all range_expr_post_int_operand >> simp[]) >>
  `eval_operand op1 t' = SOME (i2w n1)` by
    (qpat_assum `expr_post _ _ _ _ e2 _ _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[expr_post_def] >> strip_tac >>
     Cases_on `op1` >> gvs[eval_operand_def]) >>
  `n1 <= n2 /\ Num (n2 - n1) <= bound /\ 0 < Num (n2 - n1) ==> Q` by
    (strip_tac >>
     qpat_x_assum `!gs n1 es1 n2 es2. _ ==> Q` irule >>
     simp[SF ETA_ss] >>
     qpat_assum `gas_marked_exec _ _ (bind (eval_expr cx e1) _) _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     metis_tac[]) >>
  suspend "tail_entry"
QED

Resume compile_for_range_checked_frag_active[tail_entry]:
  `ret_pc_ok cenv s1 t` by
    (irule ret_pc_ok_frame >> qexistsl_tac [`cenv`, `s0`, `sa`] >>
     fs[expr_post_def]) >>
  `ret_pc_ok cenv s2 t'` by
    (irule ret_pc_ok_frame >> qexistsl_tac [`cenv`, `t`, `s1`] >>
     fs[expr_post_def]) >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (qpat_x_assum `bind (eval_expr cx e1) _ _ = _` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> rpt strip_tac >>
     imp_res_tac read_result_state >> gvs[] >>
     drule eval_expr_preserves_scopes_dom >> simp[]) >>
  `MAP FDOM mid.scopes = MAP FDOM mid'.scopes` by
    (qpat_x_assum `bind (eval_expr cx e2) _ _ = _` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> rpt strip_tac >>
     imp_res_tac read_result_state >> gvs[] >>
     drule eval_expr_preserves_scopes_dom >> simp[]) >>
  `lookup_scopes id (mid' with gas_obs := []).scopes = NONE` by
    (simp[] >> irule lookup_scopes_none_map_fdom >>
     qexists_tac `es.scopes` >> simp[]) >>
  suspend "tail_apply"
QED

Resume compile_for_range_checked_frag_active[tail_apply]:
  qmatch_goalsub_abbrev_tac `gas_outcome _ _ _ source _ _ _` >>
  `gas_outcome F (cx_tops cx) (ctx,func) source
    (mid' with gas_obs := [],t')
    (stmt_post ctx func cx lctx cenv cenv s2 sb (mid' with gas_obs := []) t')
    (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)` by
    (simp[Abbr `source`] >> irule for_range_checked_tail_outcome >>
     simp[] >> qexistsl_tac [`P`, `fty`, `op1`, `op2`, `ty`] >>
     simp[] >> suspend "tail_hyps") >>
  suspend "tail_transport"
QED

Resume compile_for_range_checked_frag_active[tail_hyps]:
  conj_tac
  >- (rpt strip_tac >> fs[not_fresh_at_def] >> rpt strip_tac >>
      first_x_assum irule >> decide_tac) >>
  conj_tac
  >- (rpt strip_tac >>
      `Q` by (first_x_assum irule >> simp[] >> decide_tac) >>
      `value_has_type tyv (IntV (n1 + &j))` by
        (drule_all range_value_has_type >> simp[]) >>
      first_x_assum irule >> simp[] >> qexists_tac `s2` >> simp[]) >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  `Q` by (first_x_assum irule >> simp[] >> decide_tac) >>
  `value_has_type tyv (IntV (n1 + &j))` by
    (drule_all range_value_has_type >> simp[]) >>
  first_x_assum irule >> metis_tac[]
QED

Resume compile_for_range_checked_frag_active[tail_transport]:
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qexists_tac `marks''` >> disj1_tac >>
  fs[gas_summary_at_def]
  >- (qexistsl_tac [`res`, `es_end`, `r`] >> simp[] >>
      disj1_tac >>
      `alloca_frame cenv es sa s0 cenv mid t` by
        (mp_tac (Q.INST [`e` |-> `e1`, `ee` |-> `mid`, `sb` |-> `s1`,
                         `v` |-> `IntV n1`, `op` |-> `op1`] expr_post_alloca_frame) >>
         impl_tac >- (simp[] >> metis_tac[]) >> simp[]) >>
      `alloca_frame cenv mid s1 t cenv (mid' with gas_obs := []) t'` by
        (mp_tac (Q.INST [`e` |-> `e2`, `es` |-> `mid with gas_obs := []`,
                         `sa` |-> `s1`, `sb` |-> `s2`, `s0` |-> `t`, `ee` |-> `mid'`,
                         `t` |-> `t'`, `v` |-> `IntV n2`, `op` |-> `op2`]
                   expr_post_alloca_frame) >>
         impl_tac >- (simp[] >> metis_tac[]) >> simp[alloca_frame_def]) >>
      `alloca_frame cenv es sa s0 cenv (mid' with gas_obs := []) t'` by
        (qpat_assum `alloca_frame cenv es sa s0 cenv mid t` (fn th1 =>
           qpat_assum `alloca_frame cenv mid s1 t _ _ _` (fn th2 =>
             mp_tac (MATCH_MP (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
               alloca_frame_trans) th1) th2))) >>
         impl_tac >- decide_tac >>
         impl_tac >- fs[expr_post_def] >> simp[]) >>
      `sa.cs_next_id <= s2.cs_next_id` by decide_tac >>
      irule stmt_post_entry_frame >>
      qexistsl_tac [`mid' with gas_obs := []`, `t'`, `s2`] >>
      fs[expr_post_def] >> rpt strip_tac >>
      `not_fresh_at s1 x` by
        (fs[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
      `not_fresh_at s2 x` by
        (fs[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
      metis_tac[]) >>
  qexistsl_tac [`res`, `es_end`, `r`] >> simp[]) >>
  qexists_tac `marks''` >> disj2_tac >> metis_tac[]
QED

Finalise compile_for_range_checked_frag_active

(* The original checked fragment is the always-active specialization. *)
Theorem compile_for_range_checked_frag:
  !P ctx func cx lctx RetQ cenv env ty id fty e1 e2 bound stmts es tyv.
    is_int_type fty /\
    evaluate_type (get_tenv cx) fty = SOME tyv /\
    32 <= type_memory_bytes cenv fty /\
    type_memory_bytes cenv fty < dimword (:256) /\ bound < dimword (:256) /\
    cenv.ce_alloca_locals /\ lookup_scopes id es.scopes = NONE /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    (!c lc sa sb. compile_stmts c lc ty stmts sa = ((), sb) ==>
                  cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
    is_word_type (expr_type e1) /\
    evaluate_type (get_tenv cx) (expr_type e1) = SOME tyv /\
    is_word_type (expr_type e2) /\
    evaluate_type (get_tenv cx) (expr_type e2) = SOME tyv /\
    expr_sim ctx func cenv cx fty e1 es /\
    (!gs tv es1.
       (do raw <- eval_expr cx e1; read_result cx raw od)
         (es with gas_obs := gs) = (INL tv, es1) ==>
       ?n1. tv = IntV n1 /\ value_has_type tyv (IntV n1) /\
            expr_sim ctx func cenv cx fty e2 es1 /\
            !gs2 tv2 es2.
              (do raw <- eval_expr cx e2; read_result cx raw od)
                (es1 with gas_obs := gs2) = (INL tv2, es2) ==>
              ?n2. tv2 = IntV n2 /\ value_has_type tyv (IntV n2) /\
                   P es2) /\
    well_typed_expr env e1 /\ well_typed_expr env e2 /\
    (!x t. FLOOKUP env.var_types x = SOME t ==>
           well_formed_type env.type_defs t) /\
    ~(?a1 n1 a2 n2. e1 = Literal a1 (IntL n1) /\ e2 = Literal a2 (IntL n2)) /\
    (!st0 c st1 ex inc ei n1 j.
       declare_local cenv id fty st0 = (c, st1) /\
       P ei /\ lookup_scopes id ei.scopes = NONE /\
       value_has_type tyv (IntV (n1 + &j)) ==>
       stmt_frag ctx func cx (InLoop ex inc) RetQ c
         (stmts_env c (InLoop ex inc) ty stmts) (eval_stmts cx stmts)
         (ei with scopes :=
            (FEMPTY |+ (id, <| assignable := F; type := tyv;
                               value := IntV (n1 + &j); popped := [] |>)) :: ei.scopes)) /\
    (!ei n1 j gs r2 es2 sc rest.
       P ei /\ lookup_scopes id ei.scopes = NONE /\
       value_has_type tyv (IntV (n1 + &j)) /\
       eval_stmts cx stmts
         (ei with <| scopes :=
            (FEMPTY |+ (id, <| assignable := F; type := tyv;
                               value := IntV (n1 + &j); popped := [] |>)) :: ei.scopes;
                     gas_obs := gs |>) =
         (r2, es2) /\
       (r2 = INL () \/ r2 = INR ContinueException) /\
       es2.scopes = sc :: rest ==>
       P (es2 with scopes := rest)) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (For id fty (Range e1 e2) bound stmts))
      (eval_stmt cx (For id fty (Range e1 e2) bound stmts)) es
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`P`, `T`] compile_for_range_checked_frag_active) >>
  CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX)))) >>
  simp_tac (srw_ss()) [pairTheory.FORALL_PROD] >>
  disch_then irule >> gvs[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- metis_tac[] >>
  qexists `env` >> simp[] >> metis_tac[]
QED

(* Integrity gate for the forced iterator boundary and checked-range consumer. *)
val () = List.app (fn th =>
  let val (ors, axs) = Tag.dest_tag (Thm.tag th)
  in if null axs andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") ors
     then print "RANGE_FORCE_AUDIT OK\n"
     else raise Fail "forced range inherited admission"
  end) [eval_iterator_range_forced, eval_stmt_for_range_cases,
        compile_for_range_checked_frag_active, compile_for_range_checked_frag];
