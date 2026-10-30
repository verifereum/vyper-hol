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
 *   compile_for_range_checked_frag — the statement fragment of For over
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
  stmtSim stmtSimForParts stmtSimForLoop exprWordOperand
  list rich_list finite_map pred_set
  fragExec localPtrsProps exprSim loweringSlice freshWrites
  vyperEvalExprPreservesScopesDom
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding
  vyperInterpreter vyperState vyperValue vyperTyping vyperEvalPreservesScopes
  vyperExprNoControl vyperValueOperation vyperArith
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
    (rpt strip_tac >> gvs[markerTheory.Abbrev_def]) >>
  `eval_operand (Var rv) s2 = SOME (b - a) /\
   eval_operand (Var rv) s6 = SOME (b - a) /\
   eval_operand (Var g1) s3 = SOME (bool_to_word bad1) /\
   eval_operand (Var z1) s4 = SOME (bool_to_word (bool_to_word bad1 = 0w)) /\
   eval_operand (Var g2) s5 = SOME (bool_to_word bad2) /\
   eval_operand (Var z2) s6 = SOME (bool_to_word (bool_to_word bad2 = 0w))` by
    (gvs[markerTheory.Abbrev_def, ALL_DISTINCT, eval_operand_def,
         lookup_var_update_var]) >>
  `step_inst_base (mk_inst (i + 2) cmp [op1; op2] [g1]) s2 = OK s3` by
    (simp[Abbr `s3`, Abbr `bad1`] >> Cases_on `cmp = SGT` >> gvs[] >>
     FIRST [irule step_SGT, irule step_GT] >> metis_tac[]) >>
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

Resume for_entry_checked_block[runs]:
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
  >- (`step_inst_base (mk_inst (i + 4) ASSERT [Var z1] []) s4 =
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
      drule_at (Pos last) run_from_prefix_abort >>
      disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >> simp[] >>
      metis_tac[]) >>
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
  >- (`step_inst_base (mk_inst (i + 7) ASSERT [Var z2] []) s6 =
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
      drule_at (Pos last) run_from_prefix_abort >>
      disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >> simp[] >>
      metis_tac[]) >>
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
  drule_at (Pos last) run_from_prefix_ok >>
  disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >> simp[] >>
  strip_tac >>
  `ee with vs_vars := s7.vs_vars = s7` by
    simp[Abbr `s7`, Abbr `s6`, Abbr `s5`, Abbr `s4`, Abbr `s3`, Abbr `s2`,
         Abbr `s1`, update_var_def, venom_state_component_equality] >>
  `~s7.vs_halted` by
    gvs[markerTheory.Abbrev_def, update_var_def] >>
  qexists_tac `s7.vs_vars` >> asm_rewrite_tac[] >>
  rpt conj_tac
  >- gvs[markerTheory.Abbrev_def, lookup_var_update_var, ALL_DISTINCT]
  >- gvs[markerTheory.Abbrev_def, lookup_var_update_var]
  >- (rpt strip_tac >>
      gvs[markerTheory.Abbrev_def, lookup_var_update_var]) >>
  rpt strip_tac >> qexists_tac `SUC fuel` >>
  qpat_x_assum `!fuel. run_from fuel ctx func ee = _`
    (fn th => rewrite_tac [th]) >>
  simp[] >>
  irule run_from_jump_result >>
  `jump_to cond_lbl (s7 with vs_inst_idx := 9) = jump_to cond_lbl s7` by
    simp[jump_to_def] >>
  `get_instruction bb 9 = SOME (mk_inst (i + 9) JMP [Label cond_lbl] [])` by
    simp[Abbr `bb`, get_instruction_def] >>
  simp[] >> qexists_tac `cond_lbl` >>
  fs[venomInstTheory.mk_inst_def, is_terminator_def, step_jmp_behavior]
QED

Finalise for_entry_checked_block


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
    ~((?w. op1 = Lit w) /\ (?w. op2 = Lit w)) ==>
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
  Cases_on `op1` >> Cases_on `op2` >> gvs[]
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
  rw[not_local_ptr_def] >> strip_tac >>
  fs[local_ptrs_reserved_def, not_fresh_at_def] >>
  qpat_x_assum `!n1 n2 p sz1 sz2. _`
    (qspecl_then [`name`, `name`, `STRING #"%" (toString n)`, `sz`, `sz`]
       mp_tac) >>
  simp[] >> qexists_tac `n` >> simp[]
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

Theorem range_value_has_type[local]:
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

(* For over a range whose ends are expressions, not both lowered to
   literals (that case is compile_for_range_frag): the ends'
   fragments, whose errors exit, then the loop variable's ALLOCA and the
   checked entry block, whose failed checks revert as the source's range
   errors exit, then the loop (compile_for_range_frag's for_loop).  The
   ends are of the loop variable's integer type and well typed, so their
   operands are held in variables the later code leaves alone
   (lower_value_word_shape).  The body's judgment is assumed for every
   loop value of the variable's type, at the states where P holds; P holds
   after the ends and again after each iteration that goes on.  The
   entry block compares the rounds with the word n2w bound, so the bound
   must fit a word; nothing upstream bounds it yet. *)
Theorem compile_for_range_checked_frag:
  !P ctx func cx lctx RetQ cenv env ty id fty e1 e2 bound stmts es res es'
   tyv.
    eval_stmt cx (For id fty (Range e1 e2) bound stmts) es = (res, es') /\
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
    (!tv es1. (do raw <- eval_expr cx e1; read_result cx raw od) es = (INL tv, es1) ==>
       ?n1. tv = IntV n1 /\ value_has_type tyv (IntV n1) /\
            expr_sim ctx func cenv cx fty e2 es1 /\
            !tv2 es2. (do raw <- eval_expr cx e2; read_result cx raw od) es1 = (INL tv2, es2) ==>
              ?n2. tv2 = IntV n2 /\ value_has_type tyv (IntV n2) /\
                   P es2) /\
    well_typed_expr env e1 /\ well_typed_expr env e2 /\
    (!x t. FLOOKUP env.var_types x = SOME t ==>
           well_formed_type env.type_defs t) /\
    (!sa op1 s1 op2 s2.
       lower_value compile_expr cenv fty e1 sa = (op1, s1) /\
       lower_value compile_expr cenv fty e2 s1 = (op2, s2) ==>
       ~((?w. op1 = Lit w) /\ (?w. op2 = Lit w))) /\
    (!st0 c st1 ex inc ei n1 j r2 es2.
       declare_local cenv id fty st0 = (c, st1) /\
       P ei /\ lookup_scopes id ei.scopes = NONE /\
       value_has_type tyv (IntV (n1 + &j)) /\
       eval_stmts cx stmts
         (ei with scopes :=
            (FEMPTY |+ (id, <| assignable := F; type := tyv;
                               value := IntV (n1 + &j); popped := [] |>)) :: ei.scopes) =
         (r2, es2) ==>
       stmt_frag ctx func cx (InLoop ex inc) RetQ c
         (stmts_env c (InLoop ex inc) ty stmts)
         (ei with scopes :=
            (FEMPTY |+ (id, <| assignable := F; type := tyv;
                               value := IntV (n1 + &j); popped := [] |>)) :: ei.scopes)
         r2 es2) /\
    (!ei n1 j r2 es2 sc rest.
       P ei /\ lookup_scopes id ei.scopes = NONE /\
       value_has_type tyv (IntV (n1 + &j)) /\
       eval_stmts cx stmts
         (ei with scopes :=
            (FEMPTY |+ (id, <| assignable := F; type := tyv;
                               value := IntV (n1 + &j); popped := [] |>)) :: ei.scopes) =
         (r2, es2) /\
       (r2 = INL () \/ r2 = INR ContinueException) /\
       es2.scopes = sc :: rest ==>
       P (es2 with scopes := rest)) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (For id fty (Range e1 e2) bound stmts)) es res es'
Proof
  rpt gen_tac >>
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  `is_word_type fty` by
    (fs[is_int_type_cases] >> gvs[is_word_type_def]) >>
  REWRITE_TAC [stmt_frag_def] >>
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
  qpat_x_assum `!sa op1 s1 op2 s2. lower_value _ _ _ e1 _ = _ /\ _ ==> _`
    (qspecl_then [`sa`, `op1`, `s1`, `op2`, `s2`] mp_tac) >>
  impl_tac >- simp[] >> disch_then assume_tac >>
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
  qspecl_then [`cenv`, `lctx`, `ty`, `id`, `fty`, `bound`, `stmts`, `op1`,
               `op2`, `sa`, `s2`, `sb`, `func`]
    mp_tac for_range_checked_parts >>
  impl_tac >- (simp[] >> metis_tac[cs_extends_trans]) >> strip_tac >>
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
  qspecl_then [`cx`, `id`, `fty`, `e1`, `e2`, `bound`, `stmts`, `es`, `res`,
               `es'`, `tyv`, `lctx`] mp_tac eval_stmt_for_range_cases >>
  impl_tac
  >- (simp[] >> rpt strip_tac >>
      qpat_x_assum `!tv es1. (do raw <- eval_expr cx e1; read_result cx raw od) es = _ ==> _` drule >>
      strip_tac >> simp[] >> rpt strip_tac >>
      qpat_x_assum `!tv2 es2. (do raw <- eval_expr cx e2; read_result cx raw od) _ = _ ==> _` drule >>
      strip_tac >> simp[]) >>
  disch_then (qx_choosel_then [`r1`, `es1`]
    (fn th => MAP_EVERY assume_tac (CONJUNCTS th))) >>
  suspend "ends"
QED

Resume compile_for_range_checked_frag[ends]:
  qpat_x_assum `expr_sim _ _ _ _ _ e1 _`
    (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`sa`, `s1`, `op1`, `r1`, `es1`, `s0`] mp_tac) >>
  impl_tac >- fs[] >>
  simp[frag_exec_def] >> disch_then (qspec_then `func` mp_tac) >>
  impl_tac >- fs[] >>
  qpat_x_assum `(?ex. r1 = INR ex /\ _) \/ _`
    (DISJ_CASES_THEN2 strip_assume_tac
       (qx_choosel_then [`n1`, `r2`, `es2`]
          (fn th => MAP_EVERY assume_tac (CONJUNCTS th))))
  >- (gvs[] >> strip_tac >> disj2_tac >> qexists_tac `fuel` >> simp[] >>
      irule expr_exit_stmt_exit >> qexists `INR ex` >> simp[]) >>
  qpat_x_assum `r1 = _` SUBST_ALL_TAC >> simp[] >> strip_tac >>
  rename1 `expr_post func cenv cx e1 es sa s1 s0 es1 (IntV n1) op1 t1` >>
  qpat_x_assum `!tv es1. (do raw <- eval_expr cx e1; read_result cx raw od) es = _ ==> _` drule >> strip_tac >>
  qpat_x_assum `IntV n1 = _`
    (SUBST_ALL_TAC o SYM o SIMP_RULE (srw_ss()) []) >>
  `eval_operand op1 t1 = SOME (i2w n1)` by
    (qpat_x_assum `expr_post _ _ _ e1 _ _ _ _ _ _ _ _` mp_tac >>
     simp[expr_post_def, expr_val_rel_def] >> rpt strip_tac >>
     TRY (first_x_assum (qspec_then `tyv` mp_tac)) >>
     gvs[typed_val_to_w256_word_value, word_value_def, val_to_w256_def]) >>
  `stmt_state_rel func cenv cx es1 t1` by fs[expr_post_def] >>
  qpat_x_assum `expr_sim _ _ _ _ _ e2 _`
    (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`s1`, `s2`, `op2`, `r2`, `es2`, `t1`] mp_tac) >>
  impl_tac >- fs[] >>
  simp[frag_exec_def] >> disch_then (qspec_then `func` mp_tac) >>
  impl_tac >- fs[] >>
  qpat_x_assum `(?ex. r2 = INR ex /\ _) \/ _`
    (DISJ_CASES_THEN2 strip_assume_tac
       (qx_choosel_then [`n2`]
          (fn th => MAP_EVERY assume_tac (CONJUNCTS th))))
  >- (rpt BasicProvers.VAR_EQ_TAC >> simp[] >> strip_tac >> disj2_tac >>
      qpat_x_assum `!fuel. (!e. run_from fuel ctx func t1 <> Error e) ==> _`
        (qspec_then `fuel` mp_tac) >>
      impl_tac >- metis_tac[exit_result_not_error] >>
      disch_then (qx_choose_then `f0` strip_assume_tac) >>
      qexists_tac `f0` >> simp[] >>
      irule expr_exit_stmt_exit >> qexists `INR ex` >> simp[]) >>
  qpat_x_assum `r2 = _` SUBST_ALL_TAC >> simp[] >> strip_tac >>
  rename1 `expr_post func cenv cx e2 es1 s1 s2 t1 es2 (IntV n2) op2 t2` >>
  suspend "alloca"
QED

Resume compile_for_range_checked_frag[alloca]:
  `value_has_type tyv (IntV n2) /\ P es2` by
    (qpat_x_assum `!tv2 es2. (do raw <- eval_expr cx e2; read_result cx raw od) es1 = _ ==> _` drule >>
     simp[]) >>
  `stmt_state_rel func cenv cx es2 t2` by fs[expr_post_def] >>
  `eval_operand op2 t2 = SOME (i2w n2)` by
    (qpat_x_assum `expr_post _ _ _ e2 _ _ _ _ _ _ _ _` mp_tac >>
     simp[expr_post_def, expr_val_rel_def] >> rpt strip_tac >>
     TRY (first_x_assum (qspec_then `tyv` mp_tac)) >>
     gvs[typed_val_to_w256_word_value, word_value_def, val_to_w256_def]) >>
  `!x w. not_fresh_at s1 x /\ lookup_var x t1 = SOME w ==>
         lookup_var x t2 = SOME w` by fs[expr_post_def] >>
  `eval_operand op1 t2 = SOME (i2w n1)` by
    (Cases_on `op1` >> gvs[eval_operand_def]) >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
         lookup_var x t2 = SOME w` by
    (rpt strip_tac >> `not_fresh_at s1 x` by metis_tac[not_fresh_at_mono] >>
     fs[expr_post_def]) >>
  `!a b. FLOOKUP s0.vs_allocas a = SOME b ==>
         FLOOKUP t2.vs_allocas a = SOME b` by fs[expr_post_def] >>
  `lookup_scopes id es2.scopes = NONE` by
    (irule lookup_scopes_none_map_fdom >> qexists `es.scopes` >>
     `!e si r sf.
        (do raw <- eval_expr cx e; read_result cx raw od) si = (r, sf) ==>
        MAP FDOM si.scopes = MAP FDOM sf.scopes` by
       (rpt gen_tac >> simp[bind_def, AllCaseEqs()] >> strip_tac >>
        imp_res_tac read_result_state >> gvs[] >>
        metis_tac[eval_expr_preserves_scopes_dom]) >>
     metis_tac[]) >>
  (* the loop variable's ALLOCA *)
  drule_all declare_local_ptr >> strip_tac >>
  qabbrev_tac `sz = type_memory_bytes cenv fty` >>
  qabbrev_tac `A = mk_inst s2.cs_next_id ALLOCA [Lit (n2w sz)] [p]` >>
  `MEM A (fn_insts func)` by
    (qpat_assum `lookup_block s2.cs_current_bb _ = _`
       (mp_tac o MATCH_MP
          (REWRITE_RULE [GSYM AND_IMP_INTRO] lookup_block_fn_insts)) >>
     disch_then irule >> simp[Abbr `A`]) >>
  `not_local_ptr cenv es2.scopes p` by
    (qpat_assum `p = _` SUBST1_TAC >> irule reserved_fresh_not_local >>
     qexists_tac `s2` >> simp[]) >>
  `A.inst_opcode = ALLOCA /\ A.inst_operands = [Lit (n2w sz)] /\
   A.inst_outputs = [p] /\ A.inst_id = s2.cs_next_id` by
    simp[Abbr `A`, venomInstTheory.mk_inst_def] >>
  `step_inst_base A t2 = exec_alloca A t2 (n2w sz : bytes32)` by
    simp[Abbr `A`, step_inst_base_def, venomInstTheory.mk_inst_def] >>
  `?sA. exec_alloca A t2 (n2w sz : bytes32) = OK sA` by
    (simp[exec_alloca_def] >> BasicProvers.every_case_tac >> simp[]) >>
  `step_inst_base A t2 = OK sA` by fs[] >>
  qspecl_then [`func`, `cenv`, `cx`, `es2`, `t2`, `A`, `p`,
               `n2w sz : bytes32`, `sA`] mp_tac stmt_state_rel_exec_alloca >>
  impl_tac >- fs[] >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `wp` strip_assume_tac)) >>
  `sA.vs_current_bb = t2.vs_current_bb /\ sA.vs_inst_idx = t2.vs_inst_idx /\
   ~sA.vs_halted /\ (!x. x <> p ==> lookup_var x sA = lookup_var x t2) /\
   (!a b. FLOOKUP t2.vs_allocas a = SOME b ==>
          FLOOKUP sA.vs_allocas a = SOME b)` by
    (qspecl_then [`A`, `t2`, `n2w sz : bytes32`, `sA`, `p`]
       mp_tac exec_alloca_frame >>
     impl_tac >- simp[] >> simp[]) >>
  `w2n (n2w sz : bytes32) = sz` by fs[] >>
  `FLOOKUP sA.vs_allocas s2.cs_next_id = SOME (w2n wp, sz)` by
    (qpat_x_assum `FLOOKUP sA.vs_allocas A.inst_id = _` mp_tac >>
     qpat_assum `A.inst_id = _` (fn th => REWRITE_TAC [th]) >>
     qpat_assum `w2n (n2w sz) = sz` (fn th => REWRITE_TAC [th])) >>
  qspecl_then [`ctx`, `func`, `t2`, `sA`, `A`, `s2.cs_current_insts`,
               `s2.cs_current_bb`, `entry_lbl`, `s2.cs_next_id + 1`]
    mp_tac for_start_block >>
  impl_tac >- fs[] >> strip_tac >>
  suspend "entry"
QED

Resume compile_for_range_checked_frag[entry]:
  `!k. not_fresh_at s2 (STRING #"%" (toString (s2.cs_next_var + k))) ==> F`
    by (rw[not_fresh_at_def] >> qexists `s2.cs_next_var + k` >> simp[]) >>
  `!x. op1 = Var x \/ op2 = Var x ==>
       x <> p /\ ~MEM x [cv; rv; g1; z1; g2; z2; ev]` by
    (rpt gen_tac >> strip_tac >>
     `not_fresh_at s2 x` by
       (gvs[] >> TRY (irule not_fresh_at_mono >> qexists `s1` >> simp[])) >>
     fs[not_fresh_at_def] >> rw[] >> first_x_assum irule >> simp[]) >>
  `eval_operand op1 (jump_to entry_lbl sA) = SOME (i2w n1) /\
   eval_operand op2 (jump_to entry_lbl sA) = SOME (i2w n2)` by
    (conj_tac
     >- (qspecl_then [`op1`, `t2`, `sA`, `entry_lbl`, `i2w n1`] mp_tac
           eval_operand_jump_to_frame >>
         impl_tac >- (simp[] >> metis_tac[]) >> simp[]) >>
     qspecl_then [`op2`, `t2`, `sA`, `entry_lbl`, `i2w n2`] mp_tac
       eval_operand_jump_to_frame >>
     impl_tac >- (simp[] >> metis_tac[]) >> simp[]) >>
  qspecl_then [`ctx`, `func`, `jump_to entry_lbl sA`, `entry_lbl`, `cond_lbl`,
               `op1`, `op2`, `i2w n1`, `i2w n2`,
               `if is_signed_type fty then SGT else GT`,
               `cv`, `rv`, `g1`, `z1`, `g2`, `z2`, `ev`, `bound`,
               `s2.cs_next_id + 2`]
    mp_tac for_entry_checked_block >>
  impl_tac
  >- (simp[jump_to_def] >> rw[] >>
      simp[ALL_DISTINCT, ASCIInumbersTheory.toString_inj] >> metis_tac[]) >>
  strip_tac >>
  qspecl_then [`get_tenv cx`, `fty`, `tyv`, `n1`, `n2`] mp_tac
    range_end_words >>
  impl_tac >- fs[] >>
  strip_tac >>
  `w2n (n2w bound : bytes32) = bound` by simp[] >>
  `(if (if is_signed_type fty then SGT else GT) = SGT
    then word_gt (i2w n1 : bytes32) (i2w n2)
    else w2n (i2w n1 : bytes32) > w2n (i2w n2 : bytes32)) <=> n2 < n1` by
    (qpat_x_assum `(if is_signed_type fty then _ else _) <=> _`
       (SUBST1_TAC o SYM) >>
     Cases_on `is_signed_type fty` >> simp[]) >>
  qpat_x_assum `range_outcome _ _ _ _ _ _ _ _ _ _`
    (DISJ_CASES_THEN2 assume_tac strip_assume_tac o
     REWRITE_RULE [range_outcome_def, DISJ_ASSOC])
  >- suspend "range_error" >>
  suspend "loop"
QED

(* The range's runtime errors: the entry block's ASSERT reverts, after the
   ends' code. *)
Resume compile_for_range_checked_frag[range_error]:
  qpat_x_assum `(n2 < n1 /\ _) \/ _` strip_assume_tac >>
  qpat_x_assum `_ ==> ?fuel t. run_from fuel ctx func _ = Abort _ _`
    mp_tac >> simp[integerTheory.INT_NOT_LT] >> strip_tac >>
  disj2_tac >>
  qpat_x_assum `!fuel rr. run_from fuel ctx func (jump_to entry_lbl sA) = rr /\ _ ==> _`
    (qspecl_then [`fuel`, `Abort Revert_abort t`] mp_tac) >>
  simp[] >> strip_tac >> rename1 `run_from f2 ctx func t2 = _` >>
  qpat_x_assum `!fuel. (!e. run_from fuel ctx func t2 <> Error e) ==> _`
    (qspec_then `f2` mp_tac) >> simp[] >> strip_tac >>
  rename1 `run_from f1 ctx func t1 = _` >>
  qpat_x_assum `!fuel. (!e. run_from fuel ctx func t1 <> Error e) ==> _`
    (qspec_then `f1` mp_tac) >> simp[] >> strip_tac >>
  rename1 `run_from f0 ctx func s0 = _` >> qexists_tac `f0` >>
  simp[exit_result_def, stmt_exit_def, expr_exit_def]
QED

Resume compile_for_range_checked_frag[loop]:
  `~(n2 < n1) /\ ~(Num (n2 - n1) > bound)` by
    simp[integerTheory.INT_NOT_LT, arithmeticTheory.NOT_GREATER] >>
  qpat_x_assum `_ /\ _ ==> ?vs. _` mp_tac >> impl_tac >- simp[] >>
  disch_then (qx_choose_then `vs` strip_assume_tac) >>
  qabbrev_tac `cc = jump_to cond_lbl (jump_to entry_lbl sA with vs_vars := vs)` >>
  (* the variables *)
  `sb0.cs_next_var <= sb1.cs_next_var` by metis_tac[] >>
  `dv <> p /\ dv <> cv /\ dv <> ev /\ nv <> cv /\ nv <> ev /\ nv <> p /\
   cv <> ev /\ cv <> p /\ ev <> p` by (fs[] >> rw[] >> fs[]) >>
  `!x. ~MEM x [cv; rv; g1; z1; g2; z2; ev] ==>
       lookup_var x cc = lookup_var x sA` by
    (gen_tac >> strip_tac >> simp[Abbr `cc`] >>
     qpat_x_assum `!x. ~MEM x _ ==> _` drule >>
     simp[lookup_var_def, jump_to_def]) >>
  `(!scs. not_local_ptr cenv scs cv) /\ (!scs. not_local_ptr cenv scs ev) /\
   (!scs. not_local_ptr cenv scs dv) /\ (!scs. not_local_ptr cenv scs nv)` by
    (rpt conj_tac >> gen_tac >>
     qpat_assum `cv = _` SUBST1_TAC >> qpat_assum `ev = _` SUBST1_TAC >>
     qpat_assum `dv = _` SUBST1_TAC >> qpat_assum `nv = _` SUBST1_TAC >>
     irule reserved_fresh_not_local >> qexists_tac `s2` >> fs[]) >>
  `local_ptrs_reserved bc sb0` by
    (irule local_ptrs_reserved_next_var >>
     qexists_tac `s2 with cs_next_var := s2.cs_next_var + 1` >> simp[] >>
     irule declare_local_reserved >> metis_tac[]) >>
  `!scs. lookup_scopes id scs = NONE ==> not_local_ptr bc (FEMPTY::scs) p` by
    (rpt strip_tac >>
     `not_local_ptr cenv (FEMPTY::scs) p` by
       (qpat_assum `p = _` SUBST1_TAC >> irule reserved_fresh_not_local >>
        qexists_tac `s2` >> simp[]) >>
     fs[not_local_ptr_def] >> rpt strip_tac >>
     `name <> id` by
       (strip_tac >> qpat_x_assum `lookup_scopes _ (FEMPTY::_) = _` mp_tac >>
        simp[lookup_scopes_def]) >>
     metis_tac[]) >>
  suspend "state"
QED

Resume compile_for_range_checked_frag[state]:
  `!q. not_fresh_at s2 q ==> ~MEM q [cv; rv; g1; z1; g2; z2; ev] /\ q <> p` by
    (rpt strip_tac >> fs[not_fresh_at_def] >> rw[] >>
     first_x_assum irule >> simp[]) >>
  `stmt_state_rel func cenv cx es2 cc` by
    (simp[Abbr `cc`, stmt_state_rel_jump_to] >>
     irule stmt_state_rel_vars_frame >> simp[stmt_state_rel_jump_to] >>
     qx_genl_tac [`nm`, `en`, `q`, `qsz`] >> strip_tac >>
     `not_fresh_at s2 q` by
       (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
     qpat_assum `!q. not_fresh_at s2 q ==> _` (drule_then strip_assume_tac) >>
     qpat_x_assum `!x. ~MEM x _ ==> _` drule >>
     fs[lookup_var_def, jump_to_def]) >>
  `lookup_var p cc = SOME wp` by
    (`~MEM p [cv; rv; g1; z1; g2; z2; ev]` by (fs[] >> rw[] >> fs[]) >>
     qpat_x_assum `!x. ~MEM x _ ==> lookup_var x cc = _` drule >> simp[]) >>
  `FLOOKUP cc.vs_allocas A.inst_id = SOME (w2n wp, sz)` by
    fs[Abbr `cc`, jump_to_def] >>
  `!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
         lookup_var x cc = SOME v` by
    (rpt strip_tac >>
     `not_fresh_at s2 x` by metis_tac[not_fresh_at_mono,
                                     arithmeticTheory.LESS_EQ_TRANS] >>
     `~MEM x [cv; rv; g1; z1; g2; z2; ev] /\ x <> p` by metis_tac[] >>
     metis_tac[]) >>
  `ret_pc_ok cenv sa cc` by
    (qspecl_then [`cenv`, `cenv`, `sa`, `sa`, `s0`, `cc`] mp_tac
       ret_pc_ok_frame >>
     impl_tac >- fs[] >> simp[]) >>
  `!fuel rr. run_from fuel ctx func cc = rr /\ (!e. rr <> Error e) ==>
             ?fuel'. run_from fuel' ctx func s0 = rr` by
    (rpt strip_tac >>
     qpat_x_assum `!fuel rr. run_from fuel ctx func cc = rr /\ _ ==> _`
       drule_all >> disch_then (qx_choose_then `f1` assume_tac) >>
     qpat_x_assum
       `!fuel rr. run_from fuel ctx func (jump_to entry_lbl sA) = rr /\ _ ==> _`
       drule_all >> disch_then (qx_choose_then `f2` assume_tac) >>
     qpat_x_assum `!fuel. (!e. run_from fuel ctx func t2 <> Error e) ==> _`
       (qspec_then `f2` mp_tac) >> simp[] >>
     disch_then (qx_choose_then `f3` assume_tac) >>
     qpat_x_assum `!fuel. (!e. run_from fuel ctx func t1 <> Error e) ==> _`
       (qspec_then `f3` mp_tac) >> simp[] >>
     disch_then (qx_choose_then `f4` assume_tac) >>
     qexists_tac `f4` >> simp[]) >>
  `!a b. FLOOKUP s0.vs_allocas a = SOME b ==> FLOOKUP cc.vs_allocas a = SOME b`
    by simp[Abbr `cc`, jump_to_def] >>
  `cc.vs_current_bb = cond_lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted`
    by (simp[Abbr `cc`, jump_to_def] >> fs[jump_to_def]) >>
  `lookup_var cv cc = SOME (i2w (n1 + &0))` by
    (simp[Abbr `cc`] >> qpat_x_assum `lookup_var cv _ = _` mp_tac >>
     simp[lookup_var_def, jump_to_def]) >>
  `lookup_var ev cc = SOME (i2w n2)` by
    (simp[Abbr `cc`] >> qpat_x_assum `lookup_var ev _ = _` mp_tac >>
     simp[lookup_var_def, jump_to_def, wordsTheory.WORD_SUB_ADD2]) >>
  suspend "run_loop"
QED

Resume compile_for_range_checked_frag[run_loop]:
  `type_memory_size tyv = 32` by
    (qspecl_then [`get_tenv cx`, `fty`, `tyv`] mp_tac
       is_int_type_memory_size >> simp[]) >>
  `!j. j < Num (n2 - n1) ==> value_has_type tyv (IntV (n1 + &j))` by
    (qspecl_then [`tyv`, `n1`, `n2`] mp_tac range_value_has_type >> simp[]) >>
  (* the body's judgment and P's preservation as for_loop takes them *)
  `!ei j r9 es9.
     P ei /\ lookup_scopes id ei.scopes = NONE /\ j < Num (n2 - n1) /\
     eval_stmts cx stmts
       (ei with scopes :=
          (FEMPTY |+ (id, <| assignable := F; type := tyv;
                             value := IntV (n1 + &j); popped := [] |>)) :: ei.scopes) =
       (r9, es9) ==>
     stmt_frag ctx func cx (InLoop exit_lbl incr_lbl) RetQ bc
       (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts)
       (ei with scopes :=
          (FEMPTY |+ (id, <| assignable := F; type := tyv;
                             value := IntV (n1 + &j); popped := [] |>)) :: ei.scopes)
       r9 es9` by
    (rpt strip_tac >>
     qpat_x_assum `!st0 c st1 ex inc ei n1 j r2 es2. _`
       (qspecl_then [`s2`, `bc`, `s2 with cs_next_var := s2.cs_next_var + 1`,
                     `exit_lbl`, `incr_lbl`, `ei`, `n1`, `j`, `r9`, `es9`]
          mp_tac) >>
     simp[]) >>
  `!ei j r9 es9 sc9 rest9.
     P ei /\ lookup_scopes id ei.scopes = NONE /\ j < Num (n2 - n1) /\
     eval_stmts cx stmts
       (ei with scopes :=
          (FEMPTY |+ (id, <| assignable := F; type := tyv;
                             value := IntV (n1 + &j); popped := [] |>)) :: ei.scopes) =
       (r9, es9) /\
     (r9 = INL () \/ r9 = INR ContinueException) /\
     es9.scopes = sc9 :: rest9 ==>
     P (es9 with scopes := rest9)` by
    (rpt strip_tac >>
     qpat_x_assum `!ei n1 j r2 es2 sc rest. _`
       (qspecl_then [`ei`, `n1`, `j`, `r9`, `es9`, `sc9`, `rest9`] mp_tac) >>
     simp[]) >>
  qspecl_then [`Num (n2 - n1)`, `P`, `ctx`, `func`, `cenv`, `bc`, `cx`, `lctx`,
               `RetQ`, `ty`, `stmts`, `id`, `tyv`, `p`, `sz`, `A`, `cv`, `ev`,
               `dv`, `nv`, `n1`, `n2`, `cond_lbl`, `exit_lbl`, `body_lbl`,
               `incr_lbl`, `s2.cs_next_id + 12`, `s2.cs_next_id + 13`,
               `s2.cs_next_id + 14`, `bbb`, `sj.cs_next_id`, `sj.cs_next_id + 1`,
               `sj.cs_next_id + 2`, `sb0`, `sb1`, `sj`, `sa`, `0`, `es2`, `cc`,
               `wp`, `res`, `es'`] mp_tac for_loop >>
  impl_tac
  >- (REWRITE_TAC [for_code_def] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      TRY (simp[block_is_terminated_def, venomInstTheory.mk_inst_def,
                is_terminator_def] >> NO_TAC) >>
      TRY (fs[] >> NO_TAC) >>
      TRY (simp[not_fresh_at_def] >> NO_TAC) >>
      rw[not_fresh_at_def] >>
      TRY (first_x_assum (qspec_then `sj.cs_next_var` mp_tac)) >> simp[]) >>
  strip_tac
  >- (rename1 `s9.vs_current_bb = exit_lbl` >> disj1_tac >>
      qexists_tac `s9` >> qexists_tac `cenv` >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >- simp[stmt_lands_def]
      >- simp[block_is_terminated_def]
      >- simp[cenv_top_ext_refl]
      >- metis_tac[]
      >- metis_tac[] >>
      rpt strip_tac >> metis_tac[]) >>
  disj2_tac >> rename1 `exit_result r9` >>
  drule exit_result_not_error >> strip_tac >> metis_tac[]
QED

Finalise compile_for_range_checked_frag

(* Integrity gate for the forced iterator boundary and checked-range consumer. *)
val () = List.app (fn th =>
  let val (ors, axs) = Tag.dest_tag (Thm.tag th)
  in if null axs andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") ors
     then print "RANGE_FORCE_AUDIT OK\n"
     else raise Fail "forced range inherited admission"
  end) [eval_iterator_range_forced, eval_stmt_for_range_cases,
        compile_for_range_checked_frag];
