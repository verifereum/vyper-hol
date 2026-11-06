Theory forPtrRangeTail
Ancestors
  forPtrCheckedFrame forPtrRangeChecked forPtrRangeLoop forPtrForcedEndpoint forPtrAllocationGhost
  stmtSimForRange stmtSimForParts stmtSimForLoop stmtSimProps
  bodyPtrDefs stmtFragPtr gasSummaryComposePtr gasOutcomeInitialObsPtr
  vyperInterpreter vyperState vyperValue vyperValueOperation
  integer_word venomState venomExecSemantics finite_map fragGasPathPtr fragExec exprSimDefs
Libs monadsyntax intLib

(* S1's source normalization is local to its range theory. *)
Theorem for_checked_range_tail_action:
  (do rl <- lift_sum (get_range_limits (IntV n1) (IntV n2));
      check (compatible_bound (Dynamic bound) (SND rl)) "For too long";
      eval_for cx tyv id stmts
        (GENLIST (\j. IntV (FST rl + &j)) (SND rl)) od) =
  if n1 <= n2 then
    if Num (n2-n1) <= bound then
      eval_for cx tyv id stmts
        (GENLIST (\j. IntV (n1 + &j)) (Num (n2-n1)))
    else raise (Error (RuntimeError "For too long"))
  else raise (Error (RuntimeError "no range"))
Proof
  simp[get_range_limits_def, lift_sum_def, check_def, assert_def,
       compatible_bound_def] >> Cases_on `n1 <= n2` >>
  simp[FUN_EQ_THM, bind_def, ignore_bind_def, return_def, raise_def, assert_def] >>
  Cases_on `Num (n2-n1) <= bound` >> simp[return_def, raise_def]
QED

Theorem for_checked_range_test_words:
  is_int_type fty /\ evaluate_type tenv fty = SOME tyv /\
  value_has_type tyv (IntV n1) /\ value_has_type tyv (IntV n2) /\
  bound < dimword (:256) ==>
  ((if (if is_signed_type fty then SGT else GT) = SGT then
       word_gt (i2w n1 : bytes32) (i2w n2)
    else w2n (i2w n1 : bytes32) > w2n (i2w n2 : bytes32)) <=> n2 < n1) /\
  (n1 <= n2 ==>
    Num (n2-n1) < dimword (:256) /\
    (w2n (i2w n2 - i2w n1 : bytes32) > w2n (n2w bound : bytes32) <=>
       ~(Num (n2-n1) <= bound)))
Proof
  strip_tac >> drule_at (Pat `evaluate_type _ _ = _`) range_end_words >>
  disch_then (qspecl_then [`n1`,`n2`] mp_tac) >> simp[] >> strip_tac >>
  Cases_on `is_signed_type fty` >> gvs[]
QED

Theorem for_checked_runtime_error_outcome:
  gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 Gf tf
    (Abort Revert_abort t) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (raise (Error (RuntimeError msg))) (es,s,G,tn) Post
    (\res ee gt r. !tail. stmt_exit_ptr RetQ (ee with gas_obs := tail) res gt r)
Proof
  strip_tac >> rewrite_tac[gas_outcome_ptr_def] >>
  qexists_tac `[]` >> disj1_tac >> rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INR (Error (RuntimeError msg))`,`es`,`Gf`,`tf`,
                `Abort Revert_abort t`] >>
  simp[gas_marked_exec_ptr_def, raise_def, exit_result_def,
       stmt_exit_ptr_def, expr_exit_def]
QED

(* The checked entry has three semantic branches.  Keep their source/error
   correspondence here so the tail consumer only supplies checked paths and
   the existing loop outcome; no instruction semantics is reopened there. *)
Theorem for_checked_range_tail_compose:
  (~(n1 <= n2) ==>
     ?Gf tf t. gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 Gf tf
       (Abort Revert_abort t)) /\
  (n1 <= n2 /\ ~(Num (n2-n1) <= bound) ==>
     ?Gf tf t. gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 Gf tf
       (Abort Revert_abort t)) /\
  (n1 <= n2 /\ Num (n2-n1) <= bound ==>
     ?Gc tc cc.
       gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 Gc tc (OK cc) /\
       gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
         (eval_for cx tyv id stmts
           (GENLIST (\j. IntV (n1 + &j)) (Num (n2-n1))))
         (es,cc,Gc,tc) Post
         (\res ee gt r. !tail.
           stmt_exit_ptr RetQ (ee with gas_obs := tail) res gt r)) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (do rl <- lift_sum (get_range_limits (IntV n1) (IntV n2));
        check (compatible_bound (Dynamic bound) (SND rl)) "For too long";
        eval_for cx tyv id stmts
          (GENLIST (\j. IntV (FST rl + &j)) (SND rl)) od)
    (es,s,G,tn) Post
    (\res ee gt r. !tail.
      stmt_exit_ptr RetQ (ee with gas_obs := tail) res gt r)
Proof
  strip_tac >> rewrite_tac[for_checked_range_tail_action] >>
  Cases_on `n1 <= n2`
  >- (Cases_on `Num (n2-n1) <= bound` >> gvs[]
      >- (irule gas_outcome_ptr_prefix >> goal_assum (drule_at Any) >>
          qexists_tac `0` >> simp[]) >>
      irule for_checked_runtime_error_outcome >> goal_assum (drule_at Any)) >>
  gvs[] >> irule for_checked_runtime_error_outcome >> goal_assum (drule_at Any)
QED

(* Consumer-facing checked entry: the continuation sees only the final map
   and its frame.  Arithmetic failure and checked aborts stay behind this
   boundary, while the continuation can use for_checked_entry_setup. *)
Theorem for_checked_range_entry_outcome_ptr:
  lookup_block ee.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions =
    [mk_inst i ASSIGN [op1] [cv];
     mk_inst (i+1) SUB [op2;op1] [rv];
     mk_inst (i+2) (if is_signed_type fty then SGT else GT) [op1;op2] [g1];
     mk_inst (i+3) ISZERO [Var g1] [z1];
     mk_inst (i+4) ASSERT [Var z1] [];
     mk_inst (i+5) GT [Var rv;Lit (n2w bound)] [g2];
     mk_inst (i+6) ISZERO [Var g2] [z2];
     mk_inst (i+7) ASSERT [Var z2] [];
     mk_inst (i+8) ADD [op1;Var rv] [ev];
     mk_inst (i+9) JMP [Label lbl] []] /\
  ee.vs_inst_idx = 0 /\ ~ee.vs_halted /\ ~ctx_has_dalloca ctx /\
  eval_operand op1 ee = SOME (i2w n1) /\
  eval_operand op2 ee = SOME (i2w n2) /\
  op_taint tn op1 = {} /\ op_taint tn op2 = {} /\
  op_prov G op1 = NONE /\ op_prov G op2 = NONE /\
  ALL_DISTINCT [cv;rv;g1;z1;g2;z2;ev] /\
  (!x. op1 = Var x \/ op2 = Var x ==> ~MEM x [cv;rv;g1;z1;g2;z2;ev]) /\
  is_int_type fty /\ evaluate_type (get_tenv cx) fty = SOME tyv /\
  value_has_type tyv (IntV n1) /\ value_has_type tyv (IntV n2) /\
  bound < dimword (:256) /\
  (!vs. n1 <= n2 /\ Num (n2-n1) <= bound /\
     lookup_var cv (ee with vs_vars := vs) = SOME (i2w n1) /\
     lookup_var ev (ee with vs_vars := vs) = SOME (i2w n2) /\
     (!x. ~MEM x [cv;rv;g1;z1;g2;z2;ev] ==>
       lookup_var x (ee with vs_vars := vs) = lookup_var x ee) ==>
     gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
       (eval_for cx tyv id stmts
         (GENLIST (\j. IntV (n1 + &j)) (Num (n2-n1))))
       (es,jump_to lbl (ee with vs_vars := vs),
        DRESTRICT G (COMPL {cv;rv;g1;z1;g2;z2;ev}),
        tn with t_var := tn.t_var |++
          [(cv,{});(rv,{});(g1,{});(z1,{});(g2,{});(z2,{});(ev,{})]) Post
       (\res ee gt r. !tail.
         stmt_exit_ptr RetQ (ee with gas_obs := tail) res gt r)) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (do rl <- lift_sum (get_range_limits (IntV n1) (IntV n2));
        check (compatible_bound (Dynamic bound) (SND rl)) "For too long";
        eval_for cx tyv id stmts
          (GENLIST (\j. IntV (FST rl + &j)) (SND rl)) od)
    (es,ee,G,tn) Post
    (\res ee gt r. !tail.
      stmt_exit_ptr RetQ (ee with gas_obs := tail) res gt r)
Proof
  strip_tac >>
  mp_tac (Q.INST [`tenv` |-> `get_tenv cx`] (SPEC_ALL for_checked_range_test_words)) >>
  (impl_tac >- simp[]) >> strip_tac >>
  drule_at (Pat `bb.bb_instructions = _`) for_entry_checked_path_ptr >>
  disch_then (drule_at (Pat `eval_operand op1 ee = _`)) >>
  disch_then (drule_at (Pat `eval_operand op2 ee = _`)) >>
  disch_then (drule_at (Pat `lookup_block _ _ = _`)) >>
  disch_then (mp_tac o Q.INST [`D` |-> `cx_dead cx`] o SPEC_ALL) >>
  (impl_tac >- (simp[] >> Cases_on `is_signed_type fty` >> gvs[] >>
    first_assum ACCEPT_TAC)) >>
  strip_tac >> suspend "compose"
QED

Resume for_checked_range_entry_outcome_ptr[compose]:
  irule for_checked_range_tail_compose >> rpt conj_tac
  >- (strip_tac >>
      qpat_x_assum `_ \/ _ ==> _` irule >> disj1_tac >>
      simp[integerTheory.INT_NOT_LT, GSYM integerTheory.INT_NOT_LE])
  >- (strip_tac >> qpat_x_assum `_ \/ _ ==> _` irule >>
      disj2_tac >> gvs[]) >>
  strip_tac >>
  qpat_x_assum `~_ /\ ~_ ==> ?vs. _` mp_tac >>
  simp[integerTheory.INT_NOT_LT, wordsTheory.WORD_SUB_ADD2] >>
  strip_tac >>
  goal_assum (drule_at Any) >> first_x_assum irule >> simp[]
QED
Finalise for_checked_range_entry_outcome_ptr
