Theory forPtrRangeTail
Ancestors
  forPtrCheckedFrame forPtrRangeLoop forPtrForcedEndpoint forPtrAllocationGhost
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
