(* Actual CPS witness and repaired direct CV execution gate.  The historical
   failed tactic is retained below as provenance; active CV gates now pass. *)
Theory vyperExtCallCpsEquivalenceTest
Ancestors
  vyperExtCallConsumptionTest vyperSmallStep[ignore_grammar]
  extCallOracle[ignore_grammar] vyperCallOutcome[ignore_grammar]
  vyperInterpreter vyperState vyperContext vyperABI vyperAST vyperValue
  vyperValueOperation list finite_map words vfmTypes pair
Libs wordsLib cv_transLib

(* Historical cpscv3 failure: cv_eval returned a conditional conversion before
   cont_pre_eval_expr_cps was registered, causing dest_eq "not an =".
Proof
  simp[counter_expr_def, counter_state_def, counter_outcome_def,
       counter_request_def, counter_calldata, failed_outcome_def,
       empty_state_def, call_outcome_request_def] >>
  CONV_TAC cv_eval
QED
*)
Theorem activated_CPS_consumes_counterexample:
  vyperSmallStep$fromtvk (vyperSmallStep$cont
    (vyperSmallStep$eval_expr_cps empty_evaluation_context counter_expr counter_state
      vyperSmallStep$DoneK)) =
    (INR (Error (RuntimeError "ExtCall reverted")),
     counter_state with <|outcomes := SOME []; requests := [counter_request]|>)
Proof
  simp[GSYM eval_expr_eq_cont_cps, activated_ExtCall_consumes_counterexample]
QED

(* Restored original direct execution gate, not the equivalence witness above. *)
Theorem activated_CPS_CV_consumes_counterexample:
  vyperSmallStep$fromtvk (vyperSmallStep$cont
    (vyperSmallStep$eval_expr_cps empty_evaluation_context counter_expr counter_state
      vyperSmallStep$DoneK)) =
    (INR (Error (RuntimeError "ExtCall reverted")),
     counter_state with <|outcomes := SOME []; requests := [counter_request]|>)
Proof
  simp[counter_expr_def, counter_state_def, counter_outcome_def,
       counter_request_def, counter_calldata, failed_outcome_def,
       empty_state_def, call_outcome_request_def] >>
  CONV_TAC cv_eval
QED

(* CV executes the CPS machine; no big-step equivalence rewrite is used. *)
Definition cps_failure_observations_def:
  cps_failure_observations =
    let r = vyperSmallStep$fromtvk (vyperSmallStep$cont
      (vyperSmallStep$eval_expr_cps empty_evaluation_context
        (Call (BaseT (UintT 256)) (ExtCall T ("f",[],BaseT (UintT 256)))
          [Literal (BaseT AddressT) (BytesL (REPLICATE 19 0w ++ [9w]))] NONE)
        (empty_state with outcomes := SOME
          [extCallOracle$failed_outcome
            (vyperCallOutcome$call_outcome_request 9w [] NONE empty_state)])
        vyperSmallStep$DoneK)) in
    FST r = INR (Error (RuntimeError "ExtCall reverted")) /\
    (SND r).outcomes = SOME [] /\
    MAP (λrq. (rq.cr_target,rq.cr_value,rq.cr_data,rq.cr_static))
      (SND r).requests = [(9w,0,[38w;18w;31w;240w],T)] /\
    (SND r).immutables = [] /\ (SND r).logs = [] /\ (SND r).scopes = []
End
val () = cv_auto_trans cps_failure_observations_def;

Theorem activated_CPS_CV_failure_observations:
  cps_failure_observations
Proof
  CONV_TAC cv_eval
QED
