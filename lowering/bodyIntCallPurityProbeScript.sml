(* Diagnostic only: supported precompiles are not syntactically pure. *)
Theory bodyIntCallPurityProbe
Ancestors
  supportedExprs supportedExprForms vyperPureExpr vyperInterpreter vyperState

Theorem supported_precompile_not_pure:
  supported_pure_expr []
    (Builtin (BaseT AddressT) ECRecover
      [Literal (BaseT (UintT 256)) (IntL 0);
       Literal (BaseT (UintT 256)) (IntL 0);
       Literal (BaseT (UintT 256)) (IntL 0);
       Literal (BaseT (UintT 256)) (IntL 0)]) /\
  ~pure_expr
    (Builtin (BaseT AddressT) ECRecover
      [Literal (BaseT (UintT 256)) (IntL 0);
       Literal (BaseT (UintT 256)) (IntL 0);
       Literal (BaseT (UintT 256)) (IntL 0);
       Literal (BaseT (UintT 256)) (IntL 0)])
Proof
  EVAL_TAC
QED

(* A successful precompile consumes an oracle outcome, even on success.
   This refutes whole-state equality, not the frozen internal-call case. *)
Theorem successful_precompile_consumes_outcome:
  !st outcome.
    outcome.co_success ==>
    precompile_call_success ECRecover
      (st with outcomes := SOME [outcome]) =
      (INL (), st with outcomes := SOME []) /\
    (st with outcomes := SOME [outcome]) <>
      (st with outcomes := SOME [])
Proof
  simp[precompile_call_success_def, precompile_builtin_def,
       check_def, assert_def, return_def, evaluation_state_component_equality]
QED
