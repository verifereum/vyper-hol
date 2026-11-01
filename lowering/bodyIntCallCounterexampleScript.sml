(* Concrete witness checks for the unconstrained internal-call metadata. *)
Theory bodyIntCallCounterexample
Ancestors
  bodyIntCallInterfaces bodySimStmtCases bodySimExprCases
  bodySim vyperTypeCallGraph vyperAST vyperContext vyperState vyperInterpreter

Theorem scalar_return_body_ih:
  !cx.
    body_stmts_ok cx
      [Return (SOME (Literal (BaseT (UintT 256)) (IntL 1)))]
Proof
  gen_tac >> irule body_stmts_cons_case >>
  conj_tac >- simp[body_stmts_nil_case] >>
  irule body_return_case >> irule body_expr_ok_intro >>
  simp[int_calls_expr_def]
QED

Theorem scalar_runtime_lowers_probe:
  IS_SOME (lower_vyper_runtime_unit
    [FunctionDecl Internal Pure F F "f" [] [] (BaseT (UintT 256))
       [Return (SOME (Literal (BaseT (UintT 256)) (IntL 1)))]]
    <| rpol_target := all_capabilities;
       rpol_frontend_dispatch := Linear;
       rpol_final_assembly := FAP_Optimize |> )
Proof
  EVAL_TAC >> simp[return_def]
QED

Theorem scalar_source_call_probe:
  eval_expr
    (empty_evaluation_context with sources :=
      [(0w, [(NONE,
        [FunctionDecl Internal Pure F F "f" [] [] (BaseT (UintT 256))
          [Return (SOME (Literal (BaseT (UintT 256)) (IntL 1)))]] )])])
    (Call (BaseT (UintT 256)) (IntCall (NONE,"f")) [] NONE)
    (empty_state with outcomes := SOME []) =
  (INL (Value (IntV 1)), empty_state with outcomes := SOME [])
Proof
  EVAL_TAC >> simp[return_def]
QED
