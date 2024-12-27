open HolKernel boolLib bossLib Parse intLib;
open finite_mapTheory;
open vyperAstTheory vyperVmTheory;

val () = new_theory "vyperTest";

Definition test_if_control_flow_ast_def:
  test_if_control_flow_ast =
  FunctionDef "foo" [External] []
  [
    AnnAssign "a" (UintT (n2w (256 DIV 8))) (Literal (IntL 1));
    If (Compare (Name "a") Eq (Literal (IntL 1)))
    [
      Assign "a" (Literal (IntL 2))
    ]
    [
      Assign "a" (Literal (IntL 3))
    ];
    Return (SOME (BinOp (Name "a") Add (Literal (IntL 42))))
  ] (UintT (n2w (256 DIV 8)))
End

Theorem evaluate_test_if_control_flow_body:
  execute_stmts 10
    (function_body test_if_control_flow_ast)
    initial_function_context = result_ctx
  ==>
  result_ctx.raised = SOME (ReturnException (IntV 44))
Proof
  rw[function_body_def, test_if_control_flow_ast_def]
  \\ simp[execute_stmts_def, new_variable_def,
          initial_function_context_def,
          evaluate_exps_def, assign_target_def,
          evaluate_cmp_def, evaluate_literal_def,
          evaluate_binop_def, lookup_scopes_def,
          find_containing_scope_def,
          raise_def, FLOOKUP_UPDATE]
QED

Definition test_for_control_flow_ast_def:
  test_for_control_flow_ast =
  FunctionDef "foo" [External] []
  [
     AnnAssign "a" (DynArrayT (UintT (n2w (256 DIV 8))) 10)
       (ArrayLit [Literal (IntL 1); Literal (IntL 2); Literal (IntL 3)]);
     AnnAssign "counter" (UintT (n2w (256 DIV 8))) (Literal (IntL 0));
     For "i" (UintT (n2w (256 DIV 8))) (Name "a")
     [ OpAssign "counter" Add (Name "i") ];
     Return (SOME (Name "counter"))
  ] (UintT (n2w (256 DIV 8)))
End

Theorem evaluate_test_for_control_flow_body:
  execute_stmts 10
    (function_body test_for_control_flow_ast)
    initial_function_context = result_ctx
  ==>
  result_ctx.raised = SOME (ReturnException (IntV 6))
Proof
  rw[function_body_def, test_for_control_flow_ast_def]
  \\ simp[execute_stmts_def,
       initial_function_context_def, new_variable_def,
       evaluate_exps_def, assign_target_def,
       evaluate_cmp_def, evaluate_literal_def,
       evaluate_binop_def, push_scope_def, lookup_scopes_def,
       find_containing_scope_def, pop_scope_def,
       raise_def, FLOOKUP_UPDATE]
QED

val () = export_theory();
