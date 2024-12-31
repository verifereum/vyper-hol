open HolKernel boolLib bossLib Parse intLib;
open finite_mapTheory;
open vyperAstTheory vyperVmTheory;

val () = new_theory "vyperTest";

Overload uint256 = “BaseT (UintT (n2w (256 DIV 8)))”

Definition test_if_control_flow_ast_def:
  test_if_control_flow_ast =
  FunctionDef "foo" [External] [] uint256
  [
    AnnAssign "a" uint256 (Literal (IntL 1));
    If (Compare (Name "a") Eq (Literal (IntL 1)))
    [
      Assign (BaseTarget (NameTarget "a")) (Literal (IntL 2))
    ]
    [
      Assign (BaseTarget (NameTarget "a")) (Literal (IntL 3))
    ];
    Return (SOME (BinOp (Name "a") Add (Literal (IntL 42))))
  ]
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
          initial_function_context_def, assign_subscripts_def,
          evaluate_exps_def, assign_target_def, set_variable_def,
          evaluate_target_def, evaluate_base_target_def,
          evaluate_cmp_def, evaluate_literal_def,
          evaluate_binop_def, lookup_scopes_def,
          find_containing_scope_def,
          raise_def, FLOOKUP_UPDATE]
QED

Definition test_for_control_flow_ast_def:
  test_for_control_flow_ast =
  FunctionDef "foo" [External] [] uint256
  [
     AnnAssign "a" (DynArrayT uint256 10)
       (ArrayLit [Literal (IntL 1); Literal (IntL 2); Literal (IntL 3)]);
     AnnAssign "counter" uint256 (Literal (IntL 0));
     For "i" uint256 (Name "a")
     [ AugAssign "counter" Add (Name "i") ];
     Return (SOME (Name "counter"))
  ]
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
       set_variable_def, evaluate_base_target_def, evaluate_target_def,
       evaluate_exps_def, assign_target_def,
       evaluate_cmp_def, evaluate_literal_def,
       evaluate_binop_def, push_scope_def, lookup_scopes_def,
       find_containing_scope_def, pop_scope_def,
       raise_def, FLOOKUP_UPDATE]
QED

Definition test_array_assign_ast_def:
  test_array_assign_ast =
  FunctionDef "foo" [External] [] uint256
  [
    AnnAssign "bar" (DynArrayT uint256 10)
      (ArrayLit [Literal (IntL 1); Literal (IntL 2)]);
    Assign (BaseTarget (SubscriptTarget (NameTarget "bar") (Literal (IntL 0))))
      (Literal (IntL 3));
    Return (SOME (BinOp (BinOp (Subscript (Name "bar") (Literal (IntL 0))) Add
                               (Subscript (Name "bar") (Literal (IntL 1)))) Add
                        (Literal (IntL 42))))
  ]
End

Theorem evaluate_test_array_assign_body:
  execute_stmts 10
    (function_body test_array_assign_ast)
    initial_function_context = result_ctx
  ==>
  result_ctx.raised = SOME (ReturnException (IntV 47))
Proof
  rw[function_body_def, test_array_assign_ast_def]
  \\ simp[execute_stmts_def,
       initial_function_context_def, new_variable_def,
       set_variable_def, evaluate_base_target_def, evaluate_target_def,
       evaluate_exps_def, assign_target_def, add_subscript_def,
       assign_subscripts_def, extract_elements_def, replace_elements_def,
       evaluate_cmp_def, evaluate_literal_def, integer_index_def,
       evaluate_binop_def, push_scope_def, lookup_scopes_def,
       find_containing_scope_def, pop_scope_def,
       raise_def, FLOOKUP_UPDATE]
QED

(* TODO: evaluate a list of toplevels to a contract context (globals + functions) *)
(* TODO: make the tests evaluate an external call in a given context *)

Definition test_storage_array_assign_ast_def:
  test_storage_array_assign_ast = [
    VariableDecl "a" (DynArrayT uint256 10) Private Storage;
    FunctionDef "foo" [External] [] uint256 [
      Assign (BaseTarget (GlobalNameTarget "a"))
        (ArrayLit [Literal (IntL 1); Literal (IntL 2)]);
      Assign (BaseTarget
               (SubscriptTarget (GlobalNameTarget "a")
                                (Literal (IntL 0))))
             (Literal (IntL 3));
      Return (SOME (BinOp
        (Subscript (GlobalName "a") (Literal (IntL 0)))
        Add
        (Subscript (GlobalName "a") (Literal (IntL 1)))))
    ]
  ]
End

val () = export_theory();
