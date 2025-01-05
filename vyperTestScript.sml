open HolKernel boolLib bossLib Parse intLib;
open numeralTheory arithmeticTheory finite_mapTheory;
open vyperAstTheory vyperVmTheory;

val () = new_theory "vyperTest";

Overload uint256 = “BaseT (UintT (n2w (256 DIV 8)))”
Overload intlit = “λi. Literal (IntL i)”

Definition test_if_control_flow_ast_def:
  test_if_control_flow_ast = [
    FunctionDef "foo" External [] uint256
    [
      AnnAssign "a" uint256 (intlit 1);
      If (Compare (Name "a") Eq (intlit 1))
      [
        Assign (BaseTarget (NameTarget "a")) (intlit 2)
      ]
      [
        Assign (BaseTarget (NameTarget "a")) (intlit 3)
      ];
      Return (SOME (BinOp (Name "a") Add (intlit 42)))
    ]
  ]
End

Theorem test_if_control_flow:
  external_call 21 "foo" [] test_if_control_flow_ast
  = SOME (IntV 44)
Proof
  rw[external_call_def,
     test_if_control_flow_ast_def,
     lookup_external_function_def, bind_arguments_def,
     initial_execution_context_def, initial_globals_def,
     initial_function_context_def ]
  \\ ntac 22 (
     rw[Once numeral_funpow, Once step_stmt_def, set_stmt_def,
        step_expr_def, exception_raised_def, new_variable_def,
        set_variable_def, find_containing_scope_def,
        evaluate_literal_def, evaluate_binop_def, evaluate_cmp_def,
        step_target_def, step_base_target_def, assign_target_def,
        assign_subscripts_def,
        lookup_scopes_def, next_stmt_def, raise_def,
        Once pop_call_def, FLOOKUP_UPDATE]
     )
QED

Definition test_for_control_flow_ast_def:
  test_for_control_flow_ast = [
    FunctionDef "foo" External [] uint256
    [
       AnnAssign "a" (DynArrayT uint256 10)
         (ArrayLit [intlit 1; intlit 2; intlit 3]);
       AnnAssign "counter" uint256 (intlit 0);
       For "i" uint256 (Name "a")
       [ AugAssign "counter" Add (Name "i") ];
       Return (SOME (Name "counter"))
    ]
  ]
End

Theorem test_for_control_flow:
  external_call 10 "foo" [] test_for_control_flow_ast
  = SOME (ReturnException (IntV 6))
Proof
  rw[external_call_def,
     test_for_control_flow_ast_def,
     lookup_external_function_def, bind_arguments_def,
     initial_execution_context_def, initial_globals_def,
     initial_function_context_def ]
  \\ execute_tac
QED

Definition test_array_assign_ast_def:
  test_array_assign_ast = [
    FunctionDef "foo" External [] uint256
    [
      AnnAssign "bar" (DynArrayT uint256 10)
        (ArrayLit [intlit 1; intlit 2]);
      Assign (BaseTarget (SubscriptTarget (NameTarget "bar") (intlit 0)))
        (intlit 3);
      Return (SOME (BinOp (BinOp (Subscript (Name "bar") (intlit 0)) Add
                                 (Subscript (Name "bar") (intlit 1))) Add
                          (intlit 42)))
    ]
  ]
End

Theorem test_array_assign:
  external_call 10 "foo" [] test_array_assign_ast
  = SOME (ReturnException (IntV 47))
Proof
  rw[external_call_def,
     test_array_assign_ast_def,
     lookup_external_function_def, bind_arguments_def,
     initial_execution_context_def, initial_globals_def,
     initial_function_context_def ]
  \\ execute_tac
QED

Definition test_storage_array_assign_ast_def:
  test_storage_array_assign_ast = [
    VariableDecl "a" (DynArrayT uint256 10) Private Storage;
    FunctionDef "foo" External [] uint256 [
      Assign (BaseTarget (GlobalNameTarget "a"))
        (ArrayLit [intlit 1; intlit 2]);
      Assign (BaseTarget
               (SubscriptTarget (GlobalNameTarget "a")
                                (intlit 0)))
             (intlit 3);
      Return (SOME (BinOp
        (Subscript (GlobalName "a") (intlit 0))
        Add
        (Subscript (GlobalName "a") (intlit 1))))
    ]
  ]
End

Theorem test_storage_array_assign:
  external_call 10 "foo" [] test_storage_array_assign_ast
  = SOME (ReturnException (IntV 5))
Proof
  rw[external_call_def,
     test_storage_array_assign_ast_def,
     lookup_external_function_def, bind_arguments_def,
     initial_execution_context_def, initial_globals_def,
     initial_function_context_def ]
  \\ execute_tac
QED

Definition test_internal_call_ast_def:
  test_internal_call = [
    FunctionDef "bar" Internal [] uint256 [
      AnnAssign "a" (DynArrayT uint256 10)
        (ArrayLit [intlit 1; intlit 2; intlit 3]);
      AnnAssign "counter" uint256 (intlit 0);
      For "i" uint256 (Name "a") [
        AugAssign "counter" Add (Name "i")
      ];
      Return (SOME (Name "counter"))
    ];
    FunctionDef "foo" External [] uint256 [
      AnnAssign "a" (DynArrayT uint256 10)
        (ArrayLit [intlit 1; intlit 2; intlit 3]);
      AnnAssign "counter" uint256 (intlit 0);
      For "i" uint256 (Name "a") [
        AugAssign "counter" Add (Name "i")
      ];
      Return (SOME (BinOp
        (Name "counter") Add
        (Call "bar" [])))
    ]
  ]
End

val () = export_theory();
