open HolKernel boolLib bossLib Parse intLib wordsLib cv_transLib;
open numeralTheory arithmeticTheory finite_mapTheory;
open vyperAstTheory vyperVmTheory;

val () = new_theory "vyperTest";

Overload uint256 = “BaseT (UintT (n2w 32 (* 256 DIV 8 *)))”
Overload intlit = “λi. Literal (IntL i)”

(*
  rw[external_call_def,
     test_for_control_flow_ast_def,
     lookup_external_function_def, bind_arguments_def,
     initial_execution_context_def, initial_globals_def,
     initial_function_context_def ]
     rw[Once numeral_funpow, Once step_stmt_def, set_stmt_def,
        step_expr_def, exception_raised_def, new_variable_def,
        set_variable_def, find_containing_scope_def,
        evaluate_literal_def, evaluate_binop_def, evaluate_cmp_def,
        step_target_def, step_base_target_def, assign_target_def,
        assign_subscripts_def, string_to_num_def, numposrepTheory.l2n_def,
        lookup_scopes_def, next_stmt_def, raise_def,
        push_loop_def, next_iteration_def, pop_loop_def,
        Once pop_call_def, FLOOKUP_UPDATE]
*)

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

val () = cv_trans_deep_embedding EVAL test_if_control_flow_ast_def;

Theorem test_if_control_flow:
  external_call "foo" [] test_if_control_flow_ast
  = INL (IntV 44)
Proof
  CONV_TAC(LAND_CONV cv_eval) \\ rw[]
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

val () = cv_trans_deep_embedding EVAL test_for_control_flow_ast_def;

Theorem test_for_control_flow:
  external_call "foo" [] test_for_control_flow_ast
  = INL (IntV 6)
Proof
  CONV_TAC(LAND_CONV cv_eval) \\ rw[]
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

val () = cv_trans_deep_embedding EVAL test_array_assign_ast_def;

Theorem test_array_assign:
  external_call "foo" [] test_array_assign_ast
  = INL (IntV 47)
Proof
  CONV_TAC(LAND_CONV cv_eval) \\ rw[]
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

val () = cv_trans_deep_embedding EVAL test_storage_array_assign_ast_def;

Theorem test_storage_array_assign:
  external_call "foo" [] test_storage_array_assign_ast
  = INL (IntV 5)
Proof
  CONV_TAC(LAND_CONV cv_eval) \\ rw[]
QED

Definition test_internal_call_ast_def:
  test_internal_call_ast = [
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

val () = cv_trans_deep_embedding EVAL test_internal_call_ast_def;

Theorem test_internal_call:
  external_call "foo" [] test_internal_call_ast
  = INL (IntV 12)
Proof
  CONV_TAC(LAND_CONV cv_eval) \\ rw[]
QED

Definition test_internal_call_without_return_ast_def:
  test_internal_call_without_return_ast = [
    VariableDecl "a" uint256 Private Storage;
    FunctionDef "bar" Internal [] VoidT [
      Assign (BaseTarget (GlobalNameTarget "a")) (intlit 42)
    ];
    FunctionDef "foo" External [] uint256 [
      Expr (Call "bar" []);
      Return (SOME (GlobalName "a"))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_internal_call_without_return_ast_def;

Theorem test_internal_call_without_return:
  external_call "foo" [] test_internal_call_without_return_ast
  = INL (IntV 42)
Proof
  CONV_TAC(LAND_CONV cv_eval) \\ rw[]
QED

val () = export_theory();
