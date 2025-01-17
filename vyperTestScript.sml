open HolKernel boolLib bossLib Parse intLib wordsLib cv_transLib;
open numeralTheory arithmeticTheory finite_mapTheory;
open vyperAstTheory vyperVmTheory;

val () = new_theory "vyperTest";

Overload uint256 = “BaseT (UintT (n2w 32 (* 256 DIV 8 *)))”
Overload intlit = “λi. Literal (IntL i)”
Overload "==" = “λe1 e2. Builtin Eq [e1; e2]”
Overload "+" = “λe1 e2. Builtin (Bop Add) [e1; e2]”
Overload len = “λe. Builtin Len [e]”

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
      If (Name "a" == intlit 1)
      [
        Assign (BaseTarget (NameTarget "a")) (intlit 2)
      ]
      [
        Assign (BaseTarget (NameTarget "a")) (intlit 3)
      ];
      Return (SOME (Name "a" + intlit 42))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_if_control_flow_ast_def;

val pair_case_rand = TypeBase.case_rand_of``:'a # 'b``

Theorem test_if_control_flow:
  FST $ external_call
    (load_contract initial_machine_state
       addr test_if_control_flow_ast)
    addr "foo" []
  = INL (IntV 44)
Proof
  rw[external_call_def, load_contract_def, initial_machine_state_def,
     SimpLHS, pair_case_rand]
  \\ CONV_TAC(LAND_CONV cv_eval) \\ rw[]
QED

Definition test_for_control_flow_ast_def:
  test_for_control_flow_ast = [
    FunctionDef "foo" External [] uint256
    [
       AnnAssign "a" (ArrayT uint256 (Dynamic 10))
         (ArrayLit (Dynamic 10) [intlit 1; intlit 2; intlit 3]);
       AnnAssign "counter" uint256 (intlit 0);
       For "i" uint256 (Name "a") 10
       [ AugAssign (NameTarget "counter") Add (Name "i") ];
       Return (SOME (Name "counter"))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_for_control_flow_ast_def;

Theorem test_for_control_flow:
  FST $ external_call
    (load_contract initial_machine_state
       addr test_for_control_flow_ast)
    addr "foo" []
  = INL (IntV 6)
Proof
  rw[external_call_def, load_contract_def, initial_machine_state_def,
     SimpLHS, pair_case_rand]
  \\ CONV_TAC(LAND_CONV cv_eval) \\ rw[]
QED

Definition test_array_assign_ast_def:
  test_array_assign_ast = [
    FunctionDef "foo" External [] uint256
    [
      AnnAssign "bar" (ArrayT uint256 (Dynamic 10))
        (ArrayLit (Dynamic 10) [intlit 1; intlit 2]);
      Assign (BaseTarget (SubscriptTarget (NameTarget "bar") (intlit 0)))
        (intlit 3);
      Return (SOME (Subscript (Name "bar") (intlit 0) +
                    Subscript (Name "bar") (intlit 1) +
                    intlit 42))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_array_assign_ast_def;

Theorem test_array_assign:
  FST $ external_call
   (load_contract initial_machine_state
      addr test_array_assign_ast)
    addr "foo" []
  = INL (IntV 47)
Proof
  rw[external_call_def, load_contract_def, initial_machine_state_def,
     SimpLHS, pair_case_rand]
  \\ CONV_TAC(LAND_CONV cv_eval) \\ rw[]
QED

Definition test_storage_array_assign_ast_def:
  test_storage_array_assign_ast = [
    VariableDecl "a" (ArrayT uint256 (Dynamic 10)) Private Storage;
    FunctionDef "foo" External [] uint256 [
      Assign (BaseTarget (GlobalNameTarget "a"))
        (ArrayLit (Dynamic 10) [intlit 1; intlit 2]);
      Assign (BaseTarget
               (SubscriptTarget (GlobalNameTarget "a")
                                (intlit 0)))
             (intlit 3);
      Return (SOME (Subscript (GlobalName "a") (intlit 0) +
                    Subscript (GlobalName "a") (intlit 1)))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_storage_array_assign_ast_def;

Theorem test_storage_array_assign:
  FST $ external_call
   (load_contract initial_machine_state
      addr test_storage_array_assign_ast)
    addr "foo" []
  = INL (IntV 5)
Proof
  rw[external_call_def, load_contract_def, initial_machine_state_def,
     SimpLHS, pair_case_rand]
  \\ CONV_TAC(LAND_CONV cv_eval) \\ rw[]
QED

Definition test_internal_call_ast_def:
  test_internal_call_ast = [
    FunctionDef "bar" Internal [] uint256 [
      AnnAssign "a" (ArrayT uint256 (Dynamic 10))
        (ArrayLit (Dynamic 10) [intlit 1; intlit 2; intlit 3]);
      AnnAssign "counter" uint256 (intlit 0);
      For "i" uint256 (Name "a") 10 [
        AugAssign (NameTarget "counter") Add (Name "i")
      ];
      Return (SOME (Name "counter"))
    ];
    FunctionDef "foo" External [] uint256 [
      AnnAssign "a" (ArrayT uint256 (Dynamic 10))
        (ArrayLit (Dynamic 10) [intlit 1; intlit 2; intlit 3]);
      AnnAssign "counter" uint256 (intlit 0);
      For "i" uint256 (Name "a") 10 [
        AugAssign (NameTarget "counter") Add (Name "i")
      ];
      Return (SOME (Name "counter" + Call "bar" []))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_internal_call_ast_def;

Theorem test_internal_call:
  FST $ external_call
   (load_contract initial_machine_state
      addr test_internal_call_ast)
    addr "foo" []
  = INL (IntV 12)
Proof
  rw[external_call_def, load_contract_def, initial_machine_state_def,
     SimpLHS, pair_case_rand]
  \\ CONV_TAC(LAND_CONV cv_eval) \\ rw[]
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
  FST $ external_call
   (load_contract initial_machine_state
      addr test_internal_call_without_return_ast)
    addr "foo" []
  = INL (IntV 42)
Proof
  rw[external_call_def, load_contract_def, initial_machine_state_def,
     SimpLHS, pair_case_rand]
  \\ CONV_TAC(LAND_CONV cv_eval) \\ rw[]
QED

Definition test_internal_call_with_args_ast_def:
  test_internal_call_with_args_ast = [
    FunctionDef "baz" Internal [("a", uint256)] uint256 [
      Return (SOME (Name "a"))
    ];
    FunctionDef "bar" Internal [("a", uint256)] uint256 [
      Return (SOME (Name "a" + Call "baz" [intlit 3]))
    ];
    FunctionDef "foo" External [] uint256 [
      AnnAssign "a" uint256 (intlit 1);
      Return (SOME (Name "a" + Call "bar" [intlit 2]))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_internal_call_with_args_ast_def;

Theorem test_internal_call_with_args:
  FST $ external_call
   (load_contract initial_machine_state
      addr test_internal_call_with_args_ast)
    addr "foo" []
  = INL (IntV 6)
Proof
  rw[external_call_def, load_contract_def, initial_machine_state_def,
     SimpLHS, pair_case_rand]
  \\ CONV_TAC(LAND_CONV cv_eval) \\ rw[]
QED

Definition test_internal_call_with_args2_ast_def:
  test_internal_call_with_args2_ast = [
    FunctionDef "baz" Internal [("a", uint256)] uint256 [
      Return (SOME (Name "a"))
    ];
    FunctionDef "bar" Internal [("a", uint256)] uint256 [
      Return (SOME (Call "baz" [intlit 3] + Name "a"))
    ];
    FunctionDef "foo" External [] uint256 [
      AnnAssign "a" uint256 (intlit 1);
      Return (SOME (Call "bar" [intlit 2] + Name "a"))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_internal_call_with_args2_ast_def;

Theorem test_internal_call_with_args2:
  FST $ external_call
   (load_contract initial_machine_state
      addr test_internal_call_with_args2_ast)
    addr "foo" []
  = INL (IntV 6)
Proof
  rw[external_call_def, load_contract_def, initial_machine_state_def,
     SimpLHS, pair_case_rand]
  \\ CONV_TAC(LAND_CONV cv_eval) \\ rw[]
QED

Definition test_storage_variables_ast_def:
  test_storage_variables_ast = [
    VariableDecl "d" uint256 Private Storage;
    FunctionDef "foo" External [] uint256 [
      AnnAssign "a" uint256 (intlit 1);
      Assign (BaseTarget (GlobalNameTarget "d")) (Name "a");
      If (Name "a" == intlit 1)
        [Assign (BaseTarget (NameTarget "a")) (intlit 2)]
        [Assign (BaseTarget (NameTarget "a")) (intlit 3)];
      Return (SOME (GlobalName "d" + intlit 42))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_storage_variables_ast_def;

Theorem test_storage_variables:
  FST $ external_call
   (load_contract initial_machine_state
      addr test_storage_variables_ast)
    addr "foo" []
  = INL (IntV 43)
Proof
  rw[external_call_def, load_contract_def, initial_machine_state_def,
     SimpLHS, pair_case_rand]
  \\ CONV_TAC(LAND_CONV cv_eval) \\ rw[]
QED

Definition test_storage_variables2_ast_def:
  test_storage_variables2_ast = [
    VariableDecl "d" uint256 Private Storage;
    VariableDecl "k" uint256 Private Storage;
    FunctionDef "foo" External [] uint256 [
      Assign (BaseTarget (GlobalNameTarget "k")) (intlit 1);
      Assign (BaseTarget (GlobalNameTarget "d")) (GlobalName "k");
      AugAssign (GlobalNameTarget "d") Add (GlobalName "k");
      Return (SOME (GlobalName "d" + GlobalName "k"))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_storage_variables2_ast_def;

Theorem test_storage_variables2:
  FST $ external_call
   (load_contract initial_machine_state
      addr test_storage_variables2_ast)
    addr "foo" []
  = INL (IntV 3)
Proof
  rw[external_call_def, load_contract_def, initial_machine_state_def,
     SimpLHS, pair_case_rand]
  \\ CONV_TAC(LAND_CONV cv_eval) \\ rw[]
QED

Definition test_storage_variables3_ast_def:
  test_storage_variables3_ast = [
    VariableDecl "d" uint256 Private Storage;
    FunctionDef "bar" Internal [] VoidT [
      AnnAssign "a" (ArrayT uint256 (Dynamic 10))
        (ArrayLit (Dynamic 10) [intlit 1; intlit 2; intlit 3]);
      For "i" uint256 (Name "a") 10 [
        AugAssign (GlobalNameTarget "d") Add (Name "i")
      ]
    ];
    FunctionDef "foo" External [] uint256 [
      AnnAssign "a" (ArrayT uint256 (Dynamic 10))
        (ArrayLit (Dynamic 10) [intlit 1; intlit 2; intlit 3]);
      AnnAssign "counter" uint256 (intlit 0);
      For "i" uint256 (Name "a") 10 [
        AugAssign (GlobalNameTarget "d") Add (Name "i")
      ];
      Expr (Call "bar" []);
      Return (SOME (GlobalName "d"))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_storage_variables3_ast_def;

Theorem test_storage_variables3:
  FST $ external_call
   (load_contract initial_machine_state
      addr test_storage_variables3_ast)
    addr "foo" []
  = INL (IntV 12)
Proof
  rw[external_call_def, load_contract_def, initial_machine_state_def,
     SimpLHS, pair_case_rand]
  \\ CONV_TAC(LAND_CONV cv_eval) \\ rw[]
QED

Definition test_statefulness_of_storage_ast_def:
  test_statefulness_of_storage_ast = [
    VariableDecl "d" uint256 Private Storage;
    FunctionDef "foo" External [] uint256 [
      AugAssign (GlobalNameTarget "d") Add (intlit 1);
      Return (SOME (GlobalName "d"))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_statefulness_of_storage_ast_def;

Theorem test_statefulness_of_storage:
  let ms = load_contract initial_machine_state addr
             test_statefulness_of_storage_ast in
  let (r1, ms) = external_call ms addr "foo" [] in
  let (r2, ms) = external_call ms addr "foo" [] in
  let (r3, ms) = external_call ms addr "foo" [] in
  let (r4, ms) = external_call ms addr "foo" [] in
  let (r5, ms) = external_call ms addr "foo" [] in
    r1 = INL (IntV 1) ∧
    r2 = INL (IntV 2) ∧
    r3 = INL (IntV 3) ∧
    r4 = INL (IntV 4) ∧
    r5 = INL (IntV 5)
Proof
  rw[external_call_def, load_contract_def, initial_machine_state_def,
     SimpLHS, pair_case_rand]
  \\ CONV_TAC cv_eval
QED

Definition test_statefulness_of_storage2_ast_def:
  test_statefulness_of_storage2_ast = [
    VariableDecl "d" uint256 Private Storage;
    FunctionDef "foo" External [] uint256 [
      AugAssign (GlobalNameTarget "d") Add (intlit 1);
      Return (SOME (GlobalName "d"))
    ];
    FunctionDef "bar" External [] uint256 [
      AugAssign (GlobalNameTarget "d") Add (intlit 1);
      Return (SOME (GlobalName "d"))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_statefulness_of_storage2_ast_def;

Theorem test_statefulness_of_storage2:
  let ms = load_contract initial_machine_state addr
             test_statefulness_of_storage2_ast in
  let (f1, ms) = external_call ms addr "foo" [] in
  let (b1, ms) = external_call ms addr "bar" [] in
  let (f2, ms) = external_call ms addr "foo" [] in
  let (b2, ms) = external_call ms addr "bar" [] in
  let (f3, ms) = external_call ms addr "foo" [] in
  let (b3, ms) = external_call ms addr "bar" [] in
  let (f4, ms) = external_call ms addr "foo" [] in
  let (b4, ms) = external_call ms addr "bar" [] in
  let (f5, ms) = external_call ms addr "foo" [] in
  let (b5, ms) = external_call ms addr "bar" [] in
    f1 = INL (IntV (0 * 2 + 1)) ∧
    f2 = INL (IntV (1 * 2 + 1)) ∧
    f3 = INL (IntV (2 * 2 + 1)) ∧
    f4 = INL (IntV (3 * 2 + 1)) ∧
    f5 = INL (IntV (4 * 2 + 1)) ∧
    b1 = INL (IntV (0 * 2 + 2)) ∧
    b2 = INL (IntV (1 * 2 + 2)) ∧
    b3 = INL (IntV (2 * 2 + 2)) ∧
    b4 = INL (IntV (3 * 2 + 2)) ∧
    b5 = INL (IntV (4 * 2 + 2))
Proof
  rw[external_call_def, load_contract_def, initial_machine_state_def,
     SimpLHS, pair_case_rand]
  \\ CONV_TAC cv_eval
QED

(* TODO: tstorage tests *)

Definition test_default_storage_values_ast_def:
  test_default_storage_values_ast = [
    StructDef "S" [("a", uint256)];
    VariableDecl "a" uint256 Private Storage;
    VariableDecl "b" uint256 Private Storage;
    VariableDecl "c" (ArrayT uint256 (Dynamic 10)) Private Storage;
    VariableDecl "d" (StructT "S") Private Storage;
    VariableDecl "e" (BaseT (BytesT (Dynamic 10))) Private Storage;
    VariableDecl "f" (BaseT (StringT 10)) Private Storage;
    FunctionDef "foo" External [] uint256 [
      Assert (GlobalName "a" == intlit 0) "";
      Assert (GlobalName "b" == intlit 0) "";
      Assert (len (GlobalName "c") == intlit 0) "";
      Assert (Attribute (GlobalName "d") "a" == intlit 0) "";
      Assert (len (GlobalName "e") == intlit 0) "";
      Assert (len (GlobalName "f") == intlit 0) "";
      Return (SOME (intlit 1))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_default_storage_values_ast_def;

Theorem test_default_storage_values:
  FST $ external_call
   (load_contract initial_machine_state
      addr test_default_storage_values_ast)
    addr "foo" []
  = INL (IntV 1)
Proof
  rw[external_call_def, load_contract_def, initial_machine_state_def,
     SimpLHS, pair_case_rand]
  \\ CONV_TAC(LAND_CONV cv_eval) \\ rw[]
QED

(* TODO range builtin tests *)

Definition test_len_builtin_ast_def:
  test_len_builtin_ast = [
    FunctionDef "foo" External [] uint256 [
      AnnAssign "a" (ArrayT uint256 (Dynamic 3))
        (ArrayLit (Dynamic 3) [intlit 1; intlit 2; intlit 3]);
      Return (SOME (len (Name "a")))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_len_builtin_ast_def;

Theorem test_len_builtin:
  FST $ external_call
   (load_contract initial_machine_state
      addr test_len_builtin_ast)
    addr "foo" []
  = INL (IntV 3)
Proof
  rw[external_call_def, load_contract_def, initial_machine_state_def,
     SimpLHS, pair_case_rand]
  \\ CONV_TAC(LAND_CONV cv_eval) \\ rw[]
QED

val () = export_theory();
