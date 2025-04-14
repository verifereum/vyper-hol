open HolKernel boolLib bossLib Parse intLib wordsLib cv_transLib;
open numeralTheory arithmeticTheory finite_mapTheory;
open vyperAstTheory vyperInterpreterTheory vyperSmallStepTheory;

val () = new_theory "vyperTest";

Definition test_if_control_flow_ast_def:
  test_if_control_flow_ast = [
    def "foo" [] uint256
    [
      AnnAssign "a" uint256 (li 1);
      If (Name "a" == li 1)
      [
        Assign (BaseTarget (NameTarget "a")) (li 2)
      ]
      [
        Assign (BaseTarget (NameTarget "a")) (li 3)
      ];
      Return (SOME (Name "a" + li 42))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_if_control_flow_ast_def;

val pair_case_rand = TypeBase.case_rand_of``:'a # 'b``

val contract_addr = “42w: address”
val sender_addr = “1001w: address”

Definition call_foo_tx_def:
  call_foo_tx = call_txn ^sender_addr ^contract_addr "foo" [] 0
End

Definition call_bar_tx_def:
  call_bar_tx = call_txn ^sender_addr ^contract_addr "bar" [] 0
End

Theorem call_foo_tx_target[simp]:
  call_foo_tx.target = 42w ∧
  call_bar_tx.target = 42w
Proof
  rw[call_foo_tx_def, call_bar_tx_def]
QED

val () = cv_trans_deep_embedding EVAL call_foo_tx_def;
val () = cv_trans_deep_embedding EVAL call_bar_tx_def;

Definition deploy_tx_def:
  deploy_tx = call_txn ^sender_addr ^contract_addr "__init__" [] 0
End

val () = cv_trans_deep_embedding EVAL deploy_tx_def;

Definition load_and_call_foo_def:
  load_and_call_foo ts =
  case load_contract initial_machine_state deploy_tx ts
    of INL am => FST $ call_external am call_foo_tx
     | INR msg => INR msg
End

val () = cv_auto_trans load_and_call_foo_def;

Definition call_transactions_def:
  call_transactions am [] = ([], am) ∧
  call_transactions am (t::ts) =
  let (r, am) = call_external am t in
  let (rs, am) = call_transactions am ts in
    (r::rs, am)
End

val () = cv_auto_trans call_transactions_def;

Theorem test_if_control_flow:
  load_and_call_foo test_if_control_flow_ast
  = INL (IntV 44)
Proof
  CONV_TAC(LAND_CONV cv_eval) \\ rw[]
QED

Definition test_for_control_flow_ast_def:
  test_for_control_flow_ast = [
    def "foo" [] uint256
    [
       AnnAssign "a" (DynArray uint256 10)
         (DynArlit 10 [li 1; li 2; li 3]);
       AnnAssign "counter" uint256 (li 0);
       For "i" uint256 (Array (Name "a")) 10
       [ AugAssign (NameTarget "counter") Add (Name "i") ];
       Return (SOME (Name "counter"))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_for_control_flow_ast_def;

Theorem test_for_control_flow:
  load_and_call_foo test_for_control_flow_ast
  = INL (IntV 6)
Proof
  CONV_TAC(LAND_CONV cv_eval) \\ rw[]
QED

Definition test_array_assign_ast_def:
  test_array_assign_ast = [
    def "foo" [] uint256
    [
      AnnAssign "bar" (DynArray uint256 10)
        (DynArlit 10 [li 1; li 2]);
      Assign (BaseTarget (SubscriptTarget (NameTarget "bar") (li 0)))
        (li 3);
      Return (SOME (Subscript (Name "bar") (li 0) +
                    Subscript (Name "bar") (li 1) +
                    li 42))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_array_assign_ast_def;

Theorem test_array_assign:
  load_and_call_foo test_array_assign_ast
  = INL (IntV 47)
Proof
  CONV_TAC(LAND_CONV cv_eval) \\ rw[]
QED

Definition test_storage_array_assign_ast_def:
  test_storage_array_assign_ast = [
    privar "a" (DynArray uint256 10);
    def "foo" [] uint256 [
      AssignSelf "a" (DynArlit 10 [li 1; li 2]);
      Assign (BaseTarget
               (SubscriptTarget (TopLevelNameTarget "a")
                                (li 0)))
             (li 3);
      Return (SOME (Subscript (TopLevelName "a") (li 0) +
                    Subscript (TopLevelName "a") (li 1)))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_storage_array_assign_ast_def;

Theorem test_storage_array_assign:
  load_and_call_foo test_storage_array_assign_ast
  = INL (IntV 5)
Proof
  CONV_TAC(LAND_CONV cv_eval) \\ rw[]
QED

Definition test_internal_call_ast_def:
  test_internal_call_ast = [
    itl_def "bar" [] uint256 [
      AnnAssign "a" (DynArray uint256 10)
        (DynArlit 10 [li 1; li 2; li 3]);
      AnnAssign "counter" uint256 (li 0);
      For "i" uint256 (Array (Name "a")) 10 [
        AugAssign (NameTarget "counter") Add (Name "i")
      ];
      Return (SOME (Name "counter"))
    ];
    def "foo" [] uint256 [
      AnnAssign "a" (DynArray uint256 10)
        (DynArlit 10 [li 1; li 2; li 3]);
      AnnAssign "counter" uint256 (li 0);
      For "i" uint256 (Array (Name "a")) 10 [
        AugAssign (NameTarget "counter") Add (Name "i")
      ];
      Return (SOME (Name "counter" + call "bar" []))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_internal_call_ast_def;

Theorem test_internal_call:
  load_and_call_foo test_internal_call_ast
  = INL (IntV 12)
Proof
  CONV_TAC(LAND_CONV cv_eval) \\ rw[]
QED

Definition test_internal_call_without_return_ast_def:
  test_internal_call_without_return_ast = [
    privar "a" uint256;
    itl_def "bar" [] NoneT [
      AssignSelf "a" (li 42)
    ];
    def "foo" [] uint256 [
      Expr (call "bar" []);
      Return (SOME (TopLevelName "a"))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_internal_call_without_return_ast_def;

Theorem test_internal_call_without_return:
  load_and_call_foo test_internal_call_without_return_ast
  = INL (IntV 42)
Proof
  CONV_TAC(LAND_CONV cv_eval) \\ rw[]
QED

Definition test_internal_call_with_args_ast_def:
  test_internal_call_with_args_ast = [
    itl_def "baz" [("a", uint256)] uint256 [
      Return (SOME (Name "a"))
    ];
    itl_def "bar" [("a", uint256)] uint256 [
      Return (SOME (Name "a" + call "baz" [li 3]))
    ];
    def "foo" [] uint256 [
      AnnAssign "a" uint256 (li 1);
      Return (SOME (Name "a" + call "bar" [li 2]))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_internal_call_with_args_ast_def;

Theorem test_internal_call_with_args:
  load_and_call_foo test_internal_call_with_args_ast
  = INL (IntV 6)
Proof
  CONV_TAC(LAND_CONV cv_eval) \\ rw[]
QED

Definition test_internal_call_with_args2_ast_def:
  test_internal_call_with_args2_ast = [
    itl_def "baz" [("a", uint256)] uint256 [
      Return (SOME (Name "a"))
    ];
    itl_def "bar" [("a", uint256)] uint256 [
      Return (SOME (call "baz" [li 3] + Name "a"))
    ];
    def "foo" [] uint256 [
      AnnAssign "a" uint256 (li 1);
      Return (SOME (call "bar" [li 2] + Name "a"))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_internal_call_with_args2_ast_def;

Theorem test_internal_call_with_args2:
  load_and_call_foo test_internal_call_with_args2_ast
  = INL (IntV 6)
Proof
  CONV_TAC(LAND_CONV cv_eval) \\ rw[]
QED

Definition test_storage_variables_ast_def:
  test_storage_variables_ast = [
    privar "d" uint256;
    def "foo" [] uint256 [
      AnnAssign "a" uint256 (li 1);
      AssignSelf "d" (Name "a");
      If (Name "a" == li 1)
        [Assign (BaseTarget (NameTarget "a")) (li 2)]
        [Assign (BaseTarget (NameTarget "a")) (li 3)];
      Return (SOME (TopLevelName "d" + li 42))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_storage_variables_ast_def;

Theorem test_storage_variables:
  load_and_call_foo test_storage_variables_ast
  = INL (IntV 43)
Proof
  CONV_TAC(LAND_CONV cv_eval) \\ rw[]
QED

Definition test_storage_variables2_ast_def:
  test_storage_variables2_ast = [
    privar "d" uint256;
    privar "k" uint256;
    def "foo" [] uint256 [
      AssignSelf "k" (li 1);
      AssignSelf "d" (TopLevelName "k");
      AugAssign (TopLevelNameTarget "d") Add (TopLevelName "k");
      Return (SOME (TopLevelName "d" + TopLevelName "k"))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_storage_variables2_ast_def;

Theorem test_storage_variables2:
  load_and_call_foo test_storage_variables2_ast
  = INL (IntV 3)
Proof
  CONV_TAC(LAND_CONV cv_eval) \\ rw[]
QED

Definition test_storage_variables3_ast_def:
  test_storage_variables3_ast = [
    privar "d" uint256;
    itl_def "bar" [] NoneT [
      AnnAssign "a" (DynArray uint256 10)
        (DynArlit 10 [li 1; li 2; li 3]);
      For "i" uint256 (Array (Name "a")) 10 [
        AugAssign (TopLevelNameTarget "d") Add (Name "i")
      ]
    ];
    def "foo" [] uint256 [
      AnnAssign "a" (DynArray uint256 10)
        (DynArlit 10 [li 1; li 2; li 3]);
      AnnAssign "counter" uint256 (li 0);
      For "i" uint256 (Array (Name "a")) 10 [
        AugAssign (TopLevelNameTarget "d") Add (Name "i")
      ];
      Expr (call "bar" []);
      Return (SOME (TopLevelName "d"))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_storage_variables3_ast_def;

Theorem test_storage_variables3:
  load_and_call_foo test_storage_variables3_ast
  = INL (IntV 12)
Proof
  CONV_TAC(LAND_CONV cv_eval) \\ rw[]
QED

Definition test_statefulness_of_storage_ast_def:
  test_statefulness_of_storage_ast = [
    privar "d" uint256;
    def "foo" [] uint256 [
      AugAssign (TopLevelNameTarget "d") Add (li 1);
      Return (SOME (TopLevelName "d"))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_statefulness_of_storage_ast_def;

Theorem test_statefulness_of_storage:
  case load_contract initial_machine_state deploy_tx
    test_statefulness_of_storage_ast
  of INR msg => F
   | INL ms =>
     let (r1, ms) = call_external ms call_foo_tx in
     let (r2, ms) = call_external ms call_foo_tx in
     let (r3, ms) = call_external ms call_foo_tx in
     let (r4, ms) = call_external ms call_foo_tx in
     let (r5, ms) = call_external ms call_foo_tx in
       r1 = INL (IntV 1) ∧
       r2 = INL (IntV 2) ∧
       r3 = INL (IntV 3) ∧
       r4 = INL (IntV 4) ∧
       r5 = INL (IntV 5)
Proof
  CONV_TAC cv_eval
QED

Definition test_statefulness_of_storage2_ast_def:
  test_statefulness_of_storage2_ast = [
    privar "d" uint256;
    def "foo" [] uint256 [
      AugAssign (TopLevelNameTarget "d") Add (li 1);
      Return (SOME (TopLevelName "d"))
    ];
    def "bar" [] uint256 [
      AugAssign (TopLevelNameTarget "d") Add (li 1);
      Return (SOME (TopLevelName "d"))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_statefulness_of_storage2_ast_def;

Theorem test_statefulness_of_storage2:
  case load_contract initial_machine_state deploy_tx
    test_statefulness_of_storage2_ast
  of INR msg => F
   | INL ms =>
  let (f1, ms) = call_external ms call_foo_tx in
  let (b1, ms) = call_external ms call_bar_tx in
  let (f2, ms) = call_external ms call_foo_tx in
  let (b2, ms) = call_external ms call_bar_tx in
  let (f3, ms) = call_external ms call_foo_tx in
  let (b3, ms) = call_external ms call_bar_tx in
  let (f4, ms) = call_external ms call_foo_tx in
  let (b4, ms) = call_external ms call_bar_tx in
  let (f5, ms) = call_external ms call_foo_tx in
  let (b5, ms) = call_external ms call_bar_tx in
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
  CONV_TAC cv_eval
QED

Definition test_statefulness_of_tstorage_ast_def:
  test_statefulness_of_tstorage_ast = [
    VariableDecl Private Transient "d" uint256;
    (* omitted: interface Bar *)
    def "foo" [] uint256 [
      AugAssign (TopLevelNameTarget "d") Add (li 1);
      Return (SOME (Call (ExtCall "bar") [self]))
    ];
    def "bar" [] uint256 [
      AugAssign (TopLevelNameTarget "d") Add (li 1);
      Return (SOME (self_ "d"))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_statefulness_of_tstorage_ast_def;

(* needs ExtCall
Theorem test_statefulness_of_tstorage:
  (case load_contract initial_machine_state deploy_tx
          test_statefulness_of_tstorage_ast of
     INL am =>
     FST $ call_transactions am
       [call_foo_tx; call_foo_tx; call_foo_tx]
   | _ => [])
  = [INL (IntV 2); INL (IntV 2); INL (IntV 2)]
Proof
  CONV_TAC $ LAND_CONV cv_eval
QED
*)

Definition test_tstorage_variables0_ast_def:
  test_tstorage_variables0_ast = [
    VariableDecl Private Transient "d" uint256;
    VariableDecl Private Transient "k" uint256;
    def "foo" [] uint256 [
      AssignSelf "k" (li 1);
      AssignSelf "d" (TopLevelName "k");
      AugAssign (TopLevelNameTarget "d") Add (TopLevelName "k");
      Return (SOME (TopLevelName "d" + TopLevelName "k"))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_tstorage_variables0_ast_def;

Theorem test_tstorage_variables0:
  load_and_call_foo test_tstorage_variables0_ast
  = INL (IntV 3)
Proof
  CONV_TAC(LAND_CONV cv_eval) \\ rw[]
QED

Definition test_tstorage_variables2_ast_def:
  test_tstorage_variables2_ast = [
    VariableDecl Private Transient "d" uint256;
    VariableDecl Private Transient "k" uint256;
    def "foo" [] uint256 [
      If (TopLevelName "k" == li 0) [
        AssignSelf "k" (li 1)
      ] [];
      AssignSelf "d" (TopLevelName "k");
      AugAssign (TopLevelNameTarget "d") Add (TopLevelName "k");
      Return (SOME (TopLevelName "d" + TopLevelName "k"))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_tstorage_variables2_ast_def;

Theorem test_tstorage_variables2:
  load_and_call_foo test_tstorage_variables2_ast
  = INL (IntV 3)
Proof
  CONV_TAC(LAND_CONV cv_eval) \\ rw[]
QED

Definition test_default_storage_values_ast_def:
  test_default_storage_values_ast = [
    StructDecl "S" [("a", uint256)];
    privar "a" uint256;
    privar "b" uint256;
    privar "c" (DynArray uint256 10);
    privar "d" (StructT "S");
    privar "e" (BaseT (BytesT (Dynamic 10)));
    privar "f" (BaseT (StringT 10));
    def "foo" [] uint256 [
      Assert (TopLevelName "a" == li 0) "";
      Assert (TopLevelName "b" == li 0) "";
      Assert (len (TopLevelName "c") == li 0) "";
      Assert (Attribute (TopLevelName "d") "a" == li 0) "";
      Assert (len (TopLevelName "e") == li 0) "";
      Assert (len (TopLevelName "f") == li 0) "";
      Return (SOME (li 1))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_default_storage_values_ast_def;

Theorem test_default_storage_values:
  load_and_call_foo test_default_storage_values_ast
  = INL (IntV 1)
Proof
  CONV_TAC(LAND_CONV cv_eval) \\ rw[]
QED

Definition test_range_builtin_ast_def:
  test_range_builtin_ast = [
    privar "a" uint256;
    def "foo" [] uint256 [
      For "i" uint256 (Range (li 0) (li 10)) 10 [
        AugAssign (TopLevelNameTarget "a") Add (Name "i")
      ];
      Return (SOME (TopLevelName "a"))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_range_builtin_ast_def;

Theorem test_range_builtin:
  load_and_call_foo test_range_builtin_ast
  = INL (IntV &(SUM (COUNT_LIST 10)))
Proof
  CONV_TAC (LAND_CONV cv_eval)
  \\ EVAL_TAC
QED

Definition test_range_builtin2_ast_def:
  test_range_builtin2_ast = [
    privar "a" uint256;
    def "foo" [] uint256 [
      AnnAssign "k" uint256 (li 5);
      For "i" uint256 (Range (li 0) (Name "k")) 5 [
        AugAssign (TopLevelNameTarget "a") Add (Name "i")
      ];
      Return (SOME (TopLevelName "a"))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_range_builtin2_ast_def;

Theorem test_range_builtin2:
  load_and_call_foo test_range_builtin2_ast
  = INL (IntV &(SUM (COUNT_LIST 5)))
Proof
  CONV_TAC (LAND_CONV cv_eval)
  \\ EVAL_TAC
QED

Definition test_range_builtin3_ast_def:
  test_range_builtin3_ast = [
    privar "a" uint256;
    def "foo" [] uint256 [
      For "i" uint256 (Range (li 1) (li 5)) (5 - 1) [
        AugAssign (TopLevelNameTarget "a") Add (Name "i")
      ];
      Return (SOME (TopLevelName "a"))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_range_builtin3_ast_def;

Theorem test_range_builtin3:
  load_and_call_foo test_range_builtin3_ast
  = INL (IntV &(SUM (MAP ((+) 1) (COUNT_LIST (5 - 1)))))
Proof
  CONV_TAC (LAND_CONV cv_eval)
  \\ EVAL_TAC
QED

Definition test_range_builtin4_ast_def:
  test_range_builtin4_ast = [
    privar "a" uint256;
    def "foo" [] uint256 [
      AnnAssign "k" uint256 (li 1);
      For "i" uint256 (Range (Name "k") (li 5)) 4 [
        AugAssign (TopLevelNameTarget "a") Add (Name "i")
      ];
      Return (SOME (TopLevelName "a"))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_range_builtin4_ast_def;

Theorem test_range_builtin4:
  load_and_call_foo test_range_builtin4_ast
  = INL (IntV &(SUM (MAP ((+) 1) (COUNT_LIST (5 - 1)))))
Proof
  CONV_TAC (LAND_CONV cv_eval)
  \\ EVAL_TAC
QED

Definition test_len_builtin_ast_def:
  test_len_builtin_ast = [
    def "foo" [] uint256 [
      AnnAssign "a" (DynArray uint256 3)
        (DynArlit 3 [li 1; li 2; li 3]);
      Return (SOME (len (Name "a")))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_len_builtin_ast_def;

Theorem test_len_builtin:
  load_and_call_foo test_len_builtin_ast
  = INL (IntV 3)
Proof
  CONV_TAC(LAND_CONV cv_eval) \\ rw[]
QED

Definition test_len_builtin2_ast_def:
  test_len_builtin2_ast = [
    privar "d" (DynArray uint256 3);
    def "foo" [] uint256 [
      Return (SOME (len (TopLevelName "d")))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_len_builtin2_ast_def;

Theorem test_len_builtin2:
  load_and_call_foo test_len_builtin2_ast
  = INL (IntV 0)
Proof
  CONV_TAC(LAND_CONV cv_eval) \\ rw[]
QED

Definition test_len_builtin3_ast_def:
  test_len_builtin3_ast = [
    privar "s" (BaseT (StringT 10));
    def "foo" [] uint256 [
      AssignSelf "s" (Literal (StringL 10 "hello"));
      Return (SOME (len (TopLevelName "s")))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_len_builtin3_ast_def;

Theorem test_len_builtin3:
  load_and_call_foo test_len_builtin3_ast
  = INL (IntV 5)
Proof
  CONV_TAC(LAND_CONV cv_eval) \\ rw[]
QED

Definition test_len_builtin4_ast_def:
  test_len_builtin4_ast = [
    privar "s" (BaseT (BytesT (Dynamic 10)));
    def "foo" [] uint256 [
      AssignSelf "s"
        (Literal (BytesL (Dynamic 10)
          ^(rhs $ concl $ EVAL “MAP (n2w o ORD) "hello" : word8 list”)));
      Return (SOME (len (TopLevelName "s")))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_len_builtin4_ast_def;

Theorem test_len_builtin4:
  load_and_call_foo test_len_builtin4_ast
  = INL (IntV 5)
Proof
  CONV_TAC(LAND_CONV cv_eval) \\ rw[]
QED

(* TODO: test abi_encode *)

(* TODO: test self call *)

(* TODO: test default arg value *)

Definition test_external_func_arg_ast_def:
  test_external_func_arg_ast = [
    def "foo" [("a", uint256)] uint256 [
      Return (SOME (Name "a"))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_external_func_arg_ast_def;

Theorem test_external_func_arg:
  case load_contract initial_machine_state deploy_tx
    test_external_func_arg_ast
  of INR _ => F
  |  INL ms =>
      FST $ call_external ms
          $ call_txn ^sender_addr ^contract_addr "foo" [IntV 42] 0
      = INL (IntV 42)
Proof
  CONV_TAC cv_eval
QED

Definition test_external_func_arg2_ast_def:
  test_external_func_arg2_ast = [
    def "foo"
      [("a", DynArray uint256 10); ("s", BaseT (StringT 100))]
      (TupleT [DynArray uint256 10; BaseT (StringT 100)]) [
      Return (SOME (ArrayLit (Fixed 2) [Name "a"; Name "s"]))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_external_func_arg2_ast_def;

Theorem test_external_func_arg2:
  a = ArrayV (Dynamic 10) [IntV 1; IntV 2; IntV 3] ∧
  s = StringV 100 "hello"
  ⇒
  (case load_contract initial_machine_state deploy_tx
     test_external_func_arg2_ast
   of INR msg => INR msg
   |  INL ms =>
       FST $ call_external ms
           $ call_txn ^sender_addr ^contract_addr "foo" [a; s] 0)
      = INL $ ArrayV (Fixed 2) [a; s]
Proof
  rw[]
  \\ CONV_TAC $ cv_eval
QED

Definition test_external_func_arg3_ast_def:
  test_external_func_arg3_ast =
  let dynarray_t = DynArray (DynArray uint256 10) 10 in [
    def "foo" [("a", DynArray uint256 10);
               ("s", BaseT (StringT 100));
               ("b", dynarray_t)]
      (TupleT [DynArray uint256 10; BaseT (StringT 100); dynarray_t]) [
      Return $ SOME $ ArrayLit (Fixed 3) [Name "a"; Name "s"; Name "b"]
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_external_func_arg3_ast_def;

Theorem test_external_func_arg3:
  complex_array = ArrayV (Dynamic 10) [
    ArrayV (Dynamic 10) [IntV 4; IntV 5; IntV 6];
    ArrayV (Dynamic 10) [IntV 7; IntV 8; IntV 9; IntV 10; IntV 11];
    ArrayV (Dynamic 10) [];
    ArrayV (Dynamic 10) [IntV 12]] ∧
  a = ArrayV (Dynamic 10) [IntV 1; IntV 2; IntV 3] ∧
  s = StringV 100 "hello"
  ⇒
  (case load_contract initial_machine_state deploy_tx
     test_external_func_arg3_ast
   of INR msg => INR msg
   |  INL ms =>
       FST $ call_external ms
           $ call_txn ^sender_addr ^contract_addr "foo" [a; s; complex_array] 0)
      = INL $ ArrayV (Fixed 3) [a; s; complex_array]
Proof
  rw[]
  \\ CONV_TAC $ cv_eval
QED

Definition test_external_func_arg4_ast_def:
  test_external_func_arg4_ast =
  let tuple_t = TupleT [BaseT(StringT 93);
                        DynArray (DynArray uint256 10) 10] in [
    def "foo" [("a", DynArray uint256 10);
               ("s", BaseT (StringT 100));
               ("b", tuple_t)]
              (TupleT [DynArray uint256 10; BaseT(StringT 100); tuple_t]) [
      Return $ SOME $ ArrayLit (Fixed 3) [Name "a"; Name "s"; Name "b"]
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_external_func_arg4_ast_def;

Theorem test_external_func_arg4:
  complex_array = ArrayV (Dynamic 10) [
    ArrayV (Dynamic 10) [IntV 4; IntV 5; IntV 6];
    ArrayV (Dynamic 10) [IntV 7; IntV 8; IntV 9; IntV 10; IntV 11];
    ArrayV (Dynamic 10) [];
    ArrayV (Dynamic 10) [IntV 12]] ∧
  complex_tuple = ArrayV (Fixed 2) [StringV 93 "apollo"; complex_array] ∧
  a = ArrayV (Dynamic 10) [IntV 1; IntV 2; IntV 3] ∧
  s = StringV 100 "hello"
  ⇒
  (case load_contract initial_machine_state deploy_tx
     test_external_func_arg4_ast
   of INR msg => INR msg
   |  INL ms =>
       FST $ call_external ms
           $ call_txn ^sender_addr ^contract_addr "foo" [a; s; complex_tuple] 0)
      = INL $ ArrayV (Fixed 3) [a; s; complex_tuple]
Proof
  rw[]
  \\ CONV_TAC $ cv_eval
QED

Definition test_empty_builtin_ast_def:
  test_empty_builtin_ast = [
    def "foo" [] uint256 [
      Return (SOME (TypeBuiltin Empty uint256))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_empty_builtin_ast_def;

Theorem test_empty_builtin:
  load_and_call_foo test_empty_builtin_ast
  = INL (IntV 0)
Proof
  CONV_TAC cv_eval
QED

Definition test_empty_builtin2_ast_def:
  test_empty_builtin2_ast = [
    def "foo" [] uint256 [
      Return (SOME (TypeBuiltin Empty (BaseT (StringT 56))))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_empty_builtin2_ast_def;

Theorem test_empty_builtin2:
  load_and_call_foo test_empty_builtin2_ast
  = INL (StringV 56 "")
Proof
  CONV_TAC cv_eval
QED

Definition test_empty_builtin3_ast_def:
  test_empty_builtin3_ast = [
    def "foo" [] uint256 [
      Return (SOME (TypeBuiltin Empty (ArrayT (BaseT (StringT 32)) (Dynamic 10))))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_empty_builtin3_ast_def;

Theorem test_empty_builtin3:
  load_and_call_foo test_empty_builtin3_ast
  = INL (ArrayV (Dynamic 10) [])
Proof
  CONV_TAC cv_eval
QED

(* TODO raw_call tests *)

(* TODO static call tests *)

(* TODO abi encode tests *)

(* TODO interface call tests *)

Definition test_struct_ast_def:
  test_struct_ast = [
    StructDecl "S" [
      ("a", uint256);
      ("b", uint256)
    ];
    def "foo" [] uint256 [
      AnnAssign "s" (StructT "S")
        (StructLit "S" [("a", li 1); ("b", li 2)]);
      Return (SOME (Attribute (Name "s") "a"))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_struct_ast_def;

Theorem test_struct:
  load_and_call_foo test_struct_ast
  = INL (IntV 1)
Proof
  CONV_TAC cv_eval
QED

Definition test_struct2_ast_def:
  test_struct2_ast = [
    StructDecl "S" [
      ("a", uint256);
      ("b", uint256)
    ];
    StructDecl "T" [
      ("s", StructT "S");
      ("c", uint256)
    ];
    def "foo" [] uint256 [
      AnnAssign "s" (StructT "S")
        (StructLit "S" [("a", li 1); ("b", li 2)]);
      AnnAssign "t" (StructT "T")
        (StructLit "T" [("s", Name "s"); ("c", li 3)]);
      Return (SOME $
        (Attribute (Attribute (Name "t") "s") "a") +
        (Attribute (Attribute (Name "t") "s") "b") +
        (Attribute (Name "t") "c")
      )
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_struct2_ast_def;

Theorem test_struct2:
  load_and_call_foo test_struct2_ast
  = INL (IntV 6)
Proof
  CONV_TAC cv_eval
QED

Definition test_struct3_ast_def:
  test_struct3_ast = [
    StructDecl "S" [
      ("a", uint256);
      ("b", uint256)
    ];
    privar "d" (DynArray (StructT "S") 3);
    def "foo" [] uint256 [
      AssignSelf "d" $
        DynArlit 3 [
          StructLit "S" [("a", li 0); ("b", li 1)];
          StructLit "S" [("a", li 2); ("b", li 3)];
          StructLit "S" [("a", li 4); ("b", li 5)]
        ];
      AnnAssign "acc" uint256 (li 0);
      For "s" (StructT "S") (Array (TopLevelName "d")) 3 [
        AugAssign (NameTarget "acc") Add $
          Attribute (Name "s") "a" +
          Attribute (Name "s") "b"
      ];
      Return $ SOME $ Name "acc"
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_struct3_ast_def;

Theorem test_struct3:
  load_and_call_foo test_struct3_ast
  = INL (IntV $ 1 + 2 + 3 + 4 + 5)
Proof
  CONV_TAC cv_eval
QED

Definition test_struct4_ast_def:
  test_struct4_ast = [
    StructDecl "S" [
      ("a", uint256);
      ("b", uint256)
    ];
    privar "s" (StructT "S");
    def "foo" [] uint256 [
      AssignSelf "s" $
        StructLit "S" [("a", li 1); ("b", li 2)];
      Assign (BaseTarget (AttributeTarget (TopLevelNameTarget "s") "a")) (li 3);
      Return $ SOME $ Attribute (self_ "s") "a" + Attribute (self_ "s") "b"
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_struct4_ast_def;

Theorem test_struct4:
  load_and_call_foo test_struct4_ast
  = INL (IntV $ 3 + 2)
Proof
  CONV_TAC cv_eval
QED

Definition test_tstorage_clearing_ast_def:
  test_tstorage_clearing_ast = [
    VariableDecl Private Transient "t" uint256;
    def "foo" [] uint256 [
      AssignSelf "t" (li 42);
      Return $ SOME (self_ "t")
    ];
    def "bar" [] uint256 [
      Return $ SOME (self_ "t")
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_tstorage_clearing_ast_def;

Theorem test_tstorage_clearing:
  (case load_contract initial_machine_state deploy_tx
          test_tstorage_clearing_ast of
     INL am =>
     FST $ call_transactions am
       [call_foo_tx; call_bar_tx; call_foo_tx]
   | _ => [])
  = [INL (IntV 42); INL (IntV 0); INL (IntV 42)]
Proof
  CONV_TAC $ cv_eval
QED

Definition test_tstorage_clearing2_ast_def:
  test_tstorage_clearing2_ast = [
    StructDecl "S" [("a", uint256)];
    VariableDecl Private Transient "a" uint256;
    VariableDecl Private Transient "b" uint256;
    VariableDecl Private Transient "c" (DynArray uint256 10);
    VariableDecl Private Transient "d" (StructT "S");
    VariableDecl Private Transient "e" (BaseT (BytesT (Dynamic 10)));
    VariableDecl Private Transient "f" (BaseT (StringT 10));
    def "foo" [] NoneT [
      Assert (self_ "a" == li 0) "";
      Assert (self_ "b" == li 0) "";
      Assert (len (self_ "c") == li 0) "";
      Assert (Attribute (self_ "d") "a" == li 0) "";
      Assert (len (self_ "e") == li 0) "";
      Assert (len (self_ "f") == li 0) ""
    ];
    def "bar" [] NoneT [
      AssignSelf "a" (li 1);
      AssignSelf "b" (li 1);
      AssignSelf "c" (DynArlit 10 [li 1; li 2; li 3]);
      Assign (BaseTarget (AttributeTarget (TopLevelNameTarget "d") "a")) (li 1);
      AssignSelf "e" $
        Literal $ BytesL (Dynamic 10) (MAP (n2w o ORD) "hello");
      AssignSelf "f" $ Literal $ StringL 10 "hello"
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_tstorage_clearing2_ast_def;

Theorem test_tstorage_clearing2:
  (case load_contract initial_machine_state deploy_tx
          test_tstorage_clearing2_ast of
     INL am =>
     FST $ call_transactions am
       [call_foo_tx; call_bar_tx; call_foo_tx]
   | _ => [])
  = [INL NoneV; INL NoneV; INL NoneV]
Proof
  CONV_TAC $ cv_eval
QED

(* TODO abi encode struct *)

Definition test_hash_map_ast_def:
  test_hash_map_ast = [
    HashMapDecl Public "var" uint256 (Type uint256);
    def "foo" [] uint256 [
      Assign
        (BaseTarget (SubscriptTarget (TopLevelNameTarget "var") (li 0)))
        (li 42);
      Return $ SOME $ Subscript (self_ "var") (li 0) +
                      Subscript (self_ "var") (li 1)
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_hash_map_ast_def;

Theorem test_hash_map:
  (case load_contract initial_machine_state deploy_tx test_hash_map_ast of
     INL am =>
     FST $ call_transactions am
       [call_foo_tx;
        call_txn ^sender_addr ^contract_addr "var" [IntV 0] 0;
        call_txn ^sender_addr ^contract_addr "var" [IntV 1] 0]
   | _ => [])
  = [INL (IntV 42); INL (IntV 42); INL (IntV 0)]
Proof
  CONV_TAC $ LAND_CONV cv_eval
  \\ rw[]
QED

Definition test_public_var_getter_ast_def:
  test_public_var_getter_ast public typ ve = [
    VariableDecl
      (if public then Public else Private)
      Storage "var" typ;
    def "foo" [] NoneT [
      Assign (BaseTarget $ TopLevelNameTarget "var") ve
    ]
  ]
End

val () = cv_auto_trans test_public_var_getter_ast_def;

Theorem test_public_var_getter:
  msg = Error "call lookup_function" ∧
  MEM (public, typ, ve, vv) [
    (T, uint256, li 42, INL $ INL $ IntV 42);
    (F, uint256, li 42, INL $ INR msg);
    (T, DynArray uint256 10,
        ArrayLit (Dynamic 10) [li 1; li 2; li 3],
        INR $ MAP (INL o IntV) [1;2;3]);
    (F, DynArray uint256 10,
        ArrayLit (Dynamic 10) [li 1; li 2; li 3],
        INR $ MAP (K (INR msg)) [1;2;3]);
    (T, BaseT $ StringT 10,
        Literal $ StringL 10 "hello",
        INL $ INL $ StringV 10 "hello");
    (F, BaseT $ StringT 10,
        Literal $ StringL 10 "hello",
        INL $ INR msg);
    (T, BaseT $ BytesT (Fixed 10),
        Literal $ BytesL (Fixed 10) (MAP (n2w o ORD) "hello"),
        INL $ INL $ BytesV (Fixed 10) (MAP (n2w o ORD) "hello"));
    (F, BaseT $ BytesT (Fixed 10),
        Literal $ BytesL (Fixed 10) (MAP (n2w o ORD) "hello"),
        INL $ INR msg)
  ] ⇒
  let txns_ers =
    case vv of INL v => [(call_txn ^sender_addr ^contract_addr "var" [] 0, v)]
             | INR ls => MAPi (λi v. (call_txn ^sender_addr ^contract_addr "var"
                                        [IntV &i] 0, v)) ls in
  (case load_contract initial_machine_state deploy_tx $
        test_public_var_getter_ast public typ ve of
   | INR msg => []
   | INL am => FST $ call_transactions am (call_foo_tx::(MAP FST txns_ers)))
  =
  (INL NoneV)::(MAP SND txns_ers)
Proof
  rw[] \\ rw[]
  \\ CONV_TAC $ LAND_CONV cv_eval
  \\ rw[]
QED

(* TODO: encode address *)

Definition test_init_ast_def:
  test_init_ast = [
    pubvar "d" uint256;
    deploy_def "__init__" [("a", uint256)] NoneT [
      AssignSelf "d" (Name "a")
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_init_ast_def;

Theorem test_init:
  (case load_contract initial_machine_state
        (call_txn ^sender_addr ^contract_addr "__init__" [IntV 42] 0)
        test_init_ast of
     INL am =>
     FST $ call_external am $ call_txn ^sender_addr ^contract_addr "d" [] 0
   | INR x => INR x)
  = INL (IntV 42)
Proof
  CONV_TAC cv_eval
QED

Definition test_init2_ast_def:
  test_init2_ast = [
    pubvar "d" uint256;
    deploy_def "__init__" [("a", uint256)] NoneT [
      Expr $ call "bar" []
    ];
    itl_def "bar" [] NoneT [
      AssignSelf "d" (call "foo" [])
    ];
    itl_def "foo" [] uint256 [
      Return $ SOME (li 42)
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_init2_ast_def;

(* TODO: make code available during init
Theorem test_init2:
  (case load_contract initial_machine_state
        (call_txn ^sender_addr ^contract_addr "__init__" [IntV 42] 0)
        test_init2_ast of
     INL am =>
     FST $ call_external am $ call_txn ^sender_addr ^contract_addr "d" [] 0
   | INR x => INR x)
  = INL (IntV 42)
Proof
  CONV_TAC cv_eval
QED
*)

(* TODO: init tests 3 4 *)

(* TODO: library storage tests *)

(* TODO: module struct attribute *)

Definition test_darray_append_ast_def:
  test_darray_append_ast = [
    pubvar "a" (DynArray uint256 10);
    def "foo" [] uint256 [
      AssignSelf "a" (DynArlit 10 []);
      Append (TopLevelNameTarget "a") (li 1);
      Return $ SOME (Subscript (self_ "a") (li 0))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_darray_append_ast_def;

Theorem test_darray_append:
  load_and_call_foo test_darray_append_ast
  = INL (IntV 1)
Proof
  CONV_TAC cv_eval
QED

Definition test_darray_append2_ast_def:
  test_darray_append2_ast = [
    pubvar "a" (DynArray uint256 1);
    def "foo" [] uint256 [
      AssignSelf "a" (DynArlit 1 []);
      Append (TopLevelNameTarget "a") (li 1);
      Append (TopLevelNameTarget "a") (li 1);
      Return $ SOME (Subscript (self_ "a") (li 0))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_darray_append2_ast_def;

Theorem test_darray_append2:
  load_and_call_foo test_darray_append2_ast
  = INR (Error "Append Overflow")
Proof
  CONV_TAC cv_eval
QED

Definition test_darray_append3_ast_def:
  test_darray_append3_ast = [
    pubvar "a" (DynArray (DynArray uint256 1) 2);
    def "foo" [] uint256 [
      AssignSelf "a" (DynArlit 2 []);
      Append (TopLevelNameTarget "a") (DynArlit 1 [li 1]);
      Append (TopLevelNameTarget "a") (DynArlit 1 [li 2]);
      Return $ SOME (Subscript (self_ "a") (li 0))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_darray_append3_ast_def;

Theorem test_darray_append3:
  load_and_call_foo test_darray_append3_ast
  = INL (ArrayV (Dynamic 1) [IntV 1])
Proof
  CONV_TAC cv_eval
QED

Definition test_darray_pop_ast_def:
  test_darray_pop_ast = [
    pubvar "a" (DynArray (DynArray uint256 1) 2);
    itl_def "bar" [] (DynArray uint256 1) [
      Return $ SOME $ DynArlit 1 []
    ];
    def "foo" [] uint256 [
      AssignSelf "a" (DynArlit 2 []);
      Append (TopLevelNameTarget "a") (DynArlit 1 [li 1]);
      AnnAssign "u" uint256 $ Subscript (Pop (TopLevelNameTarget "a")) (li 0);
      Return $ SOME $ Name "u"
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_darray_pop_ast_def;

Theorem test_darray_pop:
  load_and_call_foo test_darray_pop_ast
  = INL (IntV 1)
Proof
  CONV_TAC cv_eval
QED

Definition test_darray_pop2_ast_def:
  test_darray_pop2_ast = [
    pubvar "a" (DynArray (DynArray uint256 1) 2);
    itl_def "bar" [] (DynArray uint256 1) [
      Return $ SOME $ DynArlit 1 []
    ];
    def "foo" [] uint256 [
      AssignSelf "a" (DynArlit 2 []);
      Append (TopLevelNameTarget "a") (DynArlit 1 [li 1]);
      AnnAssign "u" (DynArray uint256 10) $ Pop (TopLevelNameTarget "a");
      Return $ SOME $ Pop (NameTarget "u")
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_darray_pop2_ast_def;

Theorem test_darray_pop2:
  load_and_call_foo test_darray_pop2_ast
  = INL (IntV 1)
Proof
  CONV_TAC cv_eval
QED

Definition test_darray_pop3_ast_def:
  test_darray_pop3_ast = [
    pubvar "a" (DynArray (DynArray uint256 1) 2);
    itl_def "bar" [] (DynArray uint256 1) [
      Return $ SOME $ DynArlit 1 []
    ];
    def "foo" [] uint256 [
      AssignSelf "a" (DynArlit 2 []);
      Append (TopLevelNameTarget "a") (DynArlit 1 [li 1]);
      Append (TopLevelNameTarget "a") (DynArlit 1 [li 2]);
      AnnAssign "u" (DynArray uint256 10) $ Pop (TopLevelNameTarget "a");
      Return $ SOME $ Pop (NameTarget "u") +
                      Subscript (Pop (TopLevelNameTarget "a")) (li 0)
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_darray_pop3_ast_def;

Theorem test_darray_pop3:
  load_and_call_foo test_darray_pop3_ast
  = INL (IntV 3)
Proof
  CONV_TAC cv_eval
QED

Definition test_pass_by_value_ast_def:
  test_pass_by_value_ast = [
    pubvar "a" $ DynArray uint256 2;
    itl_def "bar" [("d", DynArray uint256 2)] NoneT [
      Assign (BaseTarget (SubscriptTarget (NameTarget "d") (li 0)))
        (li 0)
    ];
    def "foo" [] (DynArray uint256 2) [
      AssignSelf "a" (DynArlit 2 [li 1; li 1]);
      Expr (call "bar" [TopLevelName "a"]);
      Return $ SOME $ TopLevelName "a"
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_pass_by_value_ast_def;

Theorem test_pass_by_value:
  load_and_call_foo test_pass_by_value_ast =
  INL (ArrayV (Dynamic 2) [IntV 1; IntV 1])
Proof
  CONV_TAC cv_eval
QED

Definition test_pass_by_value2_ast_def:
  test_pass_by_value2_ast = [
    itl_def "bar" [("d", DynArray uint256 2)] NoneT [
      Assign (BaseTarget (SubscriptTarget (NameTarget "d") (li 0)))
        (li 0)
    ];
    def "foo" [] (DynArray uint256 2) [
      AnnAssign "d" (DynArray uint256 2) (DynArlit 2 [li 1; li 1]);
      Expr (call "bar" [Name "d"]);
      Return $ SOME $ Name "d"
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_pass_by_value2_ast_def;

Theorem test_pass_by_value2:
  load_and_call_foo test_pass_by_value2_ast =
  INL (ArrayV (Dynamic 2) [IntV 1; IntV 1])
Proof
  CONV_TAC cv_eval
QED

Definition test_pass_by_value3_ast_def:
  test_pass_by_value3_ast = [
    def "foo" [] (DynArray uint256 2) [
      AnnAssign "d" (DynArray uint256 2) (DynArlit 2 [li 1; li 1]);
      AnnAssign "d2" (DynArray uint256 2) (Name "d");
      Assign (BaseTarget (SubscriptTarget (NameTarget "d2") (li 0))) (li 0);
      Return $ SOME $ Name "d"
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_pass_by_value3_ast_def;

Theorem test_pass_by_value3:
  load_and_call_foo test_pass_by_value3_ast =
  INL (ArrayV (Dynamic 2) [IntV 1; IntV 1])
Proof
  CONV_TAC cv_eval
QED

Definition test_pass_by_value4_ast_def:
  test_pass_by_value4_ast = [
    def "foo" [] (DynArray uint256 2) [
      AnnAssign "d" (DynArray uint256 2) (DynArlit 2 [li 1; li 1]);
      AnnAssign "d2" (DynArray uint256 2) (Name "d");
      AugAssign (SubscriptTarget (NameTarget "d2") (li 0)) Add (li 1);
      Return $ SOME $ Name "d"
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_pass_by_value4_ast_def;

Theorem test_pass_by_value4:
  load_and_call_foo test_pass_by_value4_ast =
  INL (ArrayV (Dynamic 2) [IntV 1; IntV 1])
Proof
  CONV_TAC cv_eval
QED

Definition test_pass_by_value5_ast_def:
  test_pass_by_value5_ast = [
    pubvar "a" $ DynArray uint256 2;
    itl_def "bar" [] (DynArray uint256 2) [
      Return $ SOME $ self_ "a"
    ];
    def "foo" [] (DynArray uint256 2) [
      AssignSelf "a" (DynArlit 2 [li 1; li 1]);
      AnnAssign "d" (DynArray uint256 2) (call "bar" []);
      Assign (BaseTarget (SubscriptTarget (NameTarget "d") (li 0))) (li 0);
      Return $ SOME $ TopLevelName "a"
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_pass_by_value5_ast_def;

Theorem test_pass_by_value5:
  load_and_call_foo test_pass_by_value5_ast =
  INL (ArrayV (Dynamic 2) [IntV 1; IntV 1])
Proof
  CONV_TAC cv_eval
QED

Definition test_pass_by_value6_ast_def:
  test_pass_by_value6_ast = [
    StructDecl "Foo" [("a", uint256); ("b", DynArray uint256 2)];
    privar "f" (StructT "Foo");
    itl_def "bar" [] (StructT "Foo") [
      Return $ SOME $ self_ "f"
    ];
    def "foo" [] (StructT "Foo") [
      AssignSelf "f"
        (StructLit "Foo" [("a", li 1); ("b", DynArlit 2 [li 1; li 1])]);
      AnnAssign "d" (StructT "Foo") (call "bar" []);
      Assign (BaseTarget (AttributeTarget (NameTarget "d") "a")) (li 0);
      Assign (BaseTarget (SubscriptTarget
                           (AttributeTarget (NameTarget "d") "b")
                           (li 0))) (li 0);
      Return $ SOME $ TopLevelName "f"
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_pass_by_value6_ast_def;

Theorem test_pass_by_value6:
  load_and_call_foo test_pass_by_value6_ast =
  INL (StructV [("a", IntV 1); ("b", ArrayV (Dynamic 2) [IntV 1; IntV 1])])
Proof
  CONV_TAC cv_eval
QED

Definition test_pass_by_value7_ast_def:
  test_pass_by_value7_ast = [
    HashMapDecl Private "h" uint256 (Type (DynArray uint256 2));
    def "foo" [] (DynArray uint256 2) [
      assign (sub (TopLevelNameTarget "h") (li 0)) (DynArlit 2 [li 1; li 1]);
      AnnAssign "d" (DynArray uint256 2) (Subscript (self_ "h") (li 0));
      assign (sub (NameTarget "d") (li 0)) (li 0);
      return (Subscript (self_ "h") (li 0))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_pass_by_value7_ast_def;

Theorem test_pass_by_value7:
  load_and_call_foo test_pass_by_value7_ast =
  INL $ ArrayV (Dynamic 2) [IntV 1; IntV 1]
Proof
  CONV_TAC cv_eval
QED

Definition test_pass_by_value8_ast_def:
  test_pass_by_value8_ast = [
    StructDecl "Foo" [("a", uint256); ("b", DynArray uint256 2)];
    def "foo" [] (StructT "Foo") [
      AnnAssign "f" (StructT "Foo")
        (StructLit "Foo" [("a", li 1); ("b", DynArlit 2 [li 1; li 1])]);
      AnnAssign "d" (DynArray uint256 2) (Attribute (Name "f") "b");
      assign (sub (NameTarget "d") (li 0)) (li 0);
      return (Name "f")
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_pass_by_value8_ast_def;

Theorem test_pass_by_value8:
  load_and_call_foo test_pass_by_value8_ast =
  INL $ StructV [("a", IntV 1); ("b", ArrayV (Dynamic 2) [IntV 1; IntV 1])]
Proof
  CONV_TAC cv_eval
QED

Definition test_max_builtin_ast_def:
  test_max_builtin_ast = [
    def "foo" [] uint256 [
      return $ TypeBuiltin MaxValue uint256
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_max_builtin_ast_def;

Theorem test_max_builtin:
  ISL $ load_and_call_foo test_max_builtin_ast
Proof
  CONV_TAC cv_eval
QED

Definition test_return_constant_ast_def:
  test_return_constant_ast = [
    VariableDecl Private (Constant (li 1)) "u" uint256;
    def "foo" [] uint256 [
      return (Name "u")
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_return_constant_ast_def;

Theorem test_return_constant:
  load_and_call_foo test_return_constant_ast
  = INL (IntV 1)
Proof
  CONV_TAC cv_eval
QED

(* TODO: create minimal proxy tests *)

(* TODO: create copy tests *)

(* TODO: test log *)

(* TODO: test encode static array *)

(* TODO: test storage dump *)

(* TODO: test elif condition *)

(* TODO: assert tests *)
(* TODO: raise tests *)

(* TODO: raw_revert *)
(* TODO: raw_call into acc *)
(* TODO: extcall into acc *)
(* TODO: identity precompile tests *)

(* TODO: test_blah *)

(* TODO: raw_call_with_revert *)

val () = export_theory();
