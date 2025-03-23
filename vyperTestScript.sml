open HolKernel boolLib bossLib Parse intLib wordsLib cv_transLib;
open numeralTheory arithmeticTheory finite_mapTheory;
open vyperAstTheory vyperInterpreterTheory;

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
       For "i" uint256 (Name "a") 10
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
      For "i" uint256 (Name "a") 10 [
        AugAssign (NameTarget "counter") Add (Name "i")
      ];
      Return (SOME (Name "counter"))
    ];
    def "foo" [] uint256 [
      AnnAssign "a" (DynArray uint256 10)
        (DynArlit 10 [li 1; li 2; li 3]);
      AnnAssign "counter" uint256 (li 0);
      For "i" uint256 (Name "a") 10 [
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
      For "i" uint256 (Name "a") 10 [
        AugAssign (TopLevelNameTarget "d") Add (Name "i")
      ]
    ];
    def "foo" [] uint256 [
      AnnAssign "a" (DynArray uint256 10)
        (DynArlit 10 [li 1; li 2; li 3]);
      AnnAssign "counter" uint256 (li 0);
      For "i" uint256 (Name "a") 10 [
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

(* TODO: add

Theorem test_statefulness_of_tstorage:
    for i in range(3):
        assert c.foo() == 2

*)

Definition test_default_storage_values_ast_def:
  test_default_storage_values_ast = [
    StructDef "S" [("a", uint256)];
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

(* TODO range builtin tests *)

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

(* TODO add tests

def test_external_func_arg2():
    src = """
@external
def foo(a: DynArray[uint256, 10], s: String[100]) -> (DynArray[uint256, 10], String[100]):
    return a, s
    """

    c = loads(src)
    assert c.foo([1, 2, 3], "hello") == ([1, 2, 3], "hello")


def test_external_func_arg3():
    dynarray_t = "DynArray[DynArray[uint256, 10], 10]"
    src = f"""
@external
def foo(a: DynArray[uint256, 10], s: String[100], b: {dynarray_t}) -> (DynArray[uint256, 10], String[100], {dynarray_t}):
    return a, s, b
    """

    c = loads(src)
    complex_array = [[4, 5, 6], [7, 8, 9, 10, 11], [], [12]]
    assert c.foo([1, 2, 3], "hello", complex_array) == (
        [1, 2, 3],
        "hello",
        complex_array,
    )


def test_external_func_arg4():
    tuple_t = "(String[93], DynArray[DynArray[uint256, 10], 10])"
    src = f"""
@external
def foo(a: DynArray[uint256, 10], s: String[100], b: {tuple_t}) -> (DynArray[uint256, 10], String[100], {tuple_t}):
    return a, s, b
    """

    c = loads(src)
    complex_tuple = ("apollo", [[4, 5, 6], [7, 8, 9, 10, 11], [], [12]])
    assert c.foo([1, 2, 3], "hello", complex_tuple) == (
        [1, 2, 3],
        "hello",
        complex_tuple,
    )


def test_empty_builtin():
    src = """
@external
def foo() -> uint256:
    return empty(uint256)
    """

    c = loads(src)
    assert c.foo() == 0


def test_empty_builtin2():
    src = """
@external
def foo() -> String[56]:
    return empty(String[56])
    """

    c = loads(src)
    assert c.foo() == ""


def test_empty_builtin3():
    src = """
@external
def foo() -> DynArray[String[32], 10]:
    return empty(DynArray[String[32], 10])
    """

    c = loads(src)
    assert c.foo() == []
*)

val () = export_theory();
