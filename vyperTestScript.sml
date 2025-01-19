open HolKernel boolLib bossLib Parse intLib wordsLib cv_transLib;
open numeralTheory arithmeticTheory finite_mapTheory;
open vyperAstTheory vyperVmTheory;

val () = new_theory "vyperTest";

Overload uint256 = “BaseT (UintT (n2w 32 (* 256 DIV 8 *)))”
Overload address = “BaseT AddressT”
Overload intlit = “λi. Literal (IntL i)”
Overload "==" = “λe1 e2. Builtin Eq [e1; e2]”
Overload "+" = “λe1 e2. Builtin (Bop Add) [e1; e2]”
Overload len = “λe. Builtin Len [e]”
Overload defun = “λid args ret body. FunctionDef External Nonpayable id args ret body”
Overload DynArray = “λt n. ArrayT t (Dynamic n)”
Overload DynArlit = “λn ls. ArrayLit (SOME (Dynamic n)) ls”

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
    defun "foo" [] uint256
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
    defun "foo" [] uint256
    [
       AnnAssign "a" (DynArray uint256 10)
         (DynArlit 10 [intlit 1; intlit 2; intlit 3]);
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
    defun "foo" [] uint256
    [
      AnnAssign "bar" (DynArray uint256 10)
        (DynArlit 10 [intlit 1; intlit 2]);
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
    VariableDecl Private Storage "a" (DynArray uint256 10);
    defun "foo" [] uint256 [
      Assign (BaseTarget (GlobalNameTarget "a"))
        (DynArlit 10 [intlit 1; intlit 2]);
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
    FunctionDef Internal Nonpayable "bar" [] uint256 [
      AnnAssign "a" (DynArray uint256 10)
        (DynArlit 10 [intlit 1; intlit 2; intlit 3]);
      AnnAssign "counter" uint256 (intlit 0);
      For "i" uint256 (Name "a") 10 [
        AugAssign (NameTarget "counter") Add (Name "i")
      ];
      Return (SOME (Name "counter"))
    ];
    defun "foo" [] uint256 [
      AnnAssign "a" (DynArray uint256 10)
        (DynArlit 10 [intlit 1; intlit 2; intlit 3]);
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
    VariableDecl Private Storage "a" uint256;
    FunctionDef Internal Nonpayable "bar" [] VoidT [
      Assign (BaseTarget (GlobalNameTarget "a")) (intlit 42)
    ];
    defun "foo" [] uint256 [
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
    FunctionDef Internal Nonpayable "baz" [("a", uint256)] uint256 [
      Return (SOME (Name "a"))
    ];
    FunctionDef Internal Nonpayable "bar" [("a", uint256)] uint256 [
      Return (SOME (Name "a" + Call "baz" [intlit 3]))
    ];
    defun "foo" [] uint256 [
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
    FunctionDef Internal Nonpayable "baz" [("a", uint256)] uint256 [
      Return (SOME (Name "a"))
    ];
    FunctionDef Internal Nonpayable "bar" [("a", uint256)] uint256 [
      Return (SOME (Call "baz" [intlit 3] + Name "a"))
    ];
    defun "foo" [] uint256 [
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
    VariableDecl Private Storage "d" uint256;
    defun "foo" [] uint256 [
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
    VariableDecl Private Storage "d" uint256;
    VariableDecl Private Storage "k" uint256;
    defun "foo" [] uint256 [
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
    VariableDecl Private Storage "d" uint256;
    FunctionDef Internal Nonpayable "bar" [] VoidT [
      AnnAssign "a" (DynArray uint256 10)
        (DynArlit 10 [intlit 1; intlit 2; intlit 3]);
      For "i" uint256 (Name "a") 10 [
        AugAssign (GlobalNameTarget "d") Add (Name "i")
      ]
    ];
    defun "foo" [] uint256 [
      AnnAssign "a" (DynArray uint256 10)
        (DynArlit 10 [intlit 1; intlit 2; intlit 3]);
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
    VariableDecl Private Storage "d" uint256;
    defun "foo" [] uint256 [
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
    VariableDecl Private Storage "d" uint256;
    defun "foo" [] uint256 [
      AugAssign (GlobalNameTarget "d") Add (intlit 1);
      Return (SOME (GlobalName "d"))
    ];
    defun "bar" [] uint256 [
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

Definition test_tstorage_variables0_ast_def:
  test_tstorage_variables0_ast = [
    VariableDecl Private Transient "d" uint256;
    VariableDecl Private Transient "k" uint256;
    defun "foo" [] uint256 [
      Assign (BaseTarget (GlobalNameTarget "k")) (intlit 1);
      Assign (BaseTarget (GlobalNameTarget "d")) (GlobalName "k");
      AugAssign (GlobalNameTarget "d") Add (GlobalName "k");
      Return (SOME (GlobalName "d" + GlobalName "k"))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_tstorage_variables0_ast_def;

Theorem test_tstorage_variables0:
  FST $ external_call
   (load_contract initial_machine_state
      addr test_tstorage_variables0_ast)
    addr "foo" []
  = INL (IntV 3)
Proof
  rw[external_call_def, load_contract_def, initial_machine_state_def,
     SimpLHS, pair_case_rand]
  \\ CONV_TAC(LAND_CONV cv_eval) \\ rw[]
QED

Definition test_tstorage_variables2_ast_def:
  test_tstorage_variables2_ast = [
    VariableDecl Private Transient "d" uint256;
    VariableDecl Private Transient "k" uint256;
    defun "foo" [] uint256 [
      If (GlobalName "k" == intlit 0) [
        Assign (BaseTarget (GlobalNameTarget "k")) (intlit 1)
      ] [];
      Assign (BaseTarget (GlobalNameTarget "d")) (GlobalName "k");
      AugAssign (GlobalNameTarget "d") Add (GlobalName "k");
      Return (SOME (GlobalName "d" + GlobalName "k"))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_tstorage_variables2_ast_def;

Theorem test_tstorage_variables2:
  FST $ external_call
   (load_contract initial_machine_state
      addr test_tstorage_variables2_ast)
    addr "foo" []
  = INL (IntV 3)
Proof
  rw[external_call_def, load_contract_def, initial_machine_state_def,
     SimpLHS, pair_case_rand]
  \\ CONV_TAC(LAND_CONV cv_eval) \\ rw[]
QED

(* TODO add

def test_statefulness_of_tstorage():
    src = """
d: transient(uint256)

interface Bar:
    def bar() -> uint256: payable

@external
def foo() -> uint256:
    self.d += 1
    return extcall Bar(self).bar()

@external
def bar() -> uint256:
    self.d += 1
    return self.d
    """

    c = loads(src)
    for i in range(3):
        assert c.foo() == 2

Definition test_statefulness_of_tstorage_ast_def:
  test_statefulness_of_tstorage_ast = [
    VariableDecl "d" uint256 Private Transient;
  ]
End

val () = cv_trans_deep_embedding EVAL test_statefulness_of_tstorage_ast_def;
*)

Definition test_default_storage_values_ast_def:
  test_default_storage_values_ast = [
    StructDef "S" [("a", uint256)];
    VariableDecl Private Storage "a" uint256;
    VariableDecl Private Storage "b" uint256;
    VariableDecl Private Storage "c" (DynArray uint256 10);
    VariableDecl Private Storage "d" (StructT "S");
    VariableDecl Private Storage "e" (BaseT (BytesT (Dynamic 10)));
    VariableDecl Private Storage "f" (BaseT (StringT 10));
    defun "foo" [] uint256 [
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
    defun "foo" [] uint256 [
      AnnAssign "a" (DynArray uint256 3)
        (DynArlit 3 [intlit 1; intlit 2; intlit 3]);
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

Definition test_len_builtin2_ast_def:
  test_len_builtin2_ast = [
    VariableDecl Private Storage "d" (DynArray uint256 3);
    defun "foo" [] uint256 [
      Return (SOME (len (GlobalName "d")))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_len_builtin2_ast_def;

Theorem test_len_builtin2:
  FST $ external_call
   (load_contract initial_machine_state
      addr test_len_builtin2_ast)
    addr "foo" []
  = INL (IntV 0)
Proof
  rw[external_call_def, load_contract_def, initial_machine_state_def,
     SimpLHS, pair_case_rand]
  \\ CONV_TAC(LAND_CONV cv_eval) \\ rw[]
QED

Definition test_len_builtin3_ast_def:
  test_len_builtin3_ast = [
    VariableDecl Private Storage "s" (BaseT (StringT 10));
    defun "foo" [] uint256 [
      Assign (BaseTarget (GlobalNameTarget "s")) (Literal (StringL 10 "hello"));
      Return (SOME (len (GlobalName "s")))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_len_builtin3_ast_def;

Theorem test_len_builtin3:
  FST $ external_call
   (load_contract initial_machine_state
      addr test_len_builtin3_ast)
    addr "foo" []
  = INL (IntV 5)
Proof
  rw[external_call_def, load_contract_def, initial_machine_state_def,
     SimpLHS, pair_case_rand]
  \\ CONV_TAC(LAND_CONV cv_eval) \\ rw[]
QED

Definition test_len_builtin4_ast_def:
  test_len_builtin4_ast = [
    VariableDecl Private Storage "s" (BaseT (BytesT (Dynamic 10)));
    defun "foo" [] uint256 [
      Assign (BaseTarget (GlobalNameTarget "s"))
        (Literal (BytesL (Dynamic 10)
          ^(rhs $ concl $ EVAL “MAP (n2w o ORD) "hello" : word8 list”)));
      Return (SOME (len (GlobalName "s")))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_len_builtin4_ast_def;

Theorem test_len_builtin4:
  FST $ external_call
   (load_contract initial_machine_state
      addr test_len_builtin4_ast)
    addr "foo" []
  = INL (IntV 5)
Proof
  rw[external_call_def, load_contract_def, initial_machine_state_def,
     SimpLHS, pair_case_rand]
  \\ CONV_TAC(LAND_CONV cv_eval) \\ rw[]
QED

(* TODO: test abi_encode *)

(* TODO: test self call *)

(* TODO: test default arg value *)

Definition test_external_func_arg_ast_def:
  test_external_func_arg_ast = [
    defun "foo" [("a", uint256)] uint256 [
      Return (SOME (Name "a"))
    ]
  ]
End

val () = cv_trans_deep_embedding EVAL test_external_func_arg_ast_def;

Theorem test_external_func_arg:
  FST $ external_call
   (load_contract initial_machine_state
      addr test_external_func_arg_ast)
    addr "foo" [IntV 42]
  = INL (IntV 42)
Proof
  rw[external_call_def, load_contract_def, initial_machine_state_def,
     SimpLHS, pair_case_rand]
  \\ CONV_TAC(LAND_CONV cv_eval) \\ rw[]
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
