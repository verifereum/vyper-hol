(* Membership in a static array must see the slots holding the element type's
   default value.  Static arrays are stored sparsely (make_array_value drops
   default-valued slots), so `x in arr` needs the array's static type to know
   that such slots exist.  Expected values follow Vyper: `0 in [0, 7]` is true. *)
Theory vyperInStaticArrayTest
Ancestors
  vyperInterpreter vyperSmallStep vyperState vyperContext vyperAST vyperValue
  vyperValueOperation vyperTypeSystem jsonToVyper vyperTestRunner
  list option pair words
Libs
  vyperCheckContractFrontendLib vyperTestLib vyperTestRunnerLib cv_transLib

val () = holbuild_extra_deps ["fixtures/check_contract/in_static_array.json"];

(* The sparse value alone cannot show the omitted slot; the static type can. *)
Theorem evaluate_in_array_static_default_slot:
  evaluate_in_array (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) (IntV 0)
    (SArrayV [(1, IntV 7)]) /\
  ~evaluate_in_array (ArrayTV (BaseTV (UintT 256)) (Fixed 1)) (IntV 0)
    (SArrayV [(0, IntV 7)]) /\
  ~evaluate_in_array NoneTV (IntV 0) (SArrayV [(1, IntV 7)])
Proof
  EVAL_TAC
QED

(* The builtin passes the second operand's type on to the membership test. *)
Theorem evaluate_builtin_membership_uses_operand_type:
  evaluate_builtin cx acc (BaseT BoolT) (Bop In)
    [BaseT (UintT 256); ArrayT (BaseT (UintT 256)) (Fixed 2)]
    [IntV 0; ArrayV (SArrayV [(1, IntV 7)])] = INL (BoolV T) /\
  evaluate_builtin cx acc (BaseT BoolT) (Bop NotIn)
    [BaseT (UintT 256); ArrayT (BaseT (UintT 256)) (Fixed 2)]
    [IntV 0; ArrayV (SArrayV [(1, IntV 7)])] = INL (BoolV F)
Proof
  EVAL_TAC
QED

(* Pinned Vyper output for fixtures/check_contract/in_static_array.vy, so the
   array operand's type annotation is the one the frontend produces. *)
val fixture = vyperCheckContractFrontendLib.check_contract_result_legacy
  {in_deploy = false, address = ``0w : address``,
   annotated_ast = JSONDecode.decodeFile jsonASTLib.annotated_ast
     "fixtures/check_contract/in_static_array.json",
   storage_layout = JSONDecode.decodeFile jsonASTLib.storage_layout
     "fixtures/check_contract/in_static_array.json"};

Definition in_static_array_machine_def:
  in_static_array_machine = initial_machine_state with
    <| sources := [(0w, ^(#modules fixture))]; layouts := ^(#layouts fixture) |>
End
val () = cv_auto_trans in_static_array_machine_def;

Definition in_static_array_call_def:
  in_static_array_call name args =
    FST (call_external NONE in_static_array_machine
      (empty_call_txn with <| function_name := name; target := 0w; args := args |>))
End
val () = cv_auto_trans in_static_array_call_def;

(* One observation per entry point, so a failure names the case. *)
Theorem zero_in_literal_static_array:
  in_static_array_call "zero_in_literal" [] = INL (BoolV T)
Proof
  CONV_TAC cv_eval
QED

Theorem zero_not_in_literal_static_array:
  in_static_array_call "zero_not_in_literal" [] = INL (BoolV F)
Proof
  CONV_TAC cv_eval
QED

Theorem nonzero_probe_not_in_literal_static_array:
  in_static_array_call "one_in_literal" [] = INL (BoolV F)
Proof
  CONV_TAC cv_eval
QED

Theorem zero_in_empty_local_static_array:
  in_static_array_call "zero_in_empty_local" [] = INL (BoolV T)
Proof
  CONV_TAC cv_eval
QED

Theorem empty_address_in_static_array_pair:
  in_static_array_call "empty_address_in_pair" [AddressV 1w] = INL (BoolV T) /\
  in_static_array_call "empty_address_in_pair" [AddressV 0w] = INL (BoolV T)
Proof
  CONV_TAC cv_eval
QED

(* The same literal through the CPS machine. Vyper types the literals of
   `0 in [0, 7]` as int8; uint256 is used here since the default value, which
   is what the test is about, is IntV 0 either way. *)
Definition zero_in_literal_expr_def:
  zero_in_literal_expr =
    Builtin (BaseT BoolT) (Bop In)
      [Literal (BaseT (UintT 256)) (IntL 0);
       Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2))
         (MakeArray (SOME (BaseT (UintT 256))) (Fixed 2))
         [Literal (BaseT (UintT 256)) (IntL 0);
          Literal (BaseT (UintT 256)) (IntL 7)]]
End
val () = cv_auto_trans zero_in_literal_expr_def;

Theorem zero_in_literal_static_array_cps:
  FST (fromtvk (cont (eval_expr_cps empty_evaluation_context
    zero_in_literal_expr empty_state DoneK))) = INL (Value (BoolV T))
Proof
  CONV_TAC cv_eval
QED

(* Replay of the traces Vyper's own test harness recorded for
   fixtures/exports/in_static_array/test_in_static_array.py at the pinned
   compiler: a source deployment, then each call's output as Vyper's EVM
   produced it. *)
val () = holbuild_extra_deps [
  "fixtures/exports/in_static_array/test_in_static_array.json",
  "fixtures/exports/in_static_array/test_in_static_array.json.provenance",
  "fixtures/exports/in_static_array/test_in_static_array.py"
];
val () = make_definitions_for_file
  ("in_static_array", "fixtures/exports/in_static_array/test_in_static_array.json");
val traces = all_traces "-";
val () = if List.null traces then raise Fail "in_static_array: no traces replayed"
         else List.app run_test_on_traces traces;
