(* Pinned Vyper serializes folded Decimal.value as source text, including
   expressions such as min(3.0, 5.0), rather than the computed decimal. *)
Theory vyperDecimalFrontendTest
Ancestors
  jsonToVyper vyperInterpreter vyperContext vyperState vyperTestRunner
Libs
  vyperCheckContractFrontendLib cv_transLib

fun holbuild_extra_deps (_ : string list) = ();
val () = holbuild_extra_deps [
  "fixtures/check_contract/decimal_folding.json",
  "fixtures/check_contract/decimal_folding.vy"
];

val fixture = vyperCheckContractFrontendLib.check_contract_result
  {in_deploy = false, address = ``0w : address``,
   annotated_ast = JSONDecode.decodeFile jsonASTLib.annotated_ast
     "fixtures/check_contract/decimal_folding.json",
   storage_layout = JSONDecode.decodeFile jsonASTLib.storage_layout
     "fixtures/check_contract/decimal_folding.json"};

Definition decimal_frontend_machine_def:
  decimal_frontend_machine = initial_machine_state with
    <| sources := [(0w, ^(#modules fixture))]; layouts := ^(#layouts fixture) |>
End
val () = cv_auto_trans decimal_frontend_machine_def;

Definition decimal_frontend_call_def:
  decimal_frontend_call name =
    FST (call_external NONE decimal_frontend_machine
      (empty_call_txn with <| function_name := name; target := 0w |>))
End
val () = cv_auto_trans decimal_frontend_call_def;

(* The exact expression from upstream test_minmax, with its expected scaled
   result. This exercises JSON decoding, translation and the CPS interpreter. *)
Theorem decimal_frontend_minmax:
  decimal_frontend_call "minmax" = INL (DecimalV 582231230000000)
Proof
  CONV_TAC cv_eval
QED

Theorem decimal_frontend_integer_minmax:
  decimal_frontend_call "integer_minmax" = INL (IntV 83)
Proof
  CONV_TAC cv_eval
QED

Theorem decimal_frontend_arithmetic:
  decimal_frontend_call "arithmetic" = INL (DecimalV 92500000000)
Proof
  CONV_TAC cv_eval
QED

Theorem decimal_frontend_negative:
  decimal_frontend_call "negative" = INL (DecimalV (-37500000000))
Proof
  CONV_TAC cv_eval
QED

Theorem decimal_frontend_scientific:
  decimal_frontend_call "scientific" = INL (DecimalV 125000002)
Proof
  CONV_TAC cv_eval
QED

Theorem decimal_frontend_minimum:
  decimal_frontend_call "minimum" =
    INL (DecimalV (-187072209578355573530071658587684226515959365500928))
Proof
  CONV_TAC cv_eval
QED

Theorem decimal_frontend_maximum:
  decimal_frontend_call "maximum" =
    INL (DecimalV 187072209578355573530071658587684226515959365500927)
Proof
  CONV_TAC cv_eval
QED
