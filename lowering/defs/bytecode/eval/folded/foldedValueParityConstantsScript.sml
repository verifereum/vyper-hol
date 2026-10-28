(* TOP-LEVEL: fold_cmp, fold_powmod, fold_addmod, fold_abs Python parity. *)
Theory foldedValueParityConstants
Ancestors
  foldedValueParityCompute compileVyper supportedProgram concretizeMemLocDefs
  codegenReadyCompute byte option alist integer_word
Libs foldedValueParityLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps
  ["../../folded-value-oracle", "../../folded-value-parity-fixtures.txt"];
val () = foldedValueParityLib.setup ();
val fixture_root = "../../folded-value-oracle";
fun input name = foldedValueParityLib.input fixture_root name;
fun expected name = foldedValueParityLib.expected fixture_root name;

Theorem fold_cmp_python_parity:
  compile_vyper (K SOME) (o1_policy all_capabilities) ^(input "fold_cmp") =
    SOME ^(expected "fold_cmp")
Proof
  PARITY_NORMALIZE_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  eval_call ``codegen_ready`` >>
  PARITY_NORMALIZE_TAC >>
  eval_call ``finalize_codegen`` >>
  PARITY_NORMALIZE_TAC >>
  eval_call ``lower_vyper_deploy_unit`` >>
  PARITY_NORMALIZE_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  eval_call ``codegen_ready`` >>
  PARITY_NORMALIZE_TAC >>
  eval_call ``finalize_codegen`` >>
  EVAL_TAC
QED

Theorem fold_powmod_python_parity:
  compile_vyper (K SOME) (o1_policy all_capabilities) ^(input "fold_powmod") =
    SOME ^(expected "fold_powmod")
Proof
  PARITY_NORMALIZE_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  eval_call ``codegen_ready`` >>
  PARITY_NORMALIZE_TAC >>
  eval_call ``finalize_codegen`` >>
  PARITY_NORMALIZE_TAC >>
  eval_call ``lower_vyper_deploy_unit`` >>
  PARITY_NORMALIZE_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  eval_call ``codegen_ready`` >>
  PARITY_NORMALIZE_TAC >>
  eval_call ``finalize_codegen`` >>
  EVAL_TAC
QED

Theorem fold_addmod_python_parity:
  compile_vyper (K SOME) (o1_policy all_capabilities) ^(input "fold_addmod") =
    SOME ^(expected "fold_addmod")
Proof
  PARITY_NORMALIZE_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  eval_call ``codegen_ready`` >>
  PARITY_NORMALIZE_TAC >>
  eval_call ``finalize_codegen`` >>
  PARITY_NORMALIZE_TAC >>
  eval_call ``lower_vyper_deploy_unit`` >>
  PARITY_NORMALIZE_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  eval_call ``codegen_ready`` >>
  PARITY_NORMALIZE_TAC >>
  eval_call ``finalize_codegen`` >>
  EVAL_TAC
QED

Theorem fold_abs_python_parity:
  compile_vyper (K SOME) (o1_policy all_capabilities) ^(input "fold_abs") =
    SOME ^(expected "fold_abs")
Proof
  PARITY_NORMALIZE_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  eval_call ``codegen_ready`` >>
  PARITY_NORMALIZE_TAC >>
  eval_call ``finalize_codegen`` >>
  PARITY_NORMALIZE_TAC >>
  eval_call ``lower_vyper_deploy_unit`` >>
  PARITY_NORMALIZE_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  PARITY_PASS_TAC >>
  eval_call ``codegen_ready`` >>
  PARITY_NORMALIZE_TAC >>
  eval_call ``finalize_codegen`` >>
  EVAL_TAC
QED

val () = audit "foldedValueParityConstants";
