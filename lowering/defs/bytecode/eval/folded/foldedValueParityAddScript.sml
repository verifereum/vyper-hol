(* TOP-LEVEL: fold_add_python_parity. *)
Theory foldedValueParityAdd
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

Theorem fold_add_python_parity:
  compile_vyper (K SOME) (o1_policy all_capabilities) ^(input "fold_add") =
    SOME ^(expected "fold_add")
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

val () = audit "foldedValueParityAdd";
