(* TOP-LEVEL: seven independent Python-oracle parity results.
   Compiler evaluations are split into bounded stages in folded/. *)
Theory foldedValueParity
Ancestors
  foldedValueParityAdd foldedValueParityPow foldedValueParityConstants
  foldedValueParityAbi compileVyper
Libs foldedValueParityLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps
  ["../folded-value-oracle", "../folded-value-parity-fixtures.txt"];
val fixture_root = "../folded-value-oracle";
fun input name = foldedValueParityLib.input fixture_root name;
fun expected name = foldedValueParityLib.expected fixture_root name;

Theorem fold_add_python_parity:
  compile_vyper (K SOME) (o1_policy all_capabilities) ^(input "fold_add") =
    SOME ^(expected "fold_add")
Proof
  ACCEPT_TAC foldedValueParityAddTheory.fold_add_python_parity
QED

Theorem pow_folded_exp_python_parity:
  compile_vyper (K SOME) (o1_policy all_capabilities) ^(input "pow_folded_exp") =
    SOME ^(expected "pow_folded_exp")
Proof
  ACCEPT_TAC foldedValueParityPowTheory.pow_folded_exp_python_parity
QED

Theorem fold_cmp_python_parity:
  compile_vyper (K SOME) (o1_policy all_capabilities) ^(input "fold_cmp") =
    SOME ^(expected "fold_cmp")
Proof
  ACCEPT_TAC foldedValueParityConstantsTheory.fold_cmp_python_parity
QED

Theorem enc_mid_const_python_parity:
  compile_vyper (K SOME) (o1_policy all_capabilities) ^(input "enc_mid_const") =
    SOME ^(expected "enc_mid_const")
Proof
  ACCEPT_TAC foldedValueParityAbiTheory.enc_mid_const_python_parity
QED

Theorem fold_powmod_python_parity:
  compile_vyper (K SOME) (o1_policy all_capabilities) ^(input "fold_powmod") =
    SOME ^(expected "fold_powmod")
Proof
  ACCEPT_TAC foldedValueParityConstantsTheory.fold_powmod_python_parity
QED

Theorem fold_addmod_python_parity:
  compile_vyper (K SOME) (o1_policy all_capabilities) ^(input "fold_addmod") =
    SOME ^(expected "fold_addmod")
Proof
  ACCEPT_TAC foldedValueParityConstantsTheory.fold_addmod_python_parity
QED

Theorem fold_abs_python_parity:
  compile_vyper (K SOME) (o1_policy all_capabilities) ^(input "fold_abs") =
    SOME ^(expected "fold_abs")
Proof
  ACCEPT_TAC foldedValueParityConstantsTheory.fold_abs_python_parity
QED

val () = foldedValueParityLib.audit "foldedValueParity";
