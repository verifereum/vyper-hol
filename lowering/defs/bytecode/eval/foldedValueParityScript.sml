(* TOP-LEVEL: seven independent Python-oracle parity results.
   Compiler evaluations are split into bounded stages in folded/. *)
Theory foldedValueParity
Ancestors
  foldedValueParityAdd foldedValueParityPow foldedValueParityConstants
  foldedValueParityAbi
Libs foldedValueParityLib

Theorem fold_add_python_parity:
  ^(concl foldedValueParityAddTheory.fold_add_python_parity)
Proof
  ACCEPT_TAC foldedValueParityAddTheory.fold_add_python_parity
QED

Theorem pow_folded_exp_python_parity:
  ^(concl foldedValueParityPowTheory.pow_folded_exp_python_parity)
Proof
  ACCEPT_TAC foldedValueParityPowTheory.pow_folded_exp_python_parity
QED

Theorem fold_cmp_python_parity:
  ^(concl foldedValueParityConstantsTheory.fold_cmp_python_parity)
Proof
  ACCEPT_TAC foldedValueParityConstantsTheory.fold_cmp_python_parity
QED

Theorem enc_mid_const_python_parity:
  ^(concl foldedValueParityAbiTheory.enc_mid_const_python_parity)
Proof
  ACCEPT_TAC foldedValueParityAbiTheory.enc_mid_const_python_parity
QED

Theorem fold_powmod_python_parity:
  ^(concl foldedValueParityConstantsTheory.fold_powmod_python_parity)
Proof
  ACCEPT_TAC foldedValueParityConstantsTheory.fold_powmod_python_parity
QED

Theorem fold_addmod_python_parity:
  ^(concl foldedValueParityConstantsTheory.fold_addmod_python_parity)
Proof
  ACCEPT_TAC foldedValueParityConstantsTheory.fold_addmod_python_parity
QED

Theorem fold_abs_python_parity:
  ^(concl foldedValueParityConstantsTheory.fold_abs_python_parity)
Proof
  ACCEPT_TAC foldedValueParityConstantsTheory.fold_abs_python_parity
QED

val () = foldedValueParityLib.audit "foldedValueParity";
