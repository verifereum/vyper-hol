Theory runtimeSymSrcBuiltinContracts
Ancestors
  runtimeSymSrcGeneratorContracts runtimeSymSrcBuiltinByteSimple
  runtimeSymSrcBuiltinHash runtimeSymSrcBuiltinMisc runtimeSymSrcBuiltinStrings

Theorem runtime_sym_simple_contract:
  runtime_sym_simple_clauses
Proof
  rewrite_tac[runtime_sym_simple_clauses_def] >> rpt conj_tac
  >- metis_tac[runtime_sym_builtin_abs]
  >- metis_tac[runtime_sym_builtin_calldatasize]
  >- metis_tac[runtime_sym_slice_calldata]
  >- metis_tac[runtime_sym_uint2str] >>
  metis_tac[runtime_sym_builtin_empty_complex]
QED

Theorem runtime_sym_misc_contract:
  runtime_sym_misc_clauses
Proof
  ACCEPT_TAC runtimeSymSrcBuiltinMiscTheory.runtime_sym_misc_clauses
QED
