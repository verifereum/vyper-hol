(* TOP-LEVEL: exact membership of the builtin manifest fixtures. *)
Theory supportedFixturesBuiltins
Ancestors supportedProgram evalCompilerSubsetBuiltins
Libs supportedEvalLib intLib

val () = supportedEvalLib.configure ();

Theorem account_items_supported_program:
  supported_program evalCompilerSubsetBuiltins$account_items_program
Proof
  EVAL_TAC
QED

Theorem ec_builtins_supported_program:
  supported_program evalCompilerSubsetBuiltins$ec_builtins_program
Proof
  EVAL_TAC
QED

Theorem env_block_supported_program:
  supported_program evalCompilerSubsetBuiltins$env_block_program
Proof
  EVAL_TAC
QED

Theorem env_message_core_supported_program:
  supported_program evalCompilerSubsetBuiltins$env_message_core_program
Proof
  EVAL_TAC
QED

Theorem env_tx_chain_supported_program:
  supported_program evalCompilerSubsetBuiltins$env_tx_chain_program
Proof
  EVAL_TAC
QED

Theorem hash_builtins_supported_program:
  supported_program evalCompilerSubsetBuiltins$hash_builtins_program
Proof
  EVAL_TAC
QED
