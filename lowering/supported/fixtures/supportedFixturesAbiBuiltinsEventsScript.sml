(* TOP-LEVEL: exact membership of ABI encoder/decoder and event fixtures. *)
Theory supportedFixturesAbiBuiltinsEvents
Ancestors supportedProgram evalCompilerSubsetAbiBuiltins evalCompilerSubsetAbiEvents
Libs supportedEvalLib intLib

val () = supportedEvalLib.configure ();

Theorem abi_dynamic_supported_program:
  supported_program evalCompilerSubsetAbiBuiltins$task090_abi_dynamic_program
Proof
  EVAL_TAC
QED

Theorem abi_static_supported_program:
  supported_program evalCompilerSubsetAbiBuiltins$task090_abi_static_program
Proof
  EVAL_TAC
QED

Theorem mixed_event_types_supported_program:
  supported_program evalCompilerSubsetAbiEvents$task090_mixed_event_types_program
Proof
  EVAL_TAC
QED
