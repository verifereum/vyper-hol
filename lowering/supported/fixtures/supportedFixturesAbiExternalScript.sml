(* TOP-LEVEL: exact membership of externally callable ABI fixtures. *)
Theory supportedFixturesAbiExternal
Ancestors supportedProgram evalCompilerSubsetAbiExternal
Libs supportedEvalLib intLib

val () = supportedEvalLib.configure ();

Theorem external_arrays_supported_program:
  supported_program evalCompilerSubsetAbiExternal$task090_external_arrays_program
Proof
  EVAL_TAC
QED

Theorem external_dynamic_supported_program:
  supported_program evalCompilerSubsetAbiExternal$task090_external_dynamic_program
Proof
  EVAL_TAC
QED

Theorem external_scalars_supported_program:
  supported_program evalCompilerSubsetAbiExternal$task090_external_scalars_program
Proof
  EVAL_TAC
QED

Theorem external_struct_supported_program:
  supported_program evalCompilerSubsetAbiExternal$task090_external_struct_program
Proof
  EVAL_TAC
QED
