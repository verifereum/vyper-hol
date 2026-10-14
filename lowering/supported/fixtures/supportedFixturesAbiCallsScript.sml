(* TOP-LEVEL: exact membership of aggregate internal and interface calls. *)
Theory supportedFixturesAbiCalls
Ancestors supportedProgram evalCompilerSubsetAbiInternalCalls
  evalCompilerSubsetAbiExternalCalls
Libs supportedEvalLib intLib

val () = supportedEvalLib.configure ();

Theorem internal_bytes_call_supported_program:
  supported_program evalCompilerSubsetAbiInternalCalls$task090_internal_bytes_call_program
Proof
  EVAL_TAC
QED

Theorem internal_struct_call_supported_program:
  supported_program evalCompilerSubsetAbiInternalCalls$task090_internal_struct_call_program
Proof
  EVAL_TAC
QED

Theorem internal_tuple_call_supported_program:
  supported_program evalCompilerSubsetAbiInternalCalls$task090_internal_tuple_call_program
Proof
  EVAL_TAC
QED

Theorem interface_calls_supported_program:
  supported_program evalCompilerSubsetAbiExternalCalls$task090_interface_calls_program
Proof
  EVAL_TAC
QED

Theorem send_value_supported_program:
  supported_program evalCompilerSubsetAbiExternalCalls$task090_send_value_program
Proof
  EVAL_TAC
QED
