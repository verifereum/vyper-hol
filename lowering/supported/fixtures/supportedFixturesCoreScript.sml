(* TOP-LEVEL: exact PLAN 5.6 membership for the core manifest fixtures.
   Membership only, not compiler correctness or bytecode parity. *)
Theory supportedFixturesCore
Ancestors supportedProgram evalCompiler
Libs supportedEvalLib

val () = supportedEvalLib.configure ();

Theorem empty_supported_program:
  supported_program []
Proof
  EVAL_TAC
QED

Theorem noop_supported_program:
  supported_program evalCompiler$noop_program
Proof
  EVAL_TAC
QED

Theorem return_uint_supported_program:
  supported_program evalCompiler$return_uint_program
Proof
  EVAL_TAC
QED

Theorem return_arg_supported_program:
  supported_program evalCompiler$return_arg_program
Proof
  EVAL_TAC
QED

Theorem local_uint_supported_program:
  supported_program evalCompiler$local_uint_program
Proof
  EVAL_TAC
QED

Theorem add_arg_supported_program:
  supported_program evalCompiler$add_arg_program
Proof
  EVAL_TAC
QED

Theorem storage_read_supported_program:
  supported_program evalCompiler$storage_read_program
Proof
  EVAL_TAC
QED

Theorem storage_write_supported_program:
  supported_program evalCompiler$storage_write_program
Proof
  EVAL_TAC
QED

Theorem deploy_storage_supported_program:
  supported_program evalCompiler$deploy_storage_program
Proof
  EVAL_TAC
QED

Theorem event_log_supported_program:
  supported_program evalCompiler$event_log_program
Proof
  EVAL_TAC
QED

Theorem indexed_event_log_supported_program:
  supported_program evalCompiler$indexed_event_log_program
Proof
  EVAL_TAC
QED
