(* TOP-LEVEL: exact PLAN 5.6 membership for the control manifest fixtures.
   Includes the four corrected literal-range ASTs, unchanged here. *)
Theory supportedFixturesControl
Ancestors supportedProgram evalCompiler
Libs intLib

Theorem mixed_event_log_supported_program:
  supported_program evalCompiler$mixed_event_log_program
Proof
  EVAL_TAC
QED

Theorem hashmap_read_supported_program:
  supported_program evalCompiler$hashmap_read_program
Proof
  EVAL_TAC
QED

Theorem hashmap_write_supported_program:
  supported_program evalCompiler$hashmap_write_program
Proof
  EVAL_TAC
QED

Theorem if_bool_supported_program:
  supported_program evalCompiler$if_bool_program
Proof
  EVAL_TAC
QED

Theorem if_join_supported_program:
  supported_program evalCompiler$if_join_program
Proof
  EVAL_TAC
QED

Theorem for_pass_supported_program:
  supported_program evalCompiler$for_pass_program
Proof
  EVAL_TAC
QED

Theorem for_accum_supported_program:
  supported_program evalCompiler$for_accum_program
Proof
  EVAL_TAC
QED

Theorem for_continue_supported_program:
  supported_program evalCompiler$for_continue_program
Proof
  EVAL_TAC
QED

Theorem for_break_supported_program:
  supported_program evalCompiler$for_break_program
Proof
  EVAL_TAC
QED

Theorem internal_call_supported_program:
  supported_program evalCompiler$internal_call_program
Proof
  EVAL_TAC
QED

Theorem internal_call_arg_supported_program:
  supported_program evalCompiler$internal_call_arg_program
Proof
  EVAL_TAC
QED
