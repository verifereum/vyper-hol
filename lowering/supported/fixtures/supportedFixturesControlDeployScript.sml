(* TOP-LEVEL: exact membership of assertion, raise, loop and mode fixtures. *)
Theory supportedFixturesControlDeploy
Ancestors supportedProgram evalCompilerSubsetControlDeploy
Libs supportedEvalLib intLib

val () = supportedEvalLib.configure ();

Theorem assert_bare_supported_program:
  supported_program evalCompilerSubsetControlDeploy$assert_bare_program
Proof
  EVAL_TAC
QED

Theorem assert_reason_supported_program:
  supported_program evalCompilerSubsetControlDeploy$assert_reason_program
Proof
  EVAL_TAC
QED

Theorem raise_bare_supported_program:
  supported_program evalCompilerSubsetControlDeploy$raise_bare_program
Proof
  EVAL_TAC
QED

Theorem raise_reason_supported_program:
  supported_program evalCompilerSubsetControlDeploy$raise_reason_program
Proof
  EVAL_TAC
QED

Theorem loops_supported_program:
  supported_program evalCompilerSubsetControlDeploy$loops_program
Proof
  EVAL_TAC
QED

Theorem function_modes_supported_program:
  supported_program evalCompilerSubsetControlDeploy$function_modes_program
Proof
  EVAL_TAC
QED
