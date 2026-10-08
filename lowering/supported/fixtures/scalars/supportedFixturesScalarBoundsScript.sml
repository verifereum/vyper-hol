(* TOP-LEVEL: exact membership of scalar bounds and empty fixtures. *)
Theory supportedFixturesScalarBounds
Ancestors supportedProgram evalCompilerSubsetScalars
Libs supportedEvalLib intLib

val () = supportedEvalLib.configure ();

Theorem scalar_decimal_bounds_supported_program:
  supported_program evalCompilerSubsetScalars$scalar_decimal_bounds_program
Proof
  EVAL_TAC
QED

Theorem scalar_decimal_max_supported_program:
  supported_program evalCompilerSubsetScalars$scalar_decimal_max_program
Proof
  EVAL_TAC
QED

Theorem scalar_decimal_min_supported_program:
  supported_program evalCompilerSubsetScalars$scalar_decimal_min_program
Proof
  EVAL_TAC
QED

Theorem scalar_empty_supported_program:
  supported_program evalCompilerSubsetScalars$scalar_empty_program
Proof
  EVAL_TAC
QED

Theorem scalar_integer_bounds_supported_program:
  supported_program evalCompilerSubsetScalars$scalar_integer_bounds_program
Proof
  EVAL_TAC
QED

Theorem scalar_integer_min_uint8_supported_program:
  supported_program evalCompilerSubsetScalars$scalar_integer_min_uint8_program
Proof
  EVAL_TAC
QED

Theorem scalar_integer_max_int256_supported_program:
  supported_program evalCompilerSubsetScalars$scalar_integer_max_int256_program
Proof
  EVAL_TAC
QED

Theorem scalar_integer_min_int256_supported_program:
  supported_program evalCompilerSubsetScalars$scalar_integer_min_int256_program
Proof
  EVAL_TAC
QED
