(* TOP-LEVEL: exact membership of scalar operator fixtures. *)
Theory supportedFixturesScalarOperators
Ancestors supportedProgram evalCompilerSubsetScalars
Libs supportedEvalLib intLib

val () = supportedEvalLib.configure ();

Theorem scalar_bits_supported_program:
  supported_program evalCompilerSubsetScalars$scalar_bits_program
Proof
  EVAL_TAC
QED

Theorem scalar_compare_eq_supported_program:
  supported_program evalCompilerSubsetScalars$scalar_compare_eq_program
Proof
  EVAL_TAC
QED

Theorem scalar_compare_order_int_supported_program:
  supported_program evalCompilerSubsetScalars$scalar_compare_order_int_program
Proof
  EVAL_TAC
QED

Theorem scalar_compare_order_uint_supported_program:
  supported_program evalCompilerSubsetScalars$scalar_compare_order_uint_program
Proof
  EVAL_TAC
QED

Theorem scalar_minmax_int_supported_program:
  supported_program evalCompilerSubsetScalars$scalar_minmax_int_program
Proof
  EVAL_TAC
QED

Theorem scalar_minmax_uint_supported_program:
  supported_program evalCompilerSubsetScalars$scalar_minmax_uint_program
Proof
  EVAL_TAC
QED

Theorem scalar_modular_supported_program:
  supported_program evalCompilerSubsetScalars$scalar_modular_program
Proof
  EVAL_TAC
QED

Theorem scalar_shifts_supported_program:
  supported_program evalCompilerSubsetScalars$scalar_shifts_program
Proof
  EVAL_TAC
QED

Theorem scalar_unary_supported_program:
  supported_program evalCompilerSubsetScalars$scalar_unary_program
Proof
  EVAL_TAC
QED

Theorem scalar_wei_large_supported_program:
  supported_program evalCompilerSubsetScalars$scalar_wei_large_program
Proof
  EVAL_TAC
QED

Theorem scalar_wei_small_supported_program:
  supported_program evalCompilerSubsetScalars$scalar_wei_small_program
Proof
  EVAL_TAC
QED
