(* TOP-LEVEL: exact membership of scalar arithmetic fixtures. *)
Theory supportedFixturesScalarArithmetic
Ancestors supportedProgram evalCompilerSubsetScalars
Libs supportedEvalLib intLib

val () = supportedEvalLib.configure ();

Theorem scalar_arith_decimal_supported_program:
  supported_program evalCompilerSubsetScalars$scalar_arith_decimal_program
Proof
  EVAL_TAC
QED

Theorem scalar_arith_decimal_div_supported_program:
  supported_program evalCompilerSubsetScalars$scalar_arith_decimal_div_program
Proof
  EVAL_TAC
QED

Theorem scalar_arith_decimal_mul_supported_program:
  supported_program evalCompilerSubsetScalars$scalar_arith_decimal_mul_program
Proof
  EVAL_TAC
QED

Theorem scalar_arith_decimal_sub_supported_program:
  supported_program evalCompilerSubsetScalars$scalar_arith_decimal_sub_program
Proof
  EVAL_TAC
QED

Theorem scalar_arith_int_supported_program:
  supported_program evalCompilerSubsetScalars$scalar_arith_int_program
Proof
  EVAL_TAC
QED

Theorem scalar_arith_pow_supported_program:
  supported_program evalCompilerSubsetScalars$scalar_arith_pow_program
Proof
  EVAL_TAC
QED

Theorem scalar_arith_pow_base_supported_program:
  supported_program evalCompilerSubsetScalars$scalar_arith_pow_base_program
Proof
  EVAL_TAC
QED

Theorem scalar_arith_uint_supported_program:
  supported_program evalCompilerSubsetScalars$scalar_arith_uint_program
Proof
  EVAL_TAC
QED

Theorem scalar_arith_unsafe_int_supported_program:
  supported_program evalCompilerSubsetScalars$scalar_arith_unsafe_int_program
Proof
  EVAL_TAC
QED

Theorem scalar_arith_unsafe_uint_supported_program:
  supported_program evalCompilerSubsetScalars$scalar_arith_unsafe_uint_program
Proof
  EVAL_TAC
QED
