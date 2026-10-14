(* TOP-LEVEL: exact membership of scalar width and literal fixtures. *)
Theory supportedFixturesScalarWidthsLiterals
Ancestors supportedProgram evalCompilerSubsetScalars
Libs supportedEvalLib intLib

val () = supportedEvalLib.configure ();

Theorem scalar_widths_int_high_supported_program:
  supported_program evalCompilerSubsetScalars$scalar_widths_int_high_program
Proof
  EVAL_TAC
QED

Theorem scalar_widths_int_low_supported_program:
  supported_program evalCompilerSubsetScalars$scalar_widths_int_low_program
Proof
  EVAL_TAC
QED

Theorem scalar_widths_uint_high_supported_program:
  supported_program evalCompilerSubsetScalars$scalar_widths_uint_high_program
Proof
  EVAL_TAC
QED

Theorem scalar_widths_uint_low_supported_program:
  supported_program evalCompilerSubsetScalars$scalar_widths_uint_low_program
Proof
  EVAL_TAC
QED

Theorem scalar_literal_decimal_supported_program:
  supported_program evalCompilerSubsetScalars$scalar_literal_decimal_program
Proof
  EVAL_TAC
QED

Theorem scalar_literals_bool_supported_program:
  supported_program evalCompilerSubsetScalars$scalar_literals_bool_program
Proof
  EVAL_TAC
QED

Theorem scalar_literals_bytes_supported_program:
  supported_program evalCompilerSubsetScalars$scalar_literals_bytes_program
Proof
  EVAL_TAC
QED

Theorem scalar_literals_int_small_supported_program:
  supported_program evalCompilerSubsetScalars$scalar_literals_int_small_program
Proof
  EVAL_TAC
QED

Theorem scalar_literals_int_wide_supported_program:
  supported_program evalCompilerSubsetScalars$scalar_literals_int_wide_program
Proof
  EVAL_TAC
QED
