(* TOP-LEVEL: exact PLAN 5.6 membership for the state manifest fixtures.
   Includes the corrected storage_scalar_loop AST, unchanged here. *)
Theory supportedFixturesState
Ancestors supportedProgram evalCompilerSubsetState
Libs intLib

Theorem storage_scalar_loop_supported_program:
  supported_program evalCompilerSubsetState$storage_scalar_loop_program
Proof
  EVAL_TAC
QED

Theorem storage_array_supported_program:
  supported_program evalCompilerSubsetState$storage_array_program
Proof
  EVAL_TAC
QED

Theorem storage_dynarray_supported_program:
  supported_program evalCompilerSubsetState$storage_dynarray_program
Proof
  EVAL_TAC
QED

Theorem storage_mapping_supported_program:
  supported_program evalCompilerSubsetState$storage_mapping_program
Proof
  EVAL_TAC
QED

Theorem storage_struct_supported_program:
  supported_program evalCompilerSubsetState$storage_struct_program
Proof
  EVAL_TAC
QED

Theorem transient_scalar_supported_program:
  supported_program evalCompilerSubsetState$transient_scalar_program
Proof
  EVAL_TAC
QED
