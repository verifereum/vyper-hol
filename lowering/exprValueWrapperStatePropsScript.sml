(* Value-result wrappers preserve the compiler state in their input pair. *)
Theory exprValueWrapperStateProps
Ancestors
  exprLowering compileEnv pair

Theorem dalloca_windows_state_wrappers:
  SND (as_stack_val t (op_st:operand # compile_state)) = SND op_st /\
  SND (as_ptr_val t loc op_st) = SND op_st
Proof
  Cases_on `op_st` >> simp[as_stack_val_def, as_ptr_val_def]
QED
