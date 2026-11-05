Theory bodyPtrIntCallStageBoundary
Ancestors bodyPtrDefs bodyPtrIntCallConfinement exprLowering compileEnv
  ptrDiscipline finite_map pred_set list

Theorem intcall_stage_stack_singleton:
  compile_stage_intcall_args cenv [StackValue ty op] [T] [aty] sa =
  ([op],sa)
Proof
  simp[compile_stage_intcall_args_def, unwrap_value_def,
       comp_bind_def, comp_return_def]
QED

Theorem intcall_ptr_val_word:
  is_word_type ty ==>
  (ptr_val_ok cx ty v op G tn s <=>
   op_taint tn op = {} /\ op_prov G op = NONE)
Proof
  simp[ptr_val_ok_def]
QED

