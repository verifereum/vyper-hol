(* Assignment-order barriers are removed without broadening expression forms. *)
Theory evalAssignmentOrderSupported
Ancestors
  evalAssignmentOrderFrontend supportedProgram supportedStmts

Theorem assignment_order_source_programs_supported:
  supported_program c08_storage_arr_assign_computed_rhs_source_program /\
  supported_program c09_storage_map_assign_computed_rhs_source_program /\
  supported_program g6_write_order_side_source_program /\
  supported_program x04_assign_sideeffect_order_source_program /\
  supported_program g19_aug_rhs_modifies_target_source_program /\
  supported_program s11_storage_map_assign_extcall_rhs_source_program
Proof
  EVAL_TAC
QED

Theorem flat_tuple_assignment_supported:
  supported_stmt []
    [("x",BaseT (UintT 256)); ("y",BaseT (UintT 256));
     ("pair",TupleT [BaseT (UintT 256); BaseT (UintT 256)])]
    (Assign (TupleTarget [BaseTarget (NameTarget "x"); BaseTarget (NameTarget "y")])
      (Name (TupleT [BaseT (UintT 256); BaseT (UintT 256)]) "pair"))
Proof
  EVAL_TAC
QED

Theorem nested_tuple_lowering_remains_excluded:
  ~supported_stmt tops bindings
    (Assign (TupleTarget [TupleTarget targets]) rhs)
Proof
  simp[supported_stmt_def, supported_assignment_def]
QED

Theorem nested_pop_compiler_form_remains_excluded:
  ~supported_program assign_nested_popped_read_source_program
Proof
  EVAL_TAC
QED
