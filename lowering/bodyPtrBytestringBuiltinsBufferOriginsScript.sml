(* Representative allocation-wrapper origin boundary. *)
Theory bodyPtrBytestringBuiltinsBufferOrigins
Ancestors
  bodyPtrBytestringBuiltinsAllocationDeltas context compileEnv

Theorem compile_alloc_buffer_allocation_delta:
  compile_alloc_buffer bytes sa = (buf,sb) ==>
  sa.cs_next_var <= sb.cs_next_var /\
  ?delta. state_insts sb = state_insts sa ++ delta /\
          alloca_output_interval sa.cs_next_var sb.cs_next_var delta
Proof
  simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  drule emit_op_allocation_delta >> simp[]
QED
