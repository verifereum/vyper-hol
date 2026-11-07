(* Separation of saved local allocations from later fresh outputs.
   This is a local compiler seam interface, not a supported-code exclusion. *)
Theory bodyPtrBytestringBuiltinsCompilerSeams
Ancestors
  exprSafeOperand emitHelper compileEnv arithmetic

Theorem emit_op_ne_safe_operand:
  safe_operand st saved /\ emit_op opc args st = (op,st') ==>
  op <> saved
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[safe_operand_def, not_fresh_at_def] >>
  metis_tac[LESS_EQ_REFL]
QED

Theorem emit_op_ne_saved_allocation:
  compile_alloc_buffer bytes sa = (buf,sb) /\
  sb.cs_next_var <= sc.cs_next_var /\
  emit_op opc args sc = (op,sd) ==>
  op <> buf.buf_operand
Proof
  rpt strip_tac >>
  drule alloc_buffer_safe_operand >> strip_tac >>
  `safe_operand sc buf.buf_operand` by metis_tac[safe_operand_mono] >>
  metis_tac[emit_op_ne_safe_operand]
QED
