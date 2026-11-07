(* Captured parameter ages at actual compiler declaration boundaries. *)
Theory bodyPtrBytestringBuiltinsParameterAges
Ancestors
  moduleLowering intCallCallee exprSafeOperand emitHelper compileEnv list

Theorem internal_param_decls_safe_operands:
  !ps idx sa caps next sb.
  compile_internal_param_decls ps idx sa = ((caps,next),sb) ==>
  EVERY (\(name,is_stack,op). safe_operand sb op) caps
Proof
  Induct_on `ps`
  >- simp[compile_internal_param_decls_def, comp_return_def] >>
  gen_tac >> PairCases_on `h` >>
  simp[compile_internal_param_decls_def, comp_bind_def, comp_return_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  PairCases_on `rest_result` >> gvs[] >>
  drule internal_param_decls_projection >> strip_tac >>
  drule emit_op_safe_operand >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  simp[] >> metis_tac[safe_operand_mono]
QED
