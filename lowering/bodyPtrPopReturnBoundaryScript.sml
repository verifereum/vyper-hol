Theory bodyPtrPopReturnBoundary
Ancestors
  exprLowering compileEnv stmtSimForParts

(* lower_value_int_lit already supplies the scalar computational boundary;
   reuse it rather than duplicating that theorem. *)
Theorem pop_literal_stack_no_emit:
  compile_literal_vv ty l sa = (StackValue t (Lit w),sb) ==> sb = sa
Proof
  Cases_on `l` >> simp[compile_literal_vv_def, comp_return_def]
  >- (Cases_on `b` >> simp[compile_literal_vv_def, comp_return_def])
  >- (Cases_on `ty` >> simp[comp_bind_def, comp_return_def] >>
      pairarg_tac >> simp[]) >>
  Cases_on `ty` >> simp[comp_return_def] >>
  Cases_on `b` >> simp[comp_return_def] >>
  Cases_on `b'` >> simp[comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[]
QED
