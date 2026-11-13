(* Opcode-independent freshness at the post-ADD child boundary. *)
Theory bodyPtrStructLitUnwrapFrame
Ancestors exprLoweringProps emitHelperProps freshWrites context compileEnv loweringStateRelDefs

Theorem raw_child_unwrap_compiler_frame:
  compile_expr ce (expr_type e) e sb = (vv,sc) /\
  emit_op ADD [left; Lit off] sc = (dst,sm) /\
  local_ptrs_reserved ce sb /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x) /\
  ~not_fresh_at sm out ==>
  sb.cs_next_var <= sm.cs_next_var /\
  ~not_fresh_at sb out /\
  (!x. not_fresh_at sb x ==> x <> out) /\
  (!scopes. not_local_ptr ce scopes out) /\
  (!name x sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var x) sz) ==> x <> out) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> x <> out) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> x <> out)
Proof
  strip_tac >> drule (cj 1 compile_expr_grows) >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  gvs[not_fresh_at_def, local_ptrs_reserved_def, not_local_ptr_def] >>
  rpt conj_tac >> rpt strip_tac >> res_tac >> gvs[] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_ADD]
QED
