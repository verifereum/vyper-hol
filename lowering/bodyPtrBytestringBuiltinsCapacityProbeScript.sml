Theory bodyPtrBytestringBuiltinsCapacityProbe
Ancestors
  bodyPtrDefs builtinStrings

(* Full-buffer coverage cannot start strictly inside an equally sized site. *)
Theorem ptr_buf_ok_interior_site_failure:
  eval_operand (Var x) s = SOME w /\
  FLOOKUP G x = SOME (b, sz) /\
  w2n w = b + k /\ 0 < k /\
  type_memory_bytes cenv (lowered_value_type cenv e) = sz /\
  0 < sz ==>
  ~ptr_buf_ok cenv e (Var x) G s
Proof
  rw[ptr_buf_ok_def] >> qexists_tac `w` >> simp[]
QED

Theorem uint2str_78_buffer_capacity:
  type_memory_bytes cenv
    (lowered_value_type cenv
      (Builtin (BaseT (StringT 78)) (Uint2Str 78) args)) = 128
Proof
  simp[exprLoweringTheory.lowered_value_type_def,
       vyperASTTheory.expr_type_def, compileEnvTheory.type_memory_bytes_def]
QED

Theorem uint2str_78_interior_site_failure:
  eval_operand (Var x) s = SOME w /\
  FLOOKUP G x = SOME (b, 128) /\ w2n w = b + 77 ==>
  ~ptr_buf_ok cenv
    (Builtin (BaseT (StringT 78)) (Uint2Str 78) args) (Var x) G s
Proof
  strip_tac >> irule ptr_buf_ok_interior_site_failure >>
  qexistsl_tac [`b`, `77`, `128`, `w`] >>
  simp[uint2str_78_buffer_capacity]
QED
