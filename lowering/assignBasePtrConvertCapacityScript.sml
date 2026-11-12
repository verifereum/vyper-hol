(* Capacity-growth dispatch, prior to any semantic allocation argument.
   compile_convert_bytestring_shape already exports the outer compile_expr
   shape; this boundary selects the inner branch for any child compiler. *)
Theory assignBasePtrConvertCapacity
Ancestors exprLowering context compileEnv vyperAST

Theorem assign_base_convert_growth_dispatch:
  !f cenv vv_ty ty ret_ty e1 st v st1.
    is_bytestring_type (expr_type e1) /\ is_bytestring_type ret_ty /\
    ~is_word_type ret_ty /\
    type_memory_bytes cenv (lowered_value_type cenv e1) < type_memory_bytes cenv ret_ty /\
    lower_value f cenv (expr_type e1) e1 st = (v,st1) ==>
    compile_type_builtin_dispatch_body f cenv vv_ty ty Convert ret_ty [e1] st =
      as_stack_val vv_ty (compile_bytestring_widen_copy
        (type_memory_bytes cenv ret_ty) v
        (type_memory_bytes cenv (lowered_value_type cenv e1)) st1)
Proof
  rpt strip_tac >> simp[compile_type_builtin_dispatch_body_def]
QED

Theorem assign_base_convert_bytes_32_64_dispatch:
  !f cenv vv_ty ty name st v st1.
    lower_value f cenv (BaseT (BytesT (Dynamic 32)))
      (Name (BaseT (BytesT (Dynamic 32))) name) st = (v,st1) ==>
    compile_type_builtin_dispatch_body f cenv vv_ty ty Convert
      (BaseT (BytesT (Dynamic 64)))
      [Name (BaseT (BytesT (Dynamic 32))) name] st =
      as_stack_val vv_ty (compile_bytestring_widen_copy 96 v 64 st1)
Proof
  rpt strip_tac >>
  simp[compile_type_builtin_dispatch_body_def, expr_type_def,
    lowered_value_type_def, is_bytestring_type_def, is_word_type_def,
    type_memory_bytes_def]
QED
