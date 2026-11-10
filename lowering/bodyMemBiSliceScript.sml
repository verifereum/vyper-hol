(* Memory case of the body induction, one family of bodyMemBuiltinRest's
   builtins: slice. HELD: its S1 case (exprSimBuiltins' compile_slice_case,
   exprSimSlice on s1-builtins-aggregates) is still admitted. *)
Theory bodyMemBiSlice
Ancestors
  bodyMemoryPreds

Theorem body_builtin_slice_mem:
  !cx ty n es.
    (!code_ty addr s3 tail_vs t'.
       builtin_args_length_ok (Slice n) (LENGTH es) /\
       code_slice_source (Slice n) es = SOME (code_ty,addr) /\
       eval_exprs cx (TL es) s3 = (INL tail_vs,t') ==>
       body_exprs_mem_ok cx [addr]) /\
    (!code_ty addr.
       builtin_args_length_ok (Slice n) (LENGTH es) /\
       code_slice_source (Slice n) es = SOME (code_ty,addr) ==>
       body_exprs_mem_ok cx (TL es)) /\
    (builtin_args_length_ok (Slice n) (LENGTH es) /\
     code_slice_source (Slice n) es = NONE ==> body_exprs_mem_ok cx es) ==>
    body_expr_mem_ok cx (Builtin ty (Slice n) es)
Proof
  cheat
QED
