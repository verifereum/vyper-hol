(* Memory case of the body induction: slice(self.code, start, length),
   admitted as S1's exprSimSliceSelfCode.compile_slice_self_code_case is:
   self.code is the account's installed code while the lowering reads the
   running code (CODESIZE/CODECOPY), and the state relations leave the two
   independent.  HELD until S1's residual closes. *)
Theory bodyMemBiSliceSelfCode
Ancestors
  bodyMemoryPreds exprLowering

Theorem body_builtin_slice_self_code_mem:
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
     code_slice_source (Slice n) es = NONE ==>
     body_exprs_mem_ok cx es) /\
    is_self_code (HD es) ==>
    body_expr_mem_ok cx (Builtin ty (Slice n) es)
Proof
  cheat
QED
