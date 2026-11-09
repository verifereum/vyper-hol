(* Memory case of the body induction: a slice of anything but self.code
   (bodyMemBiSlice's split).  A slice of x.code evaluates start and len
   before the address x (code_slice_source), so its premises are the
   induction's code-slice ones: the tail's judgment, and the address's after
   the tail evaluates; any other slice takes its operands' judgment. *)
Theory bodyMemBiSliceNonSelf
Ancestors
  bodyMemoryPreds exprLowering bodyMemSliceScratch bodyMemSliceTerminal

Theorem body_builtin_slice_nonself_mem:
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
    ~is_self_code (HD es) ==>
    body_expr_mem_ok cx (Builtin ty (Slice n) es)
Proof
  cheat
QED
