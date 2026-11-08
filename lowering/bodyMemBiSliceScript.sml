(* Memory case of the body induction: slice (bodyMemory's
   body_builtin_mem_ok splits it off), with the induction's code-slice
   premises.  A slice of self.code is bodyMemBiSliceSelfCode's (held with
   S1's residual); every other slice is bodyMemBiSliceNonSelf's. *)
Theory bodyMemBiSlice
Ancestors
  bodyMemoryPreds bodyMemBiSliceSelfCode bodyMemBiSliceNonSelf

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
     code_slice_source (Slice n) es = NONE ==>
     body_exprs_mem_ok cx es) ==>
    body_expr_mem_ok cx (Builtin ty (Slice n) es)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `is_self_code (HD es)`
  >- (irule body_builtin_slice_self_code_mem >> rpt conj_tac >>
      first_assum ACCEPT_TAC) >>
  irule body_builtin_slice_nonself_mem >> rpt conj_tac >>
  first_assum ACCEPT_TAC
QED
