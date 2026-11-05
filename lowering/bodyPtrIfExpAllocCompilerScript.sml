Theory bodyPtrIfExpAllocCompiler
Ancestors
  bodyPtrIfExpAllocStep bodyPtrIfExpAllocGhost bodyPtrIfExpAllocKept
  compileEnv loweringHalt stmtFragPtr

(* These are exactly the reserved-variable premises of expr_vv_sim_ptr,
   transported from its starting cutoff to the allocation after the arm. *)
Theorem compile_alloc_buffer_frame_separation:
  !cenv sa sb n buf sc scopes out.
    local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sb.cs_next_var /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
            not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
            not_fresh_at sa x) /\
    compile_alloc_buffer n sb = (buf,sc) /\ buf.buf_operand = Var out ==>
    not_local_ptr cenv scopes out /\
    (!x. not_fresh_at sa x ==> x <> out) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> x <> out) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> x <> out)
Proof
  rpt strip_tac >> drule compile_alloc_buffer_parts >> strip_tac >>
  gvs[not_local_ptr_def, local_ptrs_reserved_def] >>
  metis_tac[not_fresh_at_mono]
QED
