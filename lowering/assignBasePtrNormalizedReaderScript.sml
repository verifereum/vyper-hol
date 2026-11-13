(* The reader uses the allocated normalization root at the chosen endpoint.
   A typed-copy frame preserves its value without endpoint synchronization. *)
Theory assignBasePtrNormalizedReader
Ancestors
  assignBasePtrAllocatedReader exprSimAlloc typedMemoryCopy
  exprLoweringProps context venomInst venomState words arithmetic list

Theorem assign_base_ptr_normalized_reader_bound:
  !ctx fn cenv cx es sz sa buf sb s u t a n dst len.
    compile_alloc_buffer sz sa = (buf,sb) /\
    stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
    local_ptrs_reserved cenv sa /\ sz < dimword (:256) /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn) /\
    run_inst_seq (emitted_insts sa sb) s = OK u /\
    typed_copy_state_frame sb dst len u t /\
    eval_operand buf.buf_operand t = SOME a /\ 32*n <= sz ==>
    w2n a + 32*(n-1) < dimword (:256)
Proof
  rpt strip_tac >> drule_all literal_alloc_buffer_run >> strip_tac >>
  `!x. buf.buf_operand = Var x ==> not_fresh_at sb x` by simp[] >>
  drule_all typed_copy_state_frame_operand >> strip_tac >>
  drule_all assign_base_ptr_allocated_reader_bound >> simp[]
QED
