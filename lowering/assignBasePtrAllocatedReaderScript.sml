(* Numerical read-start bounds follow the actual allocation and a frame of
   its returned operand; no arbitrary execution endpoints are identified. *)
Theory assignBasePtrAllocatedReader
Ancestors
  exprSimAlloc exprLoweringProps context venomInst venomState
  words arithmetic list

Theorem assign_base_ptr_allocated_reader_bound:
  !ctx fn cenv cx es sz sa buf sb s u t a n.
    compile_alloc_buffer sz sa = (buf,sb) /\
    stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
    local_ptrs_reserved cenv sa /\ sz < dimword (:256) /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn) /\
    run_inst_seq (emitted_insts sa sb) s = OK u /\
    eval_operand buf.buf_operand t = eval_operand buf.buf_operand u /\
    eval_operand buf.buf_operand t = SOME a /\ 32*n <= sz ==>
    w2n a + 32*(n-1) < dimword (:256)
Proof
  rpt strip_tac >> drule_all literal_alloc_buffer_run >> strip_tac >>
  gvs[] >> Cases_on `n = 0` >> gvs[] >> decide_tac
QED
