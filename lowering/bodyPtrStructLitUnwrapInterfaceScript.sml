(* Premise production for the actual raw child endpoint; no unwrap execution. *)
Theory bodyPtrStructLitUnwrapInterface
Ancestors bodyPtrStructLitMemoryCaller bodyPtrStructLitMemoryRead
  exprSimSource bodyPtrDefs
  exprSimDefs context venomState

Theorem raw_child_memory_word_resources:
  expr_body_pre ce cx env e es /\ eval_expr cx e es = (INL tv,ee) /\
  vv_post ctx fn ce cx e es sb sm t ee tv (LocatedValue ty q) s /\
  ptr_vv_ok cx (expr_type e) tv (LocatedValue ty q) ee G tn s /\
  q.ptr_location = LocMemory /\ is_word_type ty ==>
  ?a src. eval_operand q.ptr_operand s = SOME a /\
    q.ptr_operand = Var src /\ ptr_covers G tn src s 32 /\
    (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem)
Proof
  strip_tac >> drule_all vv_post_memory_word_read >> strip_tac >>
  drule_all expr_body_pre_runtime_typed >> strip_tac >>
  `ptr_mem_ok cx ty v q.ptr_operand G tn s /\
   op_taint tn q.ptr_operand = {} /\ value_has_type tvt v` by
    (gvs[ptr_vv_ok_def] >> metis_tac[]) >>
  gvs[] >> drule_all ptr_mem_ok_word_read >> strip_tac >> metis_tac[]
QED

(* Premise ledger for memory_word_unwrap_continuation at post-ADD entry:
   - vv_post, ghost_inv, ptr_vv_ok, ghost_kept, nonhalting and cursor:
     raw_child_emitted_add_continuation (source compiler endpoint is sm).
   - ty = expr_type e and operand evaluation: vv_post_memory_word_read.
   - Var shape, 32-byte coverage and clean bytes: the theorem above, using
     expr_body_pre_runtime_typed and MemoryCaller.ptr_mem_ok_word_read.
     Neither ptr_buf_ok nor the source's single-memory representation alone
     supplies cleanliness. The source pre/eval pair is essential to this proof.
   - Source evaluation premise: gas_outcome_ptr's normal branch is universally
     tied to the gas-observation-adjusted source run. Integration must instantiate
     the pre/runtime-typing fact at that same source run, not silently identify
     its gas_obs field with es.gas_obs. This file does not perform that bind.
   - G1/tn1/s1: definitional witnesses of the actual MLOAD; MemoryUnwrap now
     requires the G1 equality explicitly and mload_output_provenance supplies
     the word's NONE provenance, independently of clean-byte reasoning.
   - unwrap compiler equality: following bind in compile_struct_lit_def.
     fn_has_code sm <unwrap end> is NOT exported by first_add_code: its strict
     suffix split must be proved for the unwrap compiler endpoint separately.
   - sb.cs_next_var <= sm.cs_next_var: compile_expr_grows then emit_op growth.
     Fresh MLOAD output: memory_word_unwrap_code. Reserved local/return and
     ghost_kept inequalities follow by transporting the entry reservations
     through child/ADD growth, then using this fresh output. The combined
     compiler frame for these facts is not yet exported by this leaf.

   Other unwrap branches (audit only; no full unwrap/store composition):
   - StackValue: unwrap_value_def returns the operand without an edge; raw
     ptr_vv_ok already contains read_result success and ptr_val_ok. The source
     post still needs expr_post_of_vv_post and read-result gas bookkeeping.
   - LocatedValue non-word LocMemory: unwrap returns the pointer, no edge;
     ptr_vv_ok provides its taint/robust representation. Raw ptr_buf_ok is
     retained by ADD, but destination declared-field capacity remains separate.
   - Storage/transient word: storage_word_unwrap_continuation derives key-taint
     emptiness using ptr_vv_ok's live-byte clauses and word_type_slot_size;
     source endpoint typing and the same compiler freshness/code frame remain.
   - LocCode word: runtime_code_word_unwrap_continuation applies only outside
     constructors; its caller derives opcode execution/source read from vv_post.
   - Non-word nonmemory places: unwrap_value_def calls compile_ensure_in_memory,
     allocating/copying an entire buffer. Neither word continuation covers that
     path; no claim of completeness or field-sized capacity is made here.
   expr_sim_ptr_of_vv is locally admitted in this checkout, so it supplies no
   inspectable proof of these raw-endpoint branch premises. Its theorem is an
   ancestor interface, not a characterization of the supplied raw endpoint.
*)
