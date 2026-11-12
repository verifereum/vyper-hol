(* Full local byte frames on the typed store's own constructed endpoint. *)
Theory bodyIntCallStoreFrame
Ancestors
  valueCopy bodyIntCallWriteFrame

Theorem compile_store_memory_run_local_frame_with_capacity:
  !cenv src dst ty sa sb s tenv tv v sw dw bound func scopes inst q b asz.
    compile_store_memory cenv src dst ty ty sa = ((),sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
    evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
    type_memory_bytes cenv ty = type_memory_size tv /\
    (if is_word_type ty then sw = typed_val_to_w256 tv v
     else val_in_memory tv v (w2n sw) s.vs_memory) /\
    type_memory_size tv + 64 < dimword (:256) /\
    (if is_bytestring_type ty then val_store_size tv v <= bound
     else type_memory_size tv <= bound) /\
    alloca_inv s /\ fn_inst_ids_distinct func /\
    local_ptrs_rel func cenv scopes s /\
    MEM inst (fn_insts func) /\ inst.inst_outputs = [q] /\
    not_local_ptr cenv scopes q /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,asz) /\
    b <= w2n dw /\ w2n dw + bound <= b + asz ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      val_in_memory tv v (w2n dw) t.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. a + len <= w2n dw \/ w2n dw + bound <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory /\
      (!n lo sz. local_region cenv scopes s n lo sz ==>
         mem_bytes_at lo sz t.vs_memory = mem_bytes_at lo sz s.vs_memory)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_store_memory_run_frame_with_capacity >> strip_tac >>
  asm_rewrite_tac[] >> qexists_tac `t` >> asm_rewrite_tac[] >>
  rpt gen_tac >> strip_tac >>
  drule_all allocated_write_local_bytes >> simp[]
QED
