(* Robust source inputs for the joint buffered internal Return suffix. *)
Theory internalReturnMemoryInputs
Ancestors
  assignBasePtrBoundary bodyDeclCopyMemory exprSimMemDefs loweringPosts
  bodyPtrDefs ptrDiscipline venomExecSemantics venomState

(* Capacity coverage and the actual source-read bound are distinct facts.
   Neither asserts that the entire source capacity is below the frontier. *)
Theorem internal_return_memory_value_inputs:
  !H ctx func cenv cx e es sa sm s0 ee v op t G tn ty tv.
    expr_post H ctx func cenv cx e es sa sm s0 ee v op t /\
    ptr_val_ok cx (post_value_type cenv e) v op G tn t /\
    ptr_buf_ok cenv e op G t /\
    expr_store_bound cx (post_value_type cenv e) v op t /\
    lowered_value_type cenv e = expr_type e /\ expr_type e = ty /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
    0 < type_memory_size tv /\
    type_memory_bytes cenv ty = type_memory_size tv ==>
    ?src a.
      op = Var src /\ lookup_var src t = SOME a /\
      ptr_covers G tn src t (type_memory_size tv) /\
      (!m. mem_agree_outside tn.t_mem t.vs_memory m ==>
           val_in_memory tv v (w2n a) m) /\
      w2n a + val_store_size tv v <= t.vs_alloca_next
Proof
  rpt strip_tac >>
  `post_value_type cenv e = ty` by metis_tac[post_value_type_lowered] >>
  `?a. eval_operand op t = SOME a` by
    fs[expr_post_def, expr_val_rel_def] >>
  `op_taint tn op = {} /\ ptr_mem_ok cx ty v op G tn t` by
    fs[ptr_val_ok_def] >>
  `?src. op = Var src /\ ptr_covers G tn src t (type_memory_size tv)` by
    (irule assignBasePtrBoundaryTheory.ptr_buf_ok_read_covers >>
     simp[] >> qexistsl [`cenv`, `e`] >> simp[]) >>
  `0 < val_store_size tv v` by metis_tac[val_store_size_pos] >>
  qexistsl [`src`, `a`] >>
  gvs[eval_operand_def, ptr_mem_ok_def, expr_store_bound_def]
QED
