(* Turn the loop's robust memory and allocation coverage into the public
   pointer value/buffer posts.  Capacity is distinct from value footprint. *)
Theory bodyPtrMakeArrayPackage
Ancestors
  bodyPtrMakeArrayTupleLoop bodyPtrDefs exprSimProps valueEncoding
  venomState words ptrDiscipline

Theorem literal_memory_ptr_posts:
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  val_wf tv v /\ type_memory_size tv <= capacity /\
  type_memory_bytes ce (lowered_value_type ce e) <= capacity /\
  lookup_var root s = SOME (n2w addr) /\ addr < dimword(:256) /\
  FLOOKUP G root = SOME (addr,capacity) /\ op_taint tn (Var root) = {} /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v addr m) ==>
  ptr_val_ok cx ty v (Var root) G tn s /\ ptr_buf_ok ce e (Var root) G s
Proof
  strip_tac >>
  `w2n (n2w addr : bytes32) = addr` by simp[w2n_n2w] >>
  `val_store_size tv v <= capacity` by metis_tac[val_store_size_le, arithmeticTheory.LESS_EQ_TRANS] >>
  simp[ptr_val_ok_def, ptr_mem_ok_def, ptr_buf_ok_def, eval_operand_def] >>
  metis_tac[arithmeticTheory.LESS_EQ_REFL, arithmeticTheory.ADD_ASSOC]
QED
