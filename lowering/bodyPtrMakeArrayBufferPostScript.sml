(* Convert a robust copied buffer to the public pointer postconditions.
   Keep source representation size and the required lowered capacity separate. *)
Theory bodyPtrMakeArrayBufferPost
Ancestors
  bodyPtrDefs exprSimProps valueEncodingProofs context compileEnv
  ptrDiscipline venomState finite_map words arithmetic

Theorem literal_buffer_pointer_post:
  ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  lookup_var dst s = SOME w /\
  val_wf tv v /\ type_memory_size tv <= sz /\
  ptr_covers G tn dst s sz /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v (w2n w) m) /\
  type_memory_bytes cenv (lowered_value_type cenv e) <= sz ==>
  ptr_val_ok cx ty v (Var dst) G tn s /\ ptr_buf_ok cenv e (Var dst) G s
Proof
  strip_tac >>
  `val_store_size tv v <= type_memory_size tv` by metis_tac[val_store_size_le] >>
  gvs[ptr_covers_def, ptr_val_ok_def, ptr_mem_ok_def, ptr_buf_ok_def,
      eval_operand_def]
QED
