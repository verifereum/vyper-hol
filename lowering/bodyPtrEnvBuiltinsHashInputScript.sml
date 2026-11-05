(* Robust operand representations expose the bytes read by hashing. *)
Theory bodyPtrEnvBuiltinsHashInput
Ancestors bodyPtrDefs representationCleanPtr vyperValue valueEncoding
  vyperAST vyperContext compileEnv words list

Theorem ptr_val_ok_bytes_read_clean:
  ptr_val_ok cx (BaseT (BytesT (Dynamic n))) (BytesV bs) op G tn s /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic n))) =
    SOME (BaseTV (BytesT (Dynamic n))) /\
  eval_operand op s = SOME w ==>
  (!i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem) /\
  (!i. w2n w + 32 <= i /\ i < w2n w + 32 + LENGTH bs ==> i NOTIN tn.t_mem)
Proof
  strip_tac >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) (w2n w) mem` by
    (gvs[ptr_val_ok_def, ptr_mem_ok_def, is_word_type_def] >> metis_tac[]) >>
  drule robust_val_in_memory_bytes_clean >> simp[]
QED

Theorem ptr_val_ok_string_read_clean:
  ptr_val_ok cx (BaseT (StringT n)) (StringV str) op G tn s /\
  evaluate_type (get_tenv cx) (BaseT (StringT n)) =
    SOME (BaseTV (StringT n)) /\
  eval_operand op s = SOME w ==>
  (!i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem) /\
  (!i. w2n w + 32 <= i /\ i < w2n w + 32 + LENGTH str ==> i NOTIN tn.t_mem)
Proof
  strip_tac >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (BaseTV (StringT n)) (StringV str) (w2n w) mem` by
    (gvs[ptr_val_ok_def, ptr_mem_ok_def, is_word_type_def] >> metis_tac[]) >>
  drule robust_val_in_memory_string_clean >> simp[]
QED
