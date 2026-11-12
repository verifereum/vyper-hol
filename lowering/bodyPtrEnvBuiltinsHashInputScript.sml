(* Robust operand representations expose the bytes read by hashing. *)
Theory bodyPtrEnvBuiltinsHashInput
Ancestors bodyPtrDefs representationCleanPtr vyperValue valueEncoding
  vyperAST vyperContext compileEnv words list exprSimProps loweringPosts finite_map

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

(* Coverage is separate from robustness: even the empty string has a
   length header, so its payload address retains an allocation site. *)
Theorem ptr_mem_ok_read_range:
  ptr_mem_ok cx ty v op G tn s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  eval_operand op s = SOME w /\
  val_footprint tv v <> 0 /\ off + len <= val_footprint tv v ==>
  ?x b sz. op = Var x /\ FLOOKUP G x = SOME (b,sz) /\
    b <= w2n w + off /\ w2n w + off + len <= b + sz
Proof
  strip_tac >>
  `?x b sz. op = Var x /\ FLOOKUP G x = SOME (b,sz) /\
    b <= w2n w /\ w2n w + val_store_size tv v <= b + sz` by
    metis_tac[ptr_mem_ok_def] >>
  qspecl_then [`tv`, `v`] assume_tac val_footprint_le_store_size >>
  qexistsl [`x`, `b`, `sz`] >> simp[] >> decide_tac
QED

Theorem ptr_val_ok_bytes_hash_range:
  ptr_val_ok cx (BaseT (BytesT (Dynamic n))) (BytesV bs) op G tn s /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic n))) =
    SOME (BaseTV (BytesT (Dynamic n))) /\
  eval_operand op s = SOME w ==>
  ?x b sz. op = Var x /\ FLOOKUP G x = SOME (b,sz) /\
    b <= w2n w + 32 /\ w2n w + 32 + LENGTH bs <= b + sz /\
    (!i. w2n w + 32 <= i /\ i < w2n w + 32 + LENGTH bs ==>
         i NOTIN tn.t_mem)
Proof
  strip_tac >> drule_all ptr_val_ok_bytes_read_clean >> strip_tac >>
  `ptr_mem_ok cx (BaseT (BytesT (Dynamic n))) (BytesV bs) op G tn s` by
    gvs[ptr_val_ok_def, is_word_type_def] >>
  drule ptr_mem_ok_read_range >>
  disch_then drule >> disch_then drule >>
  disch_then (qspecl_then [`32`, `LENGTH bs`] mp_tac) >>
  simp[val_footprint_def] >> metis_tac[]
QED

Theorem ptr_val_ok_string_hash_range:
  ptr_val_ok cx (BaseT (StringT n)) (StringV str) op G tn s /\
  evaluate_type (get_tenv cx) (BaseT (StringT n)) =
    SOME (BaseTV (StringT n)) /\
  eval_operand op s = SOME w ==>
  ?x b sz. op = Var x /\ FLOOKUP G x = SOME (b,sz) /\
    b <= w2n w + 32 /\ w2n w + 32 + LENGTH str <= b + sz /\
    (!i. w2n w + 32 <= i /\ i < w2n w + 32 + LENGTH str ==>
         i NOTIN tn.t_mem)
Proof
  strip_tac >> drule_all ptr_val_ok_string_read_clean >> strip_tac >>
  `ptr_mem_ok cx (BaseT (StringT n)) (StringV str) op G tn s` by
    gvs[ptr_val_ok_def, is_word_type_def] >>
  drule ptr_mem_ok_read_range >>
  disch_then drule >> disch_then drule >>
  disch_then (qspecl_then [`32`, `LENGTH str`] mp_tac) >>
  simp[val_footprint_def] >> metis_tac[]
QED
