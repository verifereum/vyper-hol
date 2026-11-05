Theory bodyPtrBopHashFootprint
Ancestors
  bodyPtrDefs representationCleanPtr

Theorem ptr_mem_ok_robust:
  ptr_mem_ok cx t v op G tn s /\
  evaluate_type (get_tenv cx) t = SOME tv /\
  eval_operand op s = SOME w ==>
  !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
        val_in_memory tv v (w2n w) mem
Proof
  rw[bodyPtrDefsTheory.ptr_mem_ok_def] >> metis_tac[]
QED

Theorem ptr_mem_ok_bounds:
  ptr_mem_ok cx t v op G tn s /\
  evaluate_type (get_tenv cx) t = SOME tv /\
  eval_operand op s = SOME w /\ val_footprint tv v <> 0 ==>
  ?x b sz. op = Var x /\ FLOOKUP G x = SOME (b,sz) /\
    b <= w2n w /\ w2n w + val_store_size tv v <= b+sz
Proof
  rw[bodyPtrDefsTheory.ptr_mem_ok_def] >> metis_tac[]
QED

Theorem ptr_mem_ok_representation:
  ptr_mem_ok cx t v op G tn s /\
  evaluate_type (get_tenv cx) t = SOME tv /\
  eval_operand op s = SOME w ==>
  val_in_memory tv v (w2n w) s.vs_memory
Proof
  strip_tac >>
  `mem_agree_outside tn.t_mem s.vs_memory s.vs_memory` by
    simp[bodyPtrDefsTheory.mem_agree_outside_def] >>
  metis_tac[ptr_mem_ok_robust]
QED

Theorem ptr_mem_ok_bytes_length:
  ptr_mem_ok cx t (BytesV bs) op G tn s /\
  evaluate_type (get_tenv cx) t = SOME tv /\
  eval_operand op s = SOME w /\ tv <> BaseTV AddressT /\
  (!k. tv <> BaseTV (BytesT (Fixed k))) ==>
  mem_word_at (w2n w) s.vs_memory = n2w (LENGTH bs)
Proof
  strip_tac >>
  `val_in_memory tv (BytesV bs) (w2n w) s.vs_memory` by
    metis_tac[ptr_mem_ok_representation] >>
  drule val_in_memory_bytes_word >> simp[]
QED

Theorem ptr_mem_ok_bytes_clean:
  ptr_mem_ok cx t (BytesV bs) op G tn s /\
  evaluate_type (get_tenv cx) t = SOME tv /\
  eval_operand op s = SOME w /\ tv <> BaseTV AddressT /\
  (!k. tv <> BaseTV (BytesT (Fixed k))) ==>
  (!i. w2n w <= i /\ i < w2n w+32 ==> i NOTIN tn.t_mem) /\
  (!i. w2n w+32 <= i /\ i < w2n w+32+LENGTH bs ==> i NOTIN tn.t_mem)
Proof
  strip_tac >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory tv (BytesV bs) (w2n w) mem` by
    metis_tac[ptr_mem_ok_robust] >>
  drule robust_val_in_memory_bytes_clean >> simp[]
QED

Theorem ptr_mem_ok_string_length:
  ptr_mem_ok cx t (StringV str) op G tn s /\
  evaluate_type (get_tenv cx) t = SOME tv /\
  eval_operand op s = SOME w ==>
  mem_word_at (w2n w) s.vs_memory = n2w (LENGTH str)
Proof
  strip_tac >>
  `val_in_memory tv (StringV str) (w2n w) s.vs_memory` by
    metis_tac[ptr_mem_ok_representation] >>
  gvs[valueEncodingTheory.val_in_memory_def]
QED

Theorem ptr_mem_ok_string_clean:
  ptr_mem_ok cx t (StringV str) op G tn s /\
  evaluate_type (get_tenv cx) t = SOME tv /\
  eval_operand op s = SOME w ==>
  (!i. w2n w <= i /\ i < w2n w+32 ==> i NOTIN tn.t_mem) /\
  (!i. w2n w+32 <= i /\ i < w2n w+32+LENGTH str ==> i NOTIN tn.t_mem)
Proof
  strip_tac >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory tv (StringV str) (w2n w) mem` by
    metis_tac[ptr_mem_ok_robust] >>
  drule robust_val_in_memory_string_clean >> simp[]
QED
