(* Typed cleanliness boundary probes; raw instruction execution lives in CopyStep. *)
Theory bodyPtrMakeArrayWordClean
Ancestors
  bodyPtrDefs representationCleanPtr exprSimUnwrap compileEnv vyperValue
  ptrDiscipline venomState exprSimProps

Theorem word_type_no_dead_bytes:
  is_word_type t /\ evaluate_type tenv t = SOME ty ==>
  ~dead_bytes st bs ty j b
Proof
  Cases_on `t` >> gvs[is_word_type_def]
  >- (rename1 `is_word_type (BaseT bt)` >> Cases_on `bt` >>
      gvs[is_word_type_def]
      >~ [`is_word_type (BaseT (BytesT bd))`] >-
         (Cases_on `bd` >> gvs[is_word_type_def] >>
          simp[evaluate_type_def] >> rpt strip_tac >> gvs[dead_bytes_def]) >>
      simp[evaluate_type_def, AllCaseEqs()] >> rpt strip_tac >>
      gvs[dead_bytes_def]) >>
  simp[evaluate_type_def, AllCaseEqs()] >> rpt strip_tac >> gvs[dead_bytes_def]
QED

Theorem ptr_vv_word_key_clean:
  ptr_vv_ok cx t tv (LocatedValue t' p) es G tn s /\
  is_word_type t /\ evaluate_type (get_tenv cx) t = SOME ty /\
  eval_operand p.ptr_operand s = SOME a ==>
  (p.ptr_location = LocStorage ==> key_taint tn.t_stor a = {}) /\
  (p.ptr_location = LocTransient ==> key_taint tn.t_trans a = {})
Proof
  strip_tac >>
  `type_slot_size ty = 1` by metis_tac[word_type_slot_size] >>
  `!st j b. ~dead_bytes st (w2n a) ty j b` by
    metis_tac[word_type_no_dead_bytes] >>
  gvs[ptr_vv_ok_def, key_taint_def, pred_setTheory.EXTENSION] >>
  `w2n a < w2n a + 1` by decide_tac >> metis_tac[arithmeticTheory.LESS_EQ_REFL]
QED

Theorem ptr_mem_word_clean:
  ptr_mem_ok cx t v op G tn s /\ is_word_type t /\
  evaluate_type (get_tenv cx) t = SOME ty /\ value_has_type ty v /\
  eval_operand op s = SOME a ==>
  !i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem
Proof
  strip_tac >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory ty v (w2n a) mem` by metis_tac[ptr_mem_ok_def] >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         mem_word_at (w2n a) mem = typed_val_to_w256 ty v` by
    metis_tac[val_in_memory_word_type] >>
  drule robust_mem_word_at_clean >> simp[]
QED
