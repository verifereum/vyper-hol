Theory extRetRepresentationProbePtr
Ancestors
  representationCleanPtr bodyPtrDefs vyperTypeSystem vyperValue
  vyperContext compileEnv ptrDiscipline words

Theorem ptr_val_ok_bytes_live_clean:
  ptr_val_ok cx (BaseT (BytesT (Dynamic cap))) (BytesV bs) op G tn s /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic cap))) = SOME tv /\
  eval_operand op s = SOME w ==>
  !i. w2n w <= i /\ i < w2n w + 32 + LENGTH bs ==> i NOTIN tn.t_mem
Proof
  strip_tac >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory tv (BytesV bs) (w2n w) mem` by
    (gvs[ptr_val_ok_def, ptr_mem_ok_def, is_word_type_def] >> metis_tac[]) >>
  drule robust_val_in_memory_bytes_clean >>
  `tv = BaseTV (BytesT (Dynamic cap))` by
    gvs[evaluate_type_def, AllCaseEqs()] >>
  simp[] >> strip_tac >> gen_tac >> strip_tac >>
  Cases_on `i < w2n w + 32`
  >- (qpat_x_assum `!i. w2n w <= i /\ _ ==> _` irule >> simp[]) >>
  qpat_x_assum `!i. w2n w + 32 <= i /\ _ ==> _` irule >> simp[]
QED
