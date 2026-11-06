(* Boundary probes for the zero-capacity string normalization branch. *)
Theory storageNormalizationAuditPtr
Ancestors vyperValue words arithmetic

Theorem storage_string_zero_capacity_slots:
  type_slot_size (BaseTV (StringT 0)) = 1
Proof
  EVAL_TAC >> `0 < dimword(:256)` by simp[] >>
  `1 <= dimword(:256)` by decide_tac >> simp[]
QED

Theorem storage_string_zero_capacity_type:
  evaluate_type tenv (BaseT (StringT 0)) = SOME (BaseTV (StringT 0))
Proof
  EVAL_TAC >> `0 < dimword(:256)` by simp[] >>
  `1 <= dimword(:256)` by decide_tac >> simp[]
QED
