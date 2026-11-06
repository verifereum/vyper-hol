(* Closed projections avoid recomputing an environment under quantifiers. *)
Theory bodyPtrWordBuiltinsIntervalProjections
Ancestors bodyPtrWordBuiltinsIntervalProbe bodyPtrDefs finite_map
Libs finite_mapLib intReduce
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset intReduce.add_int_compset

Theorem word_interval_vars:
  (FST word_interval_start).ce_vars = FEMPTY |+ ("b", PtrVar (Var "%0") 32)
Proof
  EVAL_TAC >> simp[]
QED

Theorem word_interval_return_buf:
  (FST word_interval_start).ce_return_buf = NONE
Proof
  EVAL_TAC
QED

Theorem word_interval_return_pc:
  (FST word_interval_start).ce_return_pc = NONE
Proof
  EVAL_TAC
QED

Theorem word_interval_next_var:
  (SND word_interval_start).cs_next_var = 5
Proof
  EVAL_TAC
QED
