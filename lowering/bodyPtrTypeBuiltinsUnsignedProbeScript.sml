(* Interface probes only; independent of the authorized signed residual. *)
Theory bodyPtrTypeBuiltinsUnsignedProbe
Ancestors
  bodyPtrTypeBuiltinsPartialRead ptrDiscipline venomInst codegenRel
  pred_set arithmetic

Theorem unsigned_data_window_shift_clean:
  !M a n.
    n <= 32 /\ (!i. a <= i /\ i < a+n ==> i NOTIN M) ==>
    shift_taint SHR (8*(32-n)) (mem_word_taint M a) = {}
Proof
  rpt strip_tac >>
  irule (cj 1 partial_word_shift_clean) >> simp[mem_word_taint_def] >>
  rpt strip_tac >> spose_not_then strip_assume_tac >>
  `a <= a+i /\ a+i < a+n` by decide_tac >> metis_tac[]
QED

Theorem extract32_data_window_clean:
  !M a off len.
    off+32 <= len /\
    (!i. a <= i /\ i < a+len ==> i NOTIN M) ==>
    mem_word_taint M (a+off) = {}
Proof
  simp[mem_word_taint_def, EXTENSION] >> rpt strip_tac >>
  spose_not_then strip_assume_tac >>
  `a <= a+(off+x) /\ a+(off+x) < a+len` by decide_tac >> metis_tac[]
QED
