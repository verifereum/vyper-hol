(* TOP-LEVEL: evaluated word types occupy one memory word. *)
Theory localValueStoreProps
Ancestors
  compileEnv vyperValue valueEncoding valueLoadProps

Theorem evaluated_word_memory_size:
  !tenv ty tv.
    evaluate_type tenv ty = SOME tv /\ is_word_type ty ==> type_memory_size tv = 32
Proof
  rpt gen_tac >> strip_tac >> Cases_on `ty` >> gvs[is_word_type_def] >>
  FIRST [drule evaluate_type_base_identity >> strip_tac >> gvs[] >>
      rename1 `is_word_type (BaseT bt)` >> Cases_on `bt` >>
      gvs[is_word_type_def, type_memory_size_def] >>
      rename1 `BytesT byte_bound` >> Cases_on `byte_bound` >>
      gvs[is_word_type_def, type_memory_size_def],
    gvs[evaluate_type_def, AllCaseEqs(), type_memory_size_def]]
QED
