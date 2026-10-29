(*
 * Well-typed source values fit their memory representation.
 *
 * TOP-LEVEL:
 *   value_has_type_memory_wf
 *
 * Helpers: word_size_capacity, typed_memory_wf_mutual.
 *)
Theory valueTypingMemoryProps
Ancestors
  vyperTyping valueEncoding arithmetic list vfmConstants
Libs
  intLib

Theorem word_size_capacity:
  !n. n <= 32 * word_size n
Proof
  gen_tac >> rewrite_tac[word_size_def] >>
  qspec_then `32` mp_tac DIVISION >> simp[] >>
  disch_then (qspec_then `n + 31` strip_assume_tac) >>
  `(n + 31) MOD 32 < 32` by simp[] >> intLib.ARITH_TAC
QED

Theorem typed_memory_wf_mutual[local]:
  (!tv v. value_has_type tv v ==> val_wf tv v) /\
  (!tvs vs. values_have_types tvs vs ==> tuple_val_wf vs tvs) /\
  (!tv n kvs. sparse_has_type tv n kvs ==> kvs_val_wf kvs tv n) /\
  (!tv vs. all_have_type tv vs ==> elems_val_wf vs tv) /\
  (!fts fs. struct_has_type fts fs ==> fields_val_wf fs fts)
Proof
  ho_match_mp_tac value_has_type_ind >>
  simp[value_has_type_def, val_wf_def, type_memory_size_def] >>
  rpt strip_tac >> irule LESS_EQ_TRANS >>
  goal_assum (drule_at Any) >> simp[word_size_capacity]
QED

Theorem value_has_type_memory_wf:
  !tv v. value_has_type tv v ==> val_wf tv v
Proof
  metis_tac[typed_memory_wf_mutual]
QED
