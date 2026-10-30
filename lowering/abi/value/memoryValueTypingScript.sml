(* TOP-LEVEL: source typing implies the memory-footprint invariant used by
   complete-layout frame and local-variable producer proofs. Helpers cover
   byte-capacity rounding and the mutual tuple/array/field predicates. *)
Theory memoryValueTyping
Ancestors
  valueEncoding vyperTyping vyperValue contractABI list pair arithmetic vfmConstants

Theorem memory_capacity_covers_bound:
  !bound. bound <= 32 * word_size bound
Proof
  simp[vfmConstantsTheory.word_size_def, GSYM ceil32_def]
QED

Theorem memory_length_fits_capacity:
  !actual bound. actual <= bound ==> actual <= 32 * word_size bound
Proof
  rpt gen_tac >> DISCH_TAC >> mp_tac (Q.SPEC `bound` memory_capacity_covers_bound) >>
  decide_tac
QED

Theorem typed_values_val_wf:
  (!tv v. value_has_type tv v ==> val_wf tv v) /\
  (!tvs vs. values_have_types tvs vs ==> tuple_val_wf vs tvs) /\
  (!tv bound sparse. sparse_has_type tv bound sparse ==> kvs_val_wf sparse tv bound) /\
  (!tv vs. all_have_type tv vs ==> elems_val_wf vs tv) /\
  (!tvs fields. struct_has_type tvs fields ==> fields_val_wf fields tvs)
Proof
  ho_match_mp_tac value_has_type_ind >>
  simp[value_has_type_def, val_wf_def, type_memory_size_def, memory_length_fits_capacity] >>
  rpt strip_tac >> irule memory_length_fits_capacity >> simp[]
QED

Theorem value_has_type_val_wf = CONJUNCT1 typed_values_val_wf;
