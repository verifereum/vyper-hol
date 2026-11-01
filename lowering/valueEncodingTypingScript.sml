(* Source value typing supplies the bounds required by memory relocation. *)
Theory valueEncodingTyping
Ancestors
  valueEncoding vyperTyping contractABI vfmConstants arithmetic list rich_list

Theorem typed_payload_fits_memory[local]:
  k <= n ==> k + 32 <= 32 + 32 * word_size n
Proof
  simp[word_size_def] >> strip_tac >>
  irule LESS_EQ_TRANS >> qexists_tac `n` >> simp[] >>
  irule (PURE_REWRITE_RULE [ceil32_def] le_ceil32)
QED

Theorem value_has_type_val_wf:
  (!tv v. value_has_type tv v ==> val_wf tv v) /\
  (!tvs vs. values_have_types tvs vs ==> tuple_val_wf vs tvs) /\
  (!tv n sparse. sparse_has_type tv n sparse ==> kvs_val_wf sparse tv n) /\
  (!tv vs. all_have_type tv vs ==> elems_val_wf vs tv) /\
  (!ftypes fields. struct_has_type ftypes fields ==> fields_val_wf fields ftypes)
Proof
  ho_match_mp_tac value_has_type_ind >>
  rw[value_has_type_def, val_wf_def, type_memory_size_def] >>
  FIRST [drule_all typed_payload_fits_memory >> simp[], gvs[]]
QED

Theorem type_memory_size_fields_zip:
  !names tvs. LENGTH names = LENGTH tvs ==>
    type_memory_size_fields (ZIP (names,tvs)) = type_memory_size_list tvs
Proof
  Induct >> Cases_on `tvs` >> simp[type_memory_size_def]
QED
