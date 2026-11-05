(* mem_dead_bytes stays inside its value's region and reads only the
 * value's live bytes.
 *)
Theory ctorDeployDeadSection
Ancestors
  ctorDeployDefs immutableSectionRel immutableValue valueEncoding
  structFieldsProps entryStateRel list rich_list

Theorem slot_le[local]:
  !k n s. k < n ==> k * s + s <= n * s
Proof
  rpt strip_tac >>
  `?d. n = k + 1 + d` by (qexists_tac `n - (k + 1)` >> decide_tac) >>
  gvs[arithmeticTheory.RIGHT_ADD_DISTRIB]
QED

Theorem mem_dead_bytes_range:
  (!sec off tv i.
     mem_dead_bytes sec off tv i ==> off <= i /\ i < off + type_memory_size tv) /\
  (!sec off tvs i.
     mem_dead_bytes_list sec off tvs i ==>
     off <= i /\ i < off + type_memory_size_list tvs) /\
  (!sec off fields i.
     mem_dead_bytes_fields sec off fields i ==>
     off <= i /\ i < off + type_memory_size_fields fields)
Proof
  ho_match_mp_tac mem_dead_bytes_ind >>
  rw[mem_dead_bytes_def, type_memory_size_def] >> res_tac >> gvs[] >>
  rename1 `k < n` >>
  drule slot_le >> disch_then (qspec_then `type_memory_size tv` assume_tac) >>
  Cases_on `k < w2n (mem_word_at off sec)` >>
  gvs[arithmeticTheory.LEFT_ADD_DISTRIB] >> res_tac >> decide_tac
QED

(* mem_dead_bytes reads only the length words its value's live bytes hold. *)
Theorem mem_dead_bytes_frame:
  !sec1 sec2 off tv.
    LENGTH sec2 = LENGTH sec1 /\
    (!j. off <= j /\ j < off + type_memory_size tv /\ j < LENGTH sec1 /\
         ~mem_dead_bytes sec1 off tv j ==> EL j sec2 = EL j sec1) ==>
    mem_dead_bytes sec2 off tv = mem_dead_bytes sec1 off tv
Proof
  cheat
QED
