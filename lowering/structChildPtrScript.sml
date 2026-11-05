(* Positional struct representation, with explicit metadata alignment. *)
Theory structChildPtr
Ancestors typedCopyLayoutPtr valueEncoding list arithmetic

Theorem fields_in_memory_element:
  !fields ftvs addr mem i.
    LENGTH fields = LENGTH ftvs /\ MAP FST fields = MAP FST ftvs /\
    fields_in_memory fields ftvs addr mem /\ i < LENGTH ftvs ==>
    val_in_memory (SND (EL i ftvs)) (SND (EL i fields))
      (addr + SUM (MAP (type_memory_size o SND) (TAKE i ftvs))) mem
Proof
  Induct >> Cases_on `ftvs` >> simp[] >>
  gen_tac >> PairCases_on `h` >> PairCases_on `h'` >>
  simp[val_in_memory_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `i` >> gvs[] >>
  first_x_assum (qspecl_then [`t`, `addr + type_memory_size h1`, `mem`, `n`] mp_tac) >>
  asm_simp_tac bool_ss [] >>
  simp_tac bool_ss [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
QED

Theorem fields_in_memory_robust_element:
  !fields ftvs addr tn mem i.
    LENGTH fields = LENGTH ftvs /\ MAP FST fields = MAP FST ftvs /\
    i < LENGTH ftvs /\
    (!m. mem_agree_outside tn mem m ==> fields_in_memory fields ftvs addr m) ==>
    !m. mem_agree_outside tn mem m ==>
    val_in_memory (SND (EL i ftvs)) (SND (EL i fields))
      (addr + SUM (MAP (type_memory_size o SND) (TAKE i ftvs))) m
Proof
  rpt strip_tac >> irule fields_in_memory_element >> simp[] >> metis_tac[]
QED

Theorem struct_metadata_prefix_sizes:
  !fs ftvs i.
    LENGTH fs = LENGTH ftvs /\
    (!j. j < LENGTH ftvs ==>
      SND (SND (EL j fs)) = type_memory_size (SND (EL j ftvs))) ==>
    MAP (SND o SND) (TAKE i fs) =
    MAP (type_memory_size o SND) (TAKE i ftvs)
Proof
  rpt strip_tac >> irule LIST_EQ >> simp[LENGTH_TAKE_EQ] >> rpt strip_tac >>
  `x < LENGTH fs /\ x < LENGTH ftvs /\ x < i` by decide_tac >>
  `x < LENGTH (TAKE i fs) /\ x < LENGTH (TAKE i ftvs)` by
    simp[LENGTH_TAKE_EQ] >>
  simp[EL_MAP, EL_TAKE]
QED

Theorem fields_in_memory_robust_metadata_element:
  !fields ftvs fs addr tn mem i.
    LENGTH fields = LENGTH ftvs /\ MAP FST fields = MAP FST ftvs /\
    LENGTH fs = LENGTH ftvs /\ MAP FST fs = MAP FST ftvs /\
    (!j. j < LENGTH ftvs ==>
      SND (SND (EL j fs)) = type_memory_size (SND (EL j ftvs))) /\
    i < LENGTH ftvs /\
    (!m. mem_agree_outside tn mem m ==> fields_in_memory fields ftvs addr m) ==>
    !m. mem_agree_outside tn mem m ==>
    val_in_memory (SND (EL i ftvs)) (SND (EL i fields))
      (addr + SUM (MAP (SND o SND) (TAKE i fs))) m
Proof
  rpt strip_tac >> drule_all struct_metadata_prefix_sizes >>
  disch_then (qspec_then `i` assume_tac) >> gvs[] >>
  irule fields_in_memory_robust_element >> simp[] >> metis_tac[]
QED
