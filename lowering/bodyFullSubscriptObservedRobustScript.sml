Theory bodyFullSubscriptObservedRobust
Ancestors
  bodyFullSubscriptLayoutByte representationCleanPtr abiDecodeStaticProps
  exprSimMemoryTransport bodyPtrDefs valueEncodingDefs vyperTyping vyperValue

Theorem observed_bytes_iff[local]:
  (!m'. mem_agree_outside dirty m m' ==> mem_bytes_at a n m' = bs) <=>
  mem_bytes_at a n m = bs /\ (!i. a <= i /\ i < a+n ==> i NOTIN dirty)
Proof
  eq_tac
  >- (strip_tac >> conj_tac
      >- (first_x_assum irule >> simp[mem_agree_outside_def]) >>
      drule robust_mem_bytes_at_clean >> simp[]) >>
  rpt strip_tac >>
  `mem_bytes_at a n m = mem_bytes_at a n m'` suffices_by metis_tac[] >>
  irule mem_bytes_at_bytewise >> fs[mem_agree_outside_def]
QED

Theorem observed_word_iff[local]:
  (!m'. mem_agree_outside dirty m m' ==> mem_word_at a m' = w) <=>
  mem_word_at a m = w /\ (!i. a <= i /\ i < a+32 ==> i NOTIN dirty)
Proof
  eq_tac
  >- (strip_tac >> conj_tac
      >- (first_x_assum irule >> simp[mem_agree_outside_def]) >>
      drule robust_mem_word_at_clean >> simp[]) >>
  rpt strip_tac >>
  `mem_word_at a m = mem_word_at a m'` suffices_by metis_tac[] >>
  irule memory_window_word >> irule mem_bytes_at_bytewise >>
  fs[mem_agree_outside_def]
QED

val observed_simps =
  [val_in_memory_def, subscript_layout_byte_cases, FORALL_AND_THM,
   IMP_CONJ_THM, DISJ_IMP_THM, observed_bytes_iff, observed_word_iff,
   AC CONJ_ASSOC CONJ_COMM]

Theorem observed_representation[local]:
  (!tv v a m.
    (!m'. mem_agree_outside dirty m m' ==> val_in_memory tv v a m') <=>
    val_in_memory tv v a m /\
    (!i. subscript_layout_byte tv v a i ==> i NOTIN dirty)) /\
  (!fs tvs a m.
    (!m'. mem_agree_outside dirty m m' ==> fields_in_memory fs tvs a m') <=>
    fields_in_memory fs tvs a m /\
    (!i. subscript_layout_fields_byte fs tvs a i ==> i NOTIN dirty)) /\
  (!vs a tv m.
    (!m'. mem_agree_outside dirty m m' ==> elems_in_memory vs a tv m') <=>
    elems_in_memory vs a tv m /\
    (!i. subscript_layout_elems_byte vs a tv i ==> i NOTIN dirty)) /\
  (!kvs a tv m.
    (!m'. mem_agree_outside dirty m m' ==> kvs_in_memory kvs a tv m') <=>
    kvs_in_memory kvs a tv m /\
    (!i. subscript_layout_kvs_byte kvs a tv i ==> i NOTIN dirty)) /\
  (!vs tvs a m.
    (!m'. mem_agree_outside dirty m m' ==> tuple_in_memory vs tvs a m') <=>
    tuple_in_memory vs tvs a m /\
    (!i. subscript_layout_tuple_byte vs tvs a i ==> i NOTIN dirty))
Proof
  ho_match_mp_tac val_in_memory_ind >>
  rpt conj_tac >> rpt gen_tac >>
  TRY (simp observed_simps >> NO_TAC)
  >~ [`val_in_memory tv (BytesV _) _ _`]
  >- (rename1 `val_in_memory tv (BytesV _) _ _` >>
      Cases_on `tv` >> TRY (simp observed_simps >> NO_TAC) >>
      rename1 `val_in_memory (BaseTV bt) _ _ _` >>
      Cases_on `bt` >> TRY (simp observed_simps >> NO_TAC) >>
      rename1 `val_in_memory (BaseTV (BytesT bd)) _ _ _` >>
      Cases_on `bd` >> simp observed_simps)
  >~ [`val_in_memory tv (StructV _) _ _`]
  >- (rename1 `val_in_memory tv (StructV _) _ _` >>
      Cases_on `tv` >> simp observed_simps >>
      qexists `m` >> simp[mem_agree_outside_def])
  >~ [`val_in_memory tv (ArrayV (DynArrayV _)) _ _`]
  >- (rename1 `val_in_memory tv (ArrayV (DynArrayV _)) _ _` >>
      Cases_on `tv` >> simp observed_simps >>
      qexists `m` >> simp[mem_agree_outside_def])
  >~ [`val_in_memory tv (ArrayV (TupleV _)) _ _`]
  >- (rename1 `val_in_memory tv (ArrayV (TupleV _)) _ _` >>
      Cases_on `tv` >> simp observed_simps >>
      qexists `m` >> simp[mem_agree_outside_def])
  >~ [`val_in_memory tv (ArrayV (SArrayV _)) _ _`]
  >- (rename1 `val_in_memory tv (ArrayV (SArrayV _)) _ _` >>
      Cases_on `tv` >> simp observed_simps >>
      TRY (qexists `m` >> simp[mem_agree_outside_def] >> NO_TAC) >>
      metis_tac[])
  >~ [`fields_in_memory (_::_) tvs _ _`]
  >- (rename1 `fields_in_memory (_::_) tvs _ _` >>
      Cases_on `tvs` >- simp observed_simps >>
      rename1 `fields_in_memory _ (h::_) _ _` >>
      PairCases_on `h` >> simp observed_simps)
  >> (rename1 `tuple_in_memory (_::_) tvs _ _` >>
      Cases_on `tvs` >> simp observed_simps)
QED

Theorem subscript_observed_robust_iff:
  !tv v a m dirty.
    well_formed_type_value tv /\ value_has_type tv v ==>
    ((!m'. mem_agree_outside dirty m m' ==> val_in_memory tv v a m') <=>
     val_in_memory tv v a m /\
     (!i. subscript_layout_byte tv v a i ==> i NOTIN dirty))
Proof
  simp[cj 1 observed_representation]
QED
