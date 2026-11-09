Theory dftGasToListCompact
Ancestors
  dftGasToListBound dftGasToListFuel dftGasToListAgreement
  dftGasToListTrace list rich_list arithmetic

Theorem bounded_count_maximum[local]:
  !N:num. !f:num->num. (!n. f n <= N) ==> ?j. !n. f n <= f j
Proof
  Induct
  >- (rpt strip_tac >> qexists_tac `0` >> gvs[]) >>
  rpt strip_tac >> Cases_on `?j. f j = SUC N`
  >- (gvs[] >> qexists_tac `j` >> simp[]) >>
  first_x_assum (qspec_then `f` mp_tac) >>
  impl_tac >- (gen_tac >> `f n <= SUC N` by simp[] >>
               `f n <> SUC N` by metis_tac[] >> decide_tac) >> simp[]
QED

Theorem bounded_nonzero_chain:
  (!m n:num. m <= n ==> ?tail. (L:num->bytes32 list) n = L m ++ tail) /\
  (?N. !n. LENGTH (FILTER (\w:bytes32. w <> 0w) (L n)) <= N) ==>
  ?j. !n i. i < LENGTH (L n) ==> padded_reading (L j) i = EL i (L n)
Proof
  strip_tac >>
  `?j. !n. LENGTH (FILTER (\w:bytes32. w <> 0w) (L n)) <=
                LENGTH (FILTER (\w:bytes32. w <> 0w) (L j))` by
    (ho_match_mp_tac bounded_count_maximum >> qexists_tac `N` >> simp[]) >>
  qexists_tac `j` >> rpt strip_tac >>
  Cases_on `n <= j`
  >- (qpat_x_assum `!m n. _` drule >> strip_tac >>
      simp[padded_reading_def] >>
      `i < LENGTH (L j)` by simp[] >>
      simp[EL_APPEND1]) >>
  `j <= n` by decide_tac >>
  qpat_x_assum `!m n. _` drule >> strip_tac >>
  `FILTER (\w:bytes32. w <> 0w) tail = []` by
    (qpat_x_assum `!n. _ <= LENGTH _` (qspec_then `n` mp_tac) >>
     simp[FILTER_APPEND] >>
     Cases_on `FILTER (\w:bytes32. w <> 0w) tail` >> simp[]) >>
  `!w. MEM w tail ==> w = 0w` by
    (gvs[FILTER_EQ_NIL, EVERY_MEM]) >>
  simp[padded_reading_def] >> Cases_on `i < LENGTH (L j)`
  >- simp[EL_APPEND1] >>
  simp[EL_APPEND2] >>
  `i - LENGTH (L j) < LENGTH tail` by (gvs[] >> decide_tac) >>
  metis_tac[MEM_EL]
QED

Theorem context_agreement_exists:
  FINITE {e | orc e <> 0w} ==>
  ?j. !fuel. agrees orc
    (MAP orc (trace_events (trace_context orc j ctx s)))
    (trace_events (trace_context orc fuel ctx s))
Proof
  strip_tac >> drule context_nonzero_count_bounded >>
  disch_then (qspecl_then [`s`, `ctx`] strip_assume_tac) >>
  qspec_then `\fuel. MAP orc (trace_events (trace_context orc fuel ctx s))`
    mp_tac (GEN_ALL bounded_nonzero_chain) >>
  simp[] >> impl_tac
  >- (conj_tac
      >- (rpt strip_tac >> drule context_events_fuel_prefix >>
          disch_then (qspecl_then [`s`, `orc`, `ctx`] strip_assume_tac) >>
          qexists_tac `MAP orc tail` >> simp[MAP_APPEND]) >>
      qexists_tac `N` >> simp[FILTER_MAP, combinTheory.o_DEF]) >>
  strip_tac >> qexists_tac `j` >> simp[agrees_def] >>
  rpt strip_tac >> first_x_assum (qspecl_then [`fuel`, `i`] mp_tac) >>
  simp[EL_MAP]
QED
