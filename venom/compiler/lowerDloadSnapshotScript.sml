Theory lowerDloadSnapshot
Ancestors
  lowerDloadCleanCopy lowerDloadRelocation regularCallEmitSim regularMemorySim
  venomExecSemantics venomState list pred_set

Theorem ld_read_memory_mcopy_byte:
  read_memory a 1 (mcopy p r n s) =
  if p <= a /\ a < p+n then read_memory (r+(a-p)) 1 s
  else read_memory a 1 s
Proof
  simp[mcopy_def, venom_returndata_read_byte, read_memory_def,
       GENLIST, read_byte_write_memory_with_expansion] >>
  Cases_on `p <= a /\ a < p+n` >> simp[EL_GENLIST]
QED

Theorem ld_snapshot_mask:
  {(p:num)+k | k<n /\ r+k IN Ts} =
  {a | p<=a /\ a<p+n /\ r+(a-p) IN Ts}
Proof
  rw[EXTENSION] >> eq_tac
  >- (strip_tac >> gvs[] >> simp[]) >>
  strip_tac >> qexists `x-p` >>
  conj_tac >- decide_tac >>
  conj_tac >- decide_tac >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem ld_byte_rel_mcopy:
  ld_byte_rel R Ts Tt (\a. read_memory a 1 s) (\b. read_memory b 1 t) /\
  (!a b. R a b ==> ((p <= a /\ a < p+n) <=> (q <= b /\ b < q+n))) /\
  (!a b. R a b /\ p <= a /\ a < p+n ==> a-p = b-q) /\
  (!k. k<n ==> R (r+k) (u+k)) ==>
  ld_byte_rel R
    ((Ts DIFF {a | p<=a /\ a<p+n}) UNION {p+k | k<n /\ r+k IN Ts})
    ((Tt DIFF {b | q<=b /\ b<q+n}) UNION {q+k | k<n /\ u+k IN Tt})
    (\a. read_memory a 1 (mcopy p r n s))
    (\b. read_memory b 1 (mcopy q u n t))
Proof
  pure_rewrite_tac[ld_snapshot_mask] >>
  pure_rewrite_tac[ld_byte_rel_def, IN_UNION, IN_DIFF, GSPECIFICATION] >>
  strip_tac >>
  rpt gen_tac >> strip_tac >>
  Cases_on `p <= a /\ a < p+n`
  >- (`q <= b /\ b < q+n` by metis_tac[] >>
      `a-p = b-q` by metis_tac[] >>
      `a-p < n` by simp[] >>
      `R (r+(a-p)) (u+(b-q))` by metis_tac[] >>
      qpat_x_assum `!a b. R a b ==> (b IN Tt ==> a IN Ts) /\ _`
        (qspecl_then [`r+(a-p)`,`u+(b-q)`] mp_tac) >>
      simp[ld_read_memory_mcopy_byte] >>
      `a+r-p = b+r-q` by decide_tac >> metis_tac[]) >>
  `~(q <= b /\ b < q+n)` by metis_tac[] >>
  qpat_x_assum `!a b. R a b ==> (b IN Tt ==> a IN Ts) /\ _`
    (qspecl_then [`a`,`b`] mp_tac) >>
  simp[ld_read_memory_mcopy_byte] >>
  `~(q <= b /\ b < n+q)` by decide_tac >> metis_tac[]
QED
