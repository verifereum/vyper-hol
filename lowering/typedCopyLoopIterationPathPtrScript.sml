Theory typedCopyLoopIterationPathPtr
Ancestors
  fragGasPathPtr arithmetic

Theorem gas_path_ptr_bounded_iteration:
  !D lo ctx func PG Inv Q n.
    (!i G tn s. i < n /\ Inv i G tn s ==>
      ?G' tn' s'.
        gas_path_ptr D lo ctx func PG G tn s 0 G' tn' (OK s') /\
        Inv (i + 1) G' tn' s') /\
    (!G tn s. Inv n G tn s ==>
      ?G' tn' s'.
        gas_path_ptr D lo ctx func PG G tn s 0 G' tn' (OK s') /\
        Q G' tn' s') ==>
    !i G tn s. i <= n /\ Inv i G tn s ==>
      ?G' tn' s'.
        gas_path_ptr D lo ctx func PG G tn s 0 G' tn' (OK s') /\
        Q G' tn' s'
Proof
  rpt gen_tac >> strip_tac >>
  qsuff_tac
    `!k i G tn s. n - i = k /\ i <= n /\ Inv i G tn s ==>
      ?G' tn' s'.
        gas_path_ptr D lo ctx func PG G tn s 0 G' tn' (OK s') /\
        Q G' tn' s'`
  >- metis_tac[] >>
  Induct_on `k`
  >- (rpt strip_tac >> `i = n` by decide_tac >> gvs[]) >>
  rpt strip_tac >>
  `i < n` by decide_tac >>
  qpat_x_assum `!i G tn s. i < n /\ _ ==> _` drule >>
  disch_then drule >> strip_tac >>
  first_x_assum (qspec_then `i + 1` mp_tac) >>
  simp[] >>
  disch_then drule >>
  strip_tac >>
  qexistsl [`G''`, `tn''`, `s''`] >>
  simp[] >>
  metis_tac[gas_path_ptr_then, ADD_CLAUSES]
QED
