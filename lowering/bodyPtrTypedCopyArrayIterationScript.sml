(* Invariant-parametric finite composition of zero-observation paths. *)
Theory bodyPtrTypedCopyArrayIteration
Ancestors fragGasPathPtr arithmetic

Theorem typed_copy_counted_iteration:
  !D ctx fn PG N I Q.
    (!i G tn s. i < N /\ I i G tn s ==>
      ?H tf u. gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK u) /\
        I (SUC i) H tf u) /\
    (!G tn s. I N G tn s ==>
      ?H tf u. gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK u) /\ Q H tf u) ==>
    !i G tn s. i <= N /\ I i G tn s ==>
      ?H tf u. gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK u) /\ Q H tf u
Proof
  rpt gen_tac >> strip_tac >>
  completeInduct_on `N-i` >> rpt strip_tac >>
  Cases_on `i = N`
  >- (gvs[] >> first_x_assum drule >> simp[]) >>
  `i < N` by decide_tac >>
  qpat_assum `!j G tn s. j < N /\ _ ==> _`
    (qspec_then `i` mp_tac) >>
  disch_then drule_all >> strip_tac >>
  `N - SUC i < N - i /\ SUC i <= N` by decide_tac >>
  qpat_x_assum `!m. m < v ==> _` (qspec_then `N - SUC i` mp_tac) >> simp[] >>
  disch_then (qspecl_then [`N`, `SUC i`] mp_tac) >> simp[] >>
  disch_then drule_all >> strip_tac >>
  drule_all gas_path_ptr_then >> simp[] >> metis_tac[]
QED
