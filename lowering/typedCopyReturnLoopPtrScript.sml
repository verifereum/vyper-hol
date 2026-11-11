(* Constructive counted iteration for typed-copy loops. *)
Theory typedCopyReturnLoopPtr
Ancestors fragGasPathPtr fragGasSeqPtr arithmetic

Theorem typed_copy_counted_iteration:
  (!i G tn s. i < N /\ Inv i G tn s ==>
    ?H tm t. gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
             Inv (SUC i) H tm t) /\
  (!G tn s. Inv N G tn s ==> ~s.vs_halted) ==>
  !i G tn s. i <= N /\ Inv i G tn s ==>
    ?H tm t. gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\ Inv N H tm t
Proof
  strip_tac >> gen_tac >> completeInduct_on `N-i` >> rpt strip_tac >>
  Cases_on `i = N`
  >- (gvs[] >> qexistsl_tac [`G`,`tn`,`s`] >>
      simp[] >> irule (cj 1 gas_path_ptr_rules) >> metis_tac[]) >>
  `i < N /\ SUC i <= N /\ N - SUC i < N-i` by decide_tac >>
  qpat_assum `!i G tn s. i < N /\ _ ==> _` drule_all >> strip_tac >>
  qpat_x_assum `!m. m < _ ==> _` (qspec_then `N-SUC i` mp_tac) >>
  (impl_tac >- decide_tac) >>
  disch_then (qspecl_then [`N`,`SUC i`] mp_tac) >>
  simp[] >> (impl_tac >- metis_tac[]) >>
  disch_then drule_all >> strip_tac >>
  goal_assum (drule_at Any) >>
  drule_all gas_path_ptr_then >> simp[]
QED

