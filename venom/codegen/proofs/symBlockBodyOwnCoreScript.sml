(* Client-parametric body induction, independent of execution semantics. *)
Theory symBlockBodyOwnCore
Ancestors
  arithmetic pair

Theorem sym_body_nonterm_result_client:
  !N (A : num # 'a -> bool) R d x.
    (!m. m < d ==> !y. m = N - FST y /\ A y ==> R y) /\
    d = N - FST x /\ A x /\ FST x < N /\
    (?y. FST y = SUC (FST x) /\ A y /\ (R y ==> R x))
    ==> R x
Proof
  rpt strip_tac >>
  `N - FST y < d` by decide_tac >>
  metis_tac[]
QED

Theorem sym_body_run_client:
  !N (A : num # 'a -> bool) R.
    (!x. A x ==>
      R x \/
      (FST x < N /\
       ?y. FST y = SUC (FST x) /\ A y /\ (R y ==> R x)))
    ==> !x. A x ==> R x
Proof
  rpt gen_tac >> strip_tac >>
  `!d x. d = N - FST x /\ A x ==> R x` suffices_by metis_tac[] >>
  completeInduct_on `d` >> rpt strip_tac >>
  qpat_x_assum `!x. A x ==> _` drule >> strip_tac >>
  simp[sym_body_nonterm_result_client]
QED
