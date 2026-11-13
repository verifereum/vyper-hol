Theory bodyPtrIntCallArrayIteration
Ancestors
  fragGasPathPtr venomState arithmetic

(* Iteration keeps the invariant abstract: the caller supplies the concrete
   header state and the one-element successor. *)
Theorem intcall_array_header_iteration_counted:
  !D ctx fn PG Inv n k s G tn.
    (!j s G tn. j <= n /\ Inv j s G tn ==> ~s.vs_halted) /\
    (!j s G tn. j < n /\ Inv j s G tn ==>
      ?t H tf. gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK t) /\
        Inv (SUC j) t H tf) /\
    k <= n /\ Inv k s G tn ==>
    ?t H tf. gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK t) /\ Inv n t H tf
Proof
  rpt gen_tac >> strip_tac >>
  `!r k s G tn. k+r=n /\ Inv k s G tn ==>
    ?t H tf. gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK t) /\ Inv n t H tf`
    suffices_by (disch_then (qspecl_then [`n-k`, `k`, `s`, `G`, `tn`] mp_tac) >>
      `k+(n-k)=n` by decide_tac >> simp[]) >>
  Induct >> map_every qx_gen_tac [`k0`, `s0`, `G0`, `tn0`] >> strip_tac
  >- (gvs[] >> qexistsl_tac [`s0`, `G0`, `tn0`] >>
      simp[] >> irule (cj 1 gas_path_ptr_rules) >> metis_tac[LESS_EQ_REFL]) >>
  `k0 < n` by decide_tac >>
  qpat_x_assum `!j s G tn. j < n /\ _ ==> _` drule_all >> strip_tac >>
  rename1 `k0 + SUC remaining = n` >>
  `SUC k0 + remaining = n` by decide_tac >>
  first_x_assum drule_all >> strip_tac >>
  drule_all gas_path_ptr_then >> simp[] >> metis_tac[]
QED
