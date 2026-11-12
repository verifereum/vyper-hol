(* Path invariants allow arbitrary control-flow excursions and zero-count edges. *)
Theory bodyPtrStructLitPhaseInvariant
Ancestors fragGasPathPtr fragExec

Theorem gas_path_ptr_success_invariant:
  !D lo ctx fn PG G0 tn0 s0 k G tn r.
    gas_path_ptr D lo ctx fn PG G0 tn0 s0 k G tn r ==>
    !P.
      (!H un s n H' un' t.
         gas_path_ptr_edge D lo ctx fn PG H un s n H' un' (OK t) /\
         P H un s ==> P H' un' t) ==>
      P G0 tn0 s0 ==>
      !t. r = OK t ==> P G tn t
Proof
  ho_match_mp_tac gas_path_ptr_ind >> rpt conj_tac
  >- simp[]
  >- (rpt strip_tac >>
      qpat_x_assum `!P. _` (qspec_then `P` mp_tac) >>
      metis_tac[])
  >> rpt strip_tac >> gvs[exit_result_def]
QED

Theorem gas_path_ptr_phase_invariant:
  (!G tn s n H un t.
     gas_path_ptr_edge D lo ctx fn PG G tn s n H un (OK t) /\
     B s /\ ~B t ==> C H un t) /\
  (!G tn s n H un t.
     gas_path_ptr_edge D lo ctx fn PG G tn s n H un (OK t) /\
     ~B s /\ C G tn s /\ ~B t ==> C H un t) /\
  gas_path_ptr D lo ctx fn PG G0 tn0 s0 k G tn (OK t) /\
  (B s0 \/ C G0 tn0 s0) /\ ~B t ==> C G tn t
Proof
  rpt strip_tac >>
  drule gas_path_ptr_success_invariant >>
  disch_then (qspec_then `\G tn s. B s \/ C G tn s` mp_tac) >>
  pure_rewrite_tac [BETA_THM] >> metis_tac[]
QED
