(* Successful counted paths preserve a raised allocation floor. *)
Theory ptrSafetyTransportEndpoint
Ancestors
  ptrSafetyTransport fragGasPathPtr ptrDiscipline venomState arithmetic

Theorem gas_path_ptr_ok_allocas_from:
  !D lo ctx fn PG G tn s marks H u r.
    gas_path_ptr D lo ctx fn PG G tn s marks H u r ==>
    !lower t. r = OK t /\ allocas_from lower s /\
      lower <= s.vs_alloca_next /\ lo <= lower ==>
      allocas_from lower t /\ lower <= t.vs_alloca_next
Proof
  ho_match_mp_tac gas_path_ptr_ind >> rpt conj_tac
  >- (rpt strip_tac >> gvs[])
  >- (rpt strip_tac >>
      drule_all gas_path_ptr_edge_lower_bound_transport >> strip_tac >>
      metis_tac[]) >>
  rpt strip_tac >> gvs[fragExecTheory.exit_result_def]
QED
