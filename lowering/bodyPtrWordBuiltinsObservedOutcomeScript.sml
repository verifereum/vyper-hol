(* Retain the source observation equation when strengthening the SAME path.
   This is only a consumer interface, not a localization theorem. *)
Theory bodyPtrWordBuiltinsObservedOutcome
Ancestors fragGasPathPtr gasSummaryComposePtr gasOutcomeMarkedPtr

Theorem gas_outcome_ptr_observed_path_strengthen:
  gas_outcome_ptr D tops (ctx,fn) PG cx st0 source (es,s0,G0,tn0) Q R /\
  (!H marks res ee G tn t.
    valid_horizon cx st0 H ee.storage_trace /\
    gas_marked_exec_ptr (D H) (ctx,fn) PG source (es,s0,G0,tn0)
      marks res ee G tn (OK t) /\
    Q H res (ee with gas_obs := []) G tn t ==>
    P H res (ee with gas_obs := []) G tn t) ==>
  gas_outcome_ptr D tops (ctx,fn) PG cx st0 source (es,s0,G0,tn0)
    (\H res ee G tn t. Q H res ee G tn t /\ P H res ee G tn t) R
Proof
  strip_tac >> irule gas_outcome_ptr_marked_conseq >>
  goal_assum (drule_at Any) >> simp[] >>
  rpt strip_tac >> simp[] >>
  metis_tac[]
QED
