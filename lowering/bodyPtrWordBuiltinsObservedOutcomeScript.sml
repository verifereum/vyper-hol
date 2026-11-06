(* Retain the source observation equation when strengthening the SAME path.
   This is only a consumer interface, not a localization theorem. *)
Theory bodyPtrWordBuiltinsObservedOutcome
Ancestors fragGasPathPtr gasSummaryComposePtr

Theorem gas_outcome_ptr_observed_path_strengthen:
  gas_outcome_ptr D tops (ctx,fn) PG source (es,s0,G0,tn0) Q R /\
  (!marks res ee G tn t.
    gas_marked_exec_ptr D (ctx,fn) PG source (es,s0,G0,tn0)
      marks res ee G tn (OK t) /\
    Q res (ee with gas_obs := []) G tn t ==>
    P res (ee with gas_obs := []) G tn t) ==>
  gas_outcome_ptr D tops (ctx,fn) PG source (es,s0,G0,tn0)
    (\res ee G tn t. Q res ee G tn t /\ P res ee G tn t) R
Proof
  rewrite_tac[gas_outcome_ptr_def, gas_summary_ptr_at_def,
              gas_marked_exec_ptr_def] >>
  metis_tac[]
QED
