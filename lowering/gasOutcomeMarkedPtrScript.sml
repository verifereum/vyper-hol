Theory gasOutcomeMarkedPtr
Ancestors
  gasSummaryComposePtr fragGasPathPtr

Theorem gas_outcome_ptr_marked_conseq:
  gas_outcome_ptr D tops (ctx,func) PG cx st0 source (es,s0,G0,tn0) Q R /\
  (!H marks rr mid G tn t.
    valid_horizon cx st0 H mid.storage_trace /\
    gas_marked_exec_ptr (D H) (ctx,func) PG source (es,s0,G0,tn0)
      marks rr mid G tn (OK t) /\
    Q H rr (mid with gas_obs := []) G tn t ==>
    Q' H rr (mid with gas_obs := []) G tn t) ==>
  gas_outcome_ptr D tops (ctx,func) PG cx st0 source (es,s0,G0,tn0) Q' R
Proof
  rewrite_tac[gas_outcome_ptr_def, gas_summary_ptr_at_marked] >>
  metis_tac[]
QED
