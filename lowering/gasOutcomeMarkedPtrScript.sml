Theory gasOutcomeMarkedPtr
Ancestors
  gasSummaryComposePtr fragGasPathPtr

Theorem gas_outcome_ptr_marked_conseq:
  gas_outcome_ptr D tops (ctx,func) PG source (es,s0,G0,tn0) Q R /\
  (!marks rr mid G tn t.
    gas_marked_exec_ptr D (ctx,func) PG source (es,s0,G0,tn0)
      marks rr mid G tn (OK t) /\
    Q rr (mid with gas_obs := []) G tn t ==>
    Q' rr (mid with gas_obs := []) G tn t) ==>
  gas_outcome_ptr D tops (ctx,func) PG source (es,s0,G0,tn0) Q' R
Proof
  rewrite_tac[gas_outcome_ptr_def, gas_summary_ptr_at_marked] >>
  metis_tac[]
QED
