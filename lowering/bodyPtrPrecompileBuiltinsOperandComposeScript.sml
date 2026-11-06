Theory bodyPtrPrecompileBuiltinsOperandCompose
Ancestors
  gasSummaryComposePtr fragGasPathPtr vyperState

Theorem pointer_summary_source_witness:
  gas_summary_ptr_at D (ctx,func) PG marks source (es,s0,G0,tn0) P R ==>
  gas_summary_ptr_at D (ctx,func) PG marks source (es,s0,G0,tn0)
    (\res ee G tn t. P res ee G tn t /\
       ?ss tt. source ss = (res,tt)) R
Proof
  rw[gas_summary_ptr_at_marked] >>
  `?ss tt. source ss = (res,tt)` by
    (fs[gas_marked_exec_ptr_def] >>
     first_x_assum (qspec_then `[]` mp_tac) >> metis_tac[]) >>
  metis_tac[]
QED

Theorem pointer_outcome_source_witness:
  gas_outcome_ptr D tops (ctx,func) PG source (es,s0,G0,tn0) P R ==>
  gas_outcome_ptr D tops (ctx,func) PG source (es,s0,G0,tn0)
    (\res ee G tn t. P res ee G tn t /\
       ?ss tt. source ss = (res,tt)) R
Proof
  rewrite_tac[gas_outcome_ptr_def] >>
  metis_tac[pointer_summary_source_witness]
QED
