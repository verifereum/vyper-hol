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

Theorem pointer_outcome_bind_success:
  gas_outcome_ptr D tops (ctx,func) PG source (es,s0,G0,tn0) P
    (\res ee gt r. ?exc. res = INR exc /\ R (INR exc) ee gt r) /\
  (!res ee G tn t ss tt.
     P res ee G tn t /\ source ss = (res,tt) ==>
     ?v. res = INL v /\
       gas_outcome_ptr D tops (ctx,func) PG (next v) (ee,t,G,tn) Q R) /\
  (!marks err ee leaf fstate.
     gas_exempt_cert F tops (ctx,func) (ignore_bind source (return ()))
       (es,s0) marks (err,ee) (leaf,fstate) ==>
     gas_exempt_cert F tops (ctx,func)
       (bind source (\v. ignore_bind (next v) (return ())))
       (es,s0) marks (err,ee) (leaf,fstate)) /\
  (!left v mid t right err ee leaf fstate.
     gas_marked_exec F (ctx,func) source (es,s0) left (INL v) mid (OK t) /\
     gas_exempt_cert F tops (ctx,func) (ignore_bind (next v) (return ()))
       (mid with gas_obs := [],t) right (err,ee) (leaf,fstate) ==>
     gas_exempt_cert F tops (ctx,func)
       (bind source (\v. ignore_bind (next v) (return ())))
       (es,s0) (left ++ right) (err,ee) (leaf,fstate)) ==>
  gas_outcome_ptr D tops (ctx,func) PG (bind source next)
    (es,s0,G0,tn0) Q R
Proof
  strip_tac >>
  drule pointer_outcome_source_witness >> strip_tac >>
  irule gas_outcome_ptr_bind >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule gas_outcome_ptr_conseq >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
