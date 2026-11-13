(* A bind callback needs the actual marked prefix, not only its post. *)
Theory bodyPtrTypeBuiltinsMarkedBind
Ancestors gasSummaryComposePtr gasSummaryComposePtrAll fragGasPathPtr gasExemptCert vyperState
  gasSummaryCompose gasSummary fragExec

Theorem gas_outcome_ptr_marked_bind:
  gas_outcome_ptr D tops (ctx,func) PG cx st0 source (es,s0,G0,tn0)
    (\H res ee G tn t. ?v. res = INL v /\ Q H v ee G tn t)
    (\H res ee gt r. ?exc. res = INR exc /\ R H (INR exc) ee gt r) /\
  (!v. storage_trace_frame (next v)) /\
  (!marks v mid G tn t.
    (?H. valid_horizon cx st0 H mid.storage_trace) /\
    gas_marked_exec F (ctx,func) source (es,s0) marks (INL v) mid (OK t) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      gas_marked_exec_ptr (D H) (ctx,func) PG source (es,s0,G0,tn0)
        marks (INL v) mid G tn (OK t) /\
      Q H v (mid with gas_obs := []) G tn t) ==>
    gas_outcome_ptr D tops (ctx,func) PG cx st0 (next v)
      (mid with gas_obs := [],t,G,tn) Q' R) /\
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
  gas_outcome_ptr D tops (ctx,func) PG cx st0 (bind source next)
    (es,s0,G0,tn0) Q' R
Proof
  strip_tac >> irule gas_outcome_ptr_bind_all >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`\H res ee gt r. ?exc. res = INR exc /\ R H (INR exc) ee gt r`,
    `\H res ee G tn t. ?v. res = INL v /\ Q H v ee G tn t`] >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `!marks v mid G tn t. _ ==> gas_outcome_ptr _ _ _ _ _ _ _ _ _ _`
    (qspecl_then [`left`, `v`, `mid`, `G`, `tn`, `t`] mp_tac) >>
  simp[gas_marked_exec_ptr_def] >>
  fs[gas_marked_exec_def] >> metis_tac[]
QED
