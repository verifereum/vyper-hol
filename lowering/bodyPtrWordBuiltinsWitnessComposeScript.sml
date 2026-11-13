(* Constructive composition through an explicit intermediate assertion.
   Both exemption obligations are unchanged from gas_outcome_ptr_bind. *)
Theory bodyPtrWordBuiltinsWitnessCompose
Ancestors gasSummaryComposePtr fragGasPathPtr gasExemptCert gasSummary
  vyperState bodyPtrTypeBuiltinsMarkedBind

Theorem gas_outcome_ptr_bind_mid:
  gas_outcome_ptr D tops (ctx,func) PG cx st0 source (es,s0,G0,tn0)
    (\H res em G tn t. ?v. res = INL v /\ M H v em G tn t)
    (\H res ee gt r. ?exc. res = INR exc /\ R H (INR exc) ee gt r) /\
  (!v. storage_trace_frame (next v)) /\
  (!v em G tn t.
    (?H. valid_horizon cx st0 H em.storage_trace) /\
    (!H. valid_horizon cx st0 H em.storage_trace ==> M H v em G tn t) ==>
    gas_outcome_ptr D tops (ctx,func) PG cx st0 (next v) (em,t,G,tn) Q R) /\
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
    (es,s0,G0,tn0) Q R
Proof
  strip_tac >> irule gas_outcome_ptr_marked_bind >>
  goal_assum (drule_at Any) >> simp[] >> qexists_tac `M` >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `!v em G tn t. _ ==> gas_outcome_ptr _ _ _ _ _ _ _ _ _ _` irule >>
  simp[] >> metis_tac[]
QED
