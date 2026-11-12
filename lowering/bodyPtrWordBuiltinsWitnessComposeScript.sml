(* Constructive composition through an explicit intermediate assertion.
   Both exemption obligations are unchanged from gas_outcome_ptr_bind. *)
Theory bodyPtrWordBuiltinsWitnessCompose
Ancestors gasSummaryComposePtr fragGasPathPtr gasExemptCert gasSummary
  vyperState

Theorem gas_outcome_ptr_bind_mid:
  gas_outcome_ptr D tops (ctx,func) PG source (es,s0,G0,tn0)
    (\res em G tn t. ?v. res = INL v /\ M v em G tn t)
    (\res ee gt r. ?exc. res = INR exc /\ R (INR exc) ee gt r) /\
  (!v em G tn t. M v em G tn t ==>
    gas_outcome_ptr D tops (ctx,func) PG (next v) (em,t,G,tn) Q R) /\
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
  strip_tac >> irule gas_outcome_ptr_bind >>
  asm_rewrite_tac[] >>
  irule gas_outcome_ptr_conseq >>
  qexistsl [`\res em G tn t. ?v. res = INL v /\ M v em G tn t`,
           `\res ee gt r. ?exc. res = INR exc /\ R (INR exc) ee gt r`] >>
  simp[] >> metis_tac[]
QED
