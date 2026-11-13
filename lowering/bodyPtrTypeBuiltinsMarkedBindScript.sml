(* A bind callback needs the actual marked prefix, not only its post. *)
Theory bodyPtrTypeBuiltinsMarkedBind
Ancestors gasSummaryComposePtr fragGasPathPtr gasExemptCert vyperState
  gasSummaryCompose gasSummary fragExec

Theorem gas_outcome_ptr_marked_bind:
  gas_outcome_ptr D tops (ctx,func) PG source (es,s0,G0,tn0)
    (\res ee G tn t. ?v. res = INL v /\ Q v ee G tn t)
    (\res ee gt r. ?exc. res = INR exc /\ R (INR exc) ee gt r) /\
  (!marks v mid G tn t.
    gas_marked_exec_ptr D (ctx,func) PG source (es,s0,G0,tn0)
      marks (INL v) mid G tn (OK t) /\
    Q v (mid with gas_obs := []) G tn t ==>
    gas_outcome_ptr D tops (ctx,func) PG (next v)
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
  gas_outcome_ptr D tops (ctx,func) PG (bind source next)
    (es,s0,G0,tn0) Q' R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ source _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_ptr_def])
  >- (pop_assum (strip_assume_tac o
        SIMP_RULE (srw_ss()) [gas_summary_ptr_at_marked]) >> gvs[]
      >~ [`exit_result r`]
      >- (rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `marks` >>
          disj1_tac >> irule gas_summary_ptr_at_bind_exception >>
          metis_tac[]) >>
      irule gas_outcome_ptr_bind_normal >> metis_tac[]) >>
  `ignore_bind (bind source next) (return ()) =
     bind source (\v. ignore_bind (next v) (return ()))` by
    simp[ignore_bind_def, bind_assoc] >>
  asm_rewrite_tac[gas_outcome_ptr_def] >> metis_tac[]
QED
