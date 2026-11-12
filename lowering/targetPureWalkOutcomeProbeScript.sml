(* Diagnostic only: this negates the post, not the full theorem antecedent. *)
Theory targetPureWalkOutcomeProbe
Ancestors
  targetPureWalkModuleProbe gasOutcome gasSummary gasExemptCert exprSimDefs
  vyperState

Theorem module_probe_no_framed_outcome:
  !ctx func s0 P.
    ~gas_outcome F (cx_tops module_probe_cx) (ctx,func)
      (eval_base_place module_probe_cx module_probe_target)
      (module_probe_state,s0)
      (\res ee t. P res ee t /\
        machine_frame (module_probe_state with logs := ee.logs) ee)
      (\res ee r. expr_exit res r)
Proof
  rpt gen_tac >> strip_tac >>
  fs[gas_outcome_def, gas_summary_at_def]
  >- (gvs[gas_marked_exec_def] >>
      first_x_assum (qspec_then `[]` mp_tac) >>
      strip_tac >> drule module_probe_source_not_frame >> simp[])
  >- (gvs[gas_marked_exec_def] >>
      first_x_assum (qspec_then `[]` mp_tac) >>
      simp[module_probe_source_execution] >> strip_tac >>
      gvs[expr_exit_def])
  >> drule gas_exempt_cert_execution >> strip_tac >>
  first_x_assum (qspec_then `[]` mp_tac) >>
  simp[ignore_bind_def, bind_def, module_probe_source_execution,
       vyperStateTheory.return_def]
QED
