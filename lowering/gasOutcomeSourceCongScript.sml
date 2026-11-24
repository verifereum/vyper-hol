Theory gasOutcomeSourceCong
Ancestors
  gasOutcome gasStorage gasSummary gasExemptCert vyperState

(* All three alternatives keep their original gas marks. *)
Theorem gas_outcome_source_cong:
  gas_outcome memory tops (ctx,func) cx st0 source (es,s) Q R /\
  (!gs. source' (es with gas_obs := gs) = source (es with gas_obs := gs)) ==>
  gas_outcome memory tops (ctx,func) cx st0 source' (es,s) Q R
Proof
  rw[gas_outcome_def] >> qexists_tac `marks`
  >- (disj1_tac >> fs[gas_bad_storage_at_def])
  >- (disj2_tac >> disj1_tac >>
      fs[gas_summary_at_def, gas_marked_exec_def] >>
      qexistsl_tac [`res`, `es_end`, `r`] >> simp[]) >>
  disj2_tac >> disj2_tac >>
  rename1 `gas_exempt_cert _ _ _ _ _ _ (err,ee) (leaf,target_end)` >>
  qexistsl_tac [`err`, `ee`, `leaf`, `target_end`] >>
  irule gas_exempt_cert_source_cong >>
  qexists_tac `ignore_bind source (return ())` >>
  simp[ignore_bind_def, bind_def]
QED
