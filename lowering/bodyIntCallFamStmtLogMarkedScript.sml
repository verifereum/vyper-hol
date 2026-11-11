(* Return mapping whose normal consequence can use the source execution. *)
Theory bodyIntCallFamStmtLogMarked
Ancestors
  bodyIntCallFamStmtLogGas gasOutcome gasSummary gasExemptCert
  fragGasPath vyperState sum
Libs
  monadsyntax

Theorem gas_outcome_marked_return_map:
  gas_outcome memory tops (ctx,func) source (es,s) Q R /\
  (!marks rr mid t.
    gas_marked_exec memory (ctx,func) source (es,s) marks rr mid (OK t) /\
    Q rr (mid with gas_obs := []) t ==>
    Q' (case rr of INL v => INL (f v) | INR ex => INR ex)
       (mid with gas_obs := []) t) /\
  (!rr ee r. R rr ee r ==>
    R' (case rr of INL v => INL (f v) | INR ex => INR ex) ee r) ==>
  gas_outcome memory tops (ctx,func)
    (bind source (\v. return (f v))) (es,s) Q' R'
Proof
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      drule gas_marked_exec_return_map >>
      disch_then (qspec_then `f` assume_tac) >> metis_tac[])
  >- (qexists_tac `marks` >> disj1_tac >>
      drule gas_marked_exec_return_map >>
      disch_then (qspec_then `f` assume_tac) >> metis_tac[]) >>
  qexists_tac `marks` >> disj2_tac >>
  gvs[ignore_bind_def, bind_assoc, bind_return] >> metis_tac[]
QED
