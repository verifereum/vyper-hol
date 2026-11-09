(* Counted result mapping, preserving the exempt alternative separately. *)
Theory bodyIntCallFamStmtLogGas
Ancestors
  gasOutcome gasSummary gasExemptCert fragGasPath vyperState sum
Libs
  monadsyntax

Theorem gas_marked_exec_return_map:
  gas_marked_exec memory (ctx,func) source (es,s) marks rr mid r ==>
  gas_marked_exec memory (ctx,func)
    (bind source (\v. return (f v))) (es,s) marks
    (case rr of INL v => INL (f v) | INR exc => INR exc) mid r
Proof
  rewrite_tac[gas_marked_exec_def] >> strip_tac >>
  simp[] >> gen_tac >> simp[bind_def] >> Cases_on `rr` >> simp[return_def]
QED

Theorem gas_outcome_return_map:
  gas_outcome memory tops (ctx,func) source (es,s) Q R /\
  (!rr ee t. Q rr ee t ==>
    Q' (case rr of INL v => INL (f v) | INR exc => INR exc) ee t) /\
  (!rr ee r. R rr ee r ==>
    R' (case rr of INL v => INL (f v) | INR exc => INR exc) ee r) ==>
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
