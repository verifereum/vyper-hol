Theory bodyPtrTypeBuiltinsPure
Ancestors fragGasPathPtr gasSummary

Theorem gas_outcome_ptr_pure:
  !D tops ctx func PG source es s G tn res Q R.
    ~s.vs_halted /\
    (!gs. source (es with gas_obs := gs) = (res, es with gas_obs := gs)) /\
    Q res (es with gas_obs := []) G tn s ==>
    gas_outcome_ptr D tops (ctx,func) PG source (es,s,G,tn) Q R
Proof
  rpt strip_tac >> rewrite_tac[gas_outcome_ptr_def] >>
  qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`res`,`es`,`G`,`tn`,`OK s`] >>
  simp[gas_explicit_def] >>
  irule (cj 1 gas_path_ptr_rules) >> simp[]
QED
