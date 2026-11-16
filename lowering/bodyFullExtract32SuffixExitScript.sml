(* A pure Extract32 suffix can raise Error, but cannot halt. *)
Theory bodyFullExtract32SuffixExit
Ancestors
  gasOutcomeFull exprSimDefs vyperInterpreter vyperState

Theorem extract32_lift_sum_value_exit_full:
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (bind (lift_sum result) (\v. return (Value v))) (es,s,G,tn)
    Q (\H res ee gt r. expr_exit res r) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (bind (lift_sum result) (\v. return (Value v))) (es,s,G,tn)
    Q (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r)
Proof
  rw[gas_outcome_full_def] >> qexists_tac `marks`
  >- metis_tac[]
  >- (disj2_tac >> disj1_tac >>
      `res <> INR HaltException` by
        (qpat_assum `!tail. _ = (res,_)` (qspec_then `[]` mp_tac) >>
         Cases_on `result` >>
         simp[NoAsms, lift_sum_def, bind_def, return_def, raise_def] >>
         strip_tac >> gvs[]) >>
      qexistsl_tac [`res`, `ee`, `r`, `G'`, `tn'`] >>
      simp[halt_exit_def])
  >> metis_tac[]
QED
