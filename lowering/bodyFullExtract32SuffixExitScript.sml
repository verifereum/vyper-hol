(* A pure Extract32 suffix can raise Error, but cannot halt. *)
Theory bodyFullExtract32SuffixExit
Ancestors
  haltExitProj
  gasOutcomeFull exprSimDefs vyperInterpreter vyperState

Theorem extract32_lift_sum_value_exit_full:
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (bind (lift_sum result) (\v. return (Value v))) (es,s,G,tn)
    Q (\H res ee gt r. expr_exit res r) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (bind (lift_sum result) (\v. return (Value v))) (es,s,G,tn)
    Q (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))
Proof
  rw[gas_outcome_full_def] >> qexists_tac `marks`
  >- metis_tac[]
  >- (disj2_tac >> disj1_tac >>
      `res <> INR HaltException` by
        (qpat_assum `!tail. _ = (res,_)` (qspec_then `[]` mp_tac) >>
         Cases_on `result` >>
         simp[NoAsms, lift_sum_def, bind_def, return_def, raise_def] >>
         strip_tac >> gvs[]) >>
      `!u. expr_exit res (Halt u) ==> res = INR HaltException` by
        (gen_tac >> Cases_on `res` >> simp[expr_exit_def] >>
         Cases_on `y` >> gvs[expr_exit_def]) >>
      qexistsl_tac [`res`, `ee`, `r`, `G'`, `tn'`] >>
      metis_tac[halt_exit_not_halt])
  >> metis_tac[]
QED
