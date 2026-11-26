(* A pure source return prepends the landed head without changing the run. *)
Theory bodyECRecoverOperandReturnConsMods
Ancestors
  gasOutcomeFullMods gasStorage vyperInterpreter vyperState
Libs monadsyntax

Theorem ecrecover_operand_return_cons_mods:
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source (es,s,G,tn) Q R ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (bind source (\vs. return ((v:value)::vs))) (es,s,G,tn)
    (\H raw ee G' tn' t. ?res.
      raw = (case res of INL vs => INL (v::vs) | INR ex => INR ex) /\
      Q H res ee G' tn' t)
    (\H raw ee gt r. ?res.
      raw = (case res of INL vs => INL (v::vs) | INR ex => INR ex) /\
      R H res ee gt r)
Proof
  strip_tac >>
  `ignore_bind (bind source (\vs. return (v::vs))) (return ()) =
   ignore_bind source (return ())` by simp[ignore_bind_def, bind_assoc, bind_return] >>
  `!x. SND (bind source (\vs. return (v::vs)) x) = SND (source x)` by
    (gen_tac >> Cases_on `source x` >> rename1 `source x = (res0,st1)` >>
     Cases_on `res0` >> simp[bind_def, return_def]) >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ source _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_mods_def]) >>
  simp[gas_outcome_full_mods_def] >> qexists_tac `marks`
  >- (disj1_tac >> conj_tac
      >- gvs[gas_bad_storage_at_def] >>
      metis_tac[])
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`case res of INL vs => INL (v::vs) | INR ex => INR ex`,
                    `ee`,`r`,`G'`,`tn'`] >>
      conj_tac >- (gen_tac >> simp[bind_def, return_def] >> Cases_on `res` >> simp[]) >>
      simp[] >> rpt strip_tac >>
      qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
      simp[]
      >- (disj1_tac >> qexists_tac `res` >> simp[]) >>
      disj2_tac >> conj_tac
      >- (qspec_then `\raw. case raw of INL vs => INL (v::vs) | INR ex => INR ex`
            mp_tac (Q.GEN `f` createSizeExitTheory.create_size_exit_ok_map) >>
          simp[]) >>
      qexists_tac `res` >> simp[])
  >> disj2_tac >> disj2_tac >> metis_tac[]
QED
