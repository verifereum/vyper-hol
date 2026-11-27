(* A linked counted endpoint with one implicit gas observation. *)
Theory bodyShaImplicitEndpointMods
Ancestors
  gasOutcomeFullMods gasSummary

Theorem sha_implicit_endpoint_mods:
  (!tail. source (mid with gas_obs := tail) = (res, ef with gas_obs := tail)) /\
  storage_trace_domain cx st0 ef.storage_trace /\
  (!H. valid_horizon cx st0 H ef.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fnm,PG)
      (s,G,tn) [F] (r,Gf,tf) /\
    ((?t. r = OK t /\ Q H res (ef with gas_obs := []) Gf tf t) \/
     (exit_result r /\ create_size_exit_ok ctx res r /\
      R H res (ef with gas_obs := []) (Gf,tf) r))) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,fnm,PG) mods cx st0 source
    (mid,s,G,tn) Q R
Proof
  strip_tac >>
  `gas_explicit [F] s.vs_gas_readings = []` by
    (Cases_on `s.vs_gas_readings` >> simp[gas_explicit_cons]) >>
  rewrite_tac[gas_outcome_full_mods_def] >>
  qexists_tac `[F]` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`res`, `ef`, `r`, `Gf`, `tf`] >> simp[]
QED

