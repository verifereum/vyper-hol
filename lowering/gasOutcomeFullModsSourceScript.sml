(* Extend linked outcomes by a zero-gas suffix. *)
Theory gasOutcomeFullModsSource
Ancestors
  gasOutcomeFullMods fragGasOriginPtr fragGasOrigin fragGasPath fragGasMode
  gasStorage fragExec vyperStorageFootprint vyperState venomState list

Theorem gas_outcome_full_mods_zero_suffix:
  gas_outcome_full_mods (DF, lo, explicit, ctx, func, PG) mods cx st0 source
    (es, s, G, tn) Q R /\
  (!res ee G1 tn1 t.
     storage_trace_domain cx st0 ee.storage_trace /\
     (!H. valid_horizon cx st0 H ee.storage_trace ==>
          Q H res ee G1 tn1 t) ==>
     ?t' G2 tn2.
       !H. valid_horizon cx st0 H ee.storage_trace ==>
         gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
           (t, G1, tn1) [] (OK t', G2, tn2) /\
         Q' H res ee G2 tn2 t') ==>
  gas_outcome_full_mods (DF, lo, explicit, ctx, func, PG) mods cx st0 source
    (es, s, G, tn) Q' R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_mods_def])
  >~ [`gas_bad_storage_at _ _ _ _ _ _`]
  >- (rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks` >>
      disj1_tac >> metis_tac[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks` >>
      disj2_tac >> disj2_tac >> metis_tac[]) >>
  rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks` >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace)
     ee.storage_trace` by fs[storage_trace_domain_def] >>
  Cases_on `exit_result r`
  (* an exit keeps its endpoint and exit post *)
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`res`, `ee`, `r`, `G'`, `tn'`] >>
      rpt conj_tac >- fs[] >- fs[] >>
      rpt strip_tac >> res_tac >> gvs[fragExecTheory.exit_result_def]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  strip_tac >> gvs[] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       Q H res (ee with gas_obs := []) G' tn' t` by
    (rpt strip_tac >> res_tac >> fs[fragExecTheory.exit_result_def]) >>
  qpat_x_assum `!res ee G1 tn1 t. _ /\ _ ==> _`
    (qspecl_then [`res`, `ee with gas_obs := []`, `G'`, `tn'`, `t`] mp_tac) >>
  impl_tac >- fs[] >> strip_tac >>
  disj2_tac >> disj1_tac >>
  qexistsl_tac [`res`, `ee`, `OK t'`, `G2`, `tn2`] >>
  rpt conj_tac >- fs[] >- fs[] >>
  rpt strip_tac >> res_tac >> fs[] >>
  metis_tac[gas_origin_ptr_path_append, APPEND_NIL]
QED
