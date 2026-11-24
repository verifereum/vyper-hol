Theory gasOutcomeIfSuffixMods
Ancestors
  gasOutcomeFullMods fragGasOriginPtr fragExec vyperStorageFootprint vyperState

(* The suffix's endpoint is fixed before quantifying over horizons. *)
Theorem gas_outcome_full_mods_zero_suffix_mono:
  gas_outcome_full_mods (DF, lo, explicit, ctx, func, PG) mods cx st0 source
    (es, s, G, tn) Q R /\
  (!res ee G1 tn1 t.
     storage_trace_domain cx st0 ee.storage_trace /\
     (!H. valid_horizon cx st0 H ee.storage_trace ==>
          Q H res ee G1 tn1 t) ==>
     ?u G2 tn2.
       !H. valid_horizon cx st0 H ee.storage_trace ==>
         gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
           (t, G1, tn1) [] (OK u, G2, tn2) /\
         Q' H res ee G2 tn2 u) /\
  (!H res ee gt r. R H res ee gt r ==> R' H res ee gt r) ==>
  gas_outcome_full_mods (DF, lo, explicit, ctx, func, PG) mods cx st0 source
    (es, s, G, tn) Q' R'
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
  disj2_tac >> disj1_tac >>
  Cases_on `exit_result r`
  >- (qexistsl_tac [`res`, `ee`, `r`, `G'`, `tn'`] >> simp[] >>
      rpt strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
        (drule_then strip_assume_tac) >>
      gvs[exit_result_def] >> metis_tac[]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace)
     ee.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
    (drule_then strip_assume_tac) >> gvs[] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       Q H res (ee with gas_obs := []) G' tn' t` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
       (drule_then strip_assume_tac) >> gvs[exit_result_def]) >>
  qpat_x_assum `!res ee G1 tn1 t. _ /\ _ ==> _`
    (qspecl_then [`res`, `ee with gas_obs := []`, `G'`, `tn'`, `t`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >> fs[exit_result_def] >>
  qexistsl_tac [`res`, `ee`, `OK u`, `G2`, `tn2`] >> simp[] >>
  rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ marks _`
    (qspec_then `H` (drule_then assume_tac)) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ [] _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >> simp[] >>
  qpat_assum `gas_origin_ptr_path _ (s,G,tn) marks _`
    (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
  simp[] >> disch_then drule >> simp[]
QED
