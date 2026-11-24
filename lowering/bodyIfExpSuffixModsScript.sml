(* Append the selected arm's zero-reading tail without changing the source
   computation or the linked unit's exemption certificate. *)
Theory bodyIfExpSuffixMods
Ancestors
  gasOutcomeFullMods fragGasOriginPtr fragExec vyperStorageFootprint

val _ = Parse.hide "finish";

Theorem ifexp_outcome_zero_suffix_framed_mods:
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source
    (es,s,G,tn) Q R /\ storage_trace_frame source /\
  (!res ee G1 tn1 t.
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
         valid_horizon cx st0 H es.storage_trace) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==> Q H res ee G1 tn1 t) ==>
    ?t' G2 tn2. !H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
        (t,G1,tn1) [] (OK t',G2,tn2) /\ Q' H res ee G2 tn2 t') ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source
    (es,s,G,tn) Q' R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_full_mods_def])
  >~ [`gas_bad_storage_at _ _ _ _ _ _`]
  >- (rewrite_tac[gas_outcome_full_mods_def] >> qexists `marks` >>
      disj1_tac >> simp[] >> qexistsl [`H`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish`] >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rewrite_tac[gas_outcome_full_mods_def] >> qexists `marks` >>
      disj2_tac >> disj2_tac >>
      qexistsl [`err`,`ee`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish`] >>
      simp[] >> qexists `H` >> simp[]) >>
  rewrite_tac[gas_outcome_full_mods_def] >> qexists `marks` >>
  disj2_tac >> disj1_tac >>
  Cases_on `exit_result r`
  >- (qexistsl [`res`,`ee`,`r`,`G'`,`tn'`] >> simp[] >> rpt strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _` drule >>
      Cases_on `r` >> gvs[exit_result_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace)
     ee.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> gvs[] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       valid_horizon cx st0 H es.storage_trace` by
    (rpt strip_tac >>
     qpat_assum `!tail. source _ = _` (qspec_then `[]` assume_tac) >>
     `valid_horizon cx st0 H (ee with gas_obs := []).storage_trace` by simp[] >>
     drule_all valid_horizon_frame >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       Q H res (ee with gas_obs := []) G' tn' t` by
    (rpt strip_tac >> qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _` drule >>
     simp[fragExecTheory.exit_result_def]) >>
  qpat_x_assum `!res ee G1 tn1 t. _ /\ _ /\ _ ==> _`
    (qspecl_then [`res`,`ee with gas_obs := []`,`G'`,`tn'`,`t`] mp_tac) >>
  simp[] >> strip_tac >> qexistsl [`res`,`ee`,`OK t'`,`G2`,`tn2`] >>
  simp[] >> rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ (s,G,tn) _ _ /\ _`
    drule >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ (t,G',tn') _ _ /\ _`
    drule >> strip_tac >> simp[] >>
  qpat_assum `gas_origin_ptr_path _ (s,G,tn) _ _`
    (mp_then Any mp_tac gas_origin_ptr_path_append) >>
  disch_then (drule o SIMP_RULE (srw_ss()) []) >> simp[]
QED
