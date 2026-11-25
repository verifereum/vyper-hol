Theory entryCreateOutcomeStore
Ancestors
  entryCreateOutcomeWitness fragGasOriginPtr vyperStorageFootprint

(* The suffix runs only on a matched normal result. Its physical and ghost
   endpoints are fixed before the universal horizon quantifier. *)
Theorem witnessed_operand_zero_suffix:
  witnessed_operand_outcome F1 M1 (DF, lo, explicit, ctx, func, PG)
    tops cx st0 source (es, s, G, tn) Q R /\
  (!s m. F1 s m ==> focus s m) /\
  (!s m r. exit_result r /\ M1 s m r ==> M s m r) /\
  (!m res ee G1 tn1 t.
     M1 s m (OK t) /\ storage_trace_domain cx st0 ee.storage_trace /\
     (!H. valid_horizon cx st0 H ee.storage_trace ==>
          Q H res ee G1 tn1 t) ==>
     ?u J tz. M s m (OK u) /\
       !H. valid_horizon cx st0 H ee.storage_trace ==>
         gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
           (t, G1, tn1) [] (OK u, J, tz) /\
         Q' H res ee J tz u) ==>
  witnessed_operand_outcome focus M (DF, lo, explicit, ctx, func, PG)
    tops cx st0 source (es, s, G, tn) Q' R
Proof
  strip_tac >>
  qpat_x_assum `witnessed_operand_outcome _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [witnessed_operand_outcome_def])
  >~ [`gas_bad_storage_at _ _ _ _ _ _`]
  >- (rewrite_tac[witnessed_operand_outcome_def] >> qexists_tac `marks` >>
      disj1_tac >> metis_tac[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rewrite_tac[witnessed_operand_outcome_def] >> qexists_tac `marks` >>
      disj2_tac >> disj2_tac >> metis_tac[]) >>
  rewrite_tac[witnessed_operand_outcome_def] >> qexists_tac `marks` >>
  disj2_tac >> disj1_tac >>
  Cases_on `exit_result r`
  >- (qexistsl_tac [`res`, `ee`, `r`, `G'`, `tn'`] >>
      `M s marks r` by metis_tac[] >>
      rpt conj_tac >> simp[] >> rpt strip_tac >> res_tac >>
      gvs[fragExecTheory.exit_result_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace)
     ee.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  strip_tac >> gvs[] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       Q H res (ee with gas_obs := []) G' tn' t` by
    (rpt strip_tac >> res_tac >> fs[]) >>
  qpat_x_assum `!m res ee G1 tn1 t. _ ==> _`
    (qspecl_then [`marks`, `res`, `ee with gas_obs := []`, `G'`, `tn'`, `t`]
      mp_tac) >>
  impl_tac >- fs[] >> strip_tac >>
  qexistsl_tac [`res`, `ee`, `OK u`, `J`, `tz`] >>
  rpt conj_tac >> simp[] >> rpt strip_tac >> res_tac >> fs[] >>
  metis_tac[gas_origin_ptr_path_append, listTheory.APPEND_NIL]
QED
