(* Gas composition for a place-valued pointer prefix. *)
Theory tuplePlaceHeadGas
Ancestors
  tuplePlaceSuffixCode tuplePlaceTargetGas tuplePlaceWriteOutcome tuplePlaceSourceGas
  tuplePlaceSourceHead tuplePlaceStep placeStoreStaticExit
  gasOutcome gasSummary gasSummaryCompose gasExemptCert gasStorage vyperState
  vyperStorageFootprint vyperStorageTrace
  targetPlaceSimCases exprSimDefs fragGasMode fragGasPath
  vyperFiniteStoragePreservation vyperStoragePlaceObserved

Theorem tuple_place_gas_outcome_prefix:
  gas_marked_exec memory (ctx,func)
    (a : evaluation_state -> place evaluation_result)
    (es,s0) left (INL v) mid (OK t) /\
  gas_outcome memory tops (ctx,func) cx st0 (k v)
    (mid with gas_obs := [],t) Q R ==>
  gas_outcome memory tops (ctx,func) cx st0 (bind a k) (es,s0) Q R
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac mp_tac) >>
  rewrite_tac[gas_outcome_def] >>
  disch_then (qx_choose_then `right` (DISJ_CASES_THEN mp_tac))
  >- (strip_tac >> qexists `left ++ right` >> disj1_tac >>
      irule gasStorageTheory.gas_bad_storage_at_bind_right >>
      metis_tac[]) >>
  disch_then (DISJ_CASES_THEN mp_tac)
  >- (rewrite_tac[gas_summary_at_def] >>
      disch_then (qx_choose_then `out` (qx_choose_then `fin`
        (qx_choose_then `r` (CONJUNCTS_THEN2 assume_tac assume_tac)))) >>
      qexists `left ++ right` >> disj2_tac >> disj1_tac >>
      rewrite_tac[gas_summary_at_def] >>
      qexistsl [`out`,`fin`,`r`] >>
      conj_tac >- (irule gas_marked_exec_bind_normal >>
                    goal_assum drule >> simp[]) >>
      first_assum ACCEPT_TAC) >>
  strip_tac >>
  rename1 `gas_exempt_cert _ _ _ _ _ right (err,ef) (callee,tf)` >>
  qexists `left ++ right` >> disj2_tac >> disj2_tac >>
  qexistsl [`err`,`ef`,`callee`,`tf`] >>
  rewrite_tac[ignore_bind_def,bind_assoc] >>
  irule gas_exempt_cert_bind_place >>
  qexistsl [`mid`,`t`,`v`] >> simp[GSYM ignore_bind_def]
QED

(* The continuation also gets the source's storage domain at its endpoint,
   so it can pick a valid horizon there. *)
Theorem tuple_place_gas_outcome_bind_exec:
  gas_outcome memory tops (ctx,func) cx st0
    (a : evaluation_state -> place evaluation_result) (es,s0) P Exit /\
  (!H res ee t. P H res ee t ==> ?v. res = INL v) /\
  (!H res ee r. Exit H res ee r ==> ?ex. res = INR ex /\ R H (INR ex) ee r) /\
  (!marks v mid t.
    gas_marked_exec memory (ctx,func) a (es,s0) marks (INL v) mid (OK t) /\
    storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
       P H (INL v) (mid with gas_obs := []) t) ==>
    gas_outcome memory tops (ctx,func) cx st0 (k v)
      (mid with gas_obs := [],t) Q R) /\
  (!v. storage_trace_frame (k v)) ==>
  gas_outcome memory tops (ctx,func) cx st0 (bind a k) (es,s0) Q R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ a _ _ _`
    (mp_tac o BETA_RULE o REWRITE_RULE [gas_outcome_def]) >>
  disch_then (qx_choose_then `marks` (DISJ_CASES_THEN mp_tac))
  >- (strip_tac >> rewrite_tac[gas_outcome_def] >>
      qexists `marks` >> disj1_tac >>
      irule gasStorageTheory.gas_bad_storage_at_bind_left >> simp[]) >>
  disch_then (DISJ_CASES_THEN mp_tac)
  >- (rewrite_tac[gas_summary_at_def] >> BETA_TAC >>
      disch_then (qx_choose_then `res` (qx_choose_then `mid`
        (qx_choose_then `r` (CONJUNCTS_THEN2 assume_tac mp_tac)))) >>
      reverse (Cases_on `vyperStorageFootprint$storage_trace_domain cx st0 mid.storage_trace`)
      >- (disch_then kall_tac >> rewrite_tac[gas_outcome_def] >>
          qexists `marks` >> disj1_tac >>
          irule gasStorageTheory.gas_bad_storage_at_bind_left >> simp[] >>
          irule gasStorageTheory.gas_bad_storage_at_counted_prefix >>
          metis_tac[]) >>
      `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
         mid.storage_trace` by
        fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
      disch_then (DISJ_CASES_THEN strip_assume_tac)
      >- (qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
            (assume_tac o SIMP_RULE (srw_ss()) []) >>
          `?v. res = INL v` by metis_tac[] >> gvs[] >>
          irule tuple_place_gas_outcome_prefix >>
          qexistsl [`marks`,`mid`,`t`,`v`] >> simp[] >>
          first_x_assum irule >> simp[] >>
          goal_assum (drule_at Any)) >>
      qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
        (assume_tac o SIMP_RULE (srw_ss()) []) >>
      `?ex. res = INR ex` by metis_tac[] >> gvs[] >>
      rewrite_tac[gas_outcome_def] >>
      qexists `marks` >> disj2_tac >> disj1_tac >>
      rewrite_tac[gas_summary_at_def] >>
      qexistsl [`INR ex`,`mid`,`r`] >>
      conj_tac >- (irule gas_marked_exec_bind_exception >> simp[]) >>
      BETA_TAC >> simp[] >> disj2_tac >> rpt strip_tac >>
      qpat_x_assum `!H res ee r. Exit H res ee r ==> _`
        (qspecl_then [`H`, `INR ex`, `mid with gas_obs := []`, `r`] mp_tac) >>
      impl_tac >- metis_tac[] >> strip_tac >> gvs[]) >>
  strip_tac >>
  rename1 `gas_exempt_cert _ _ _ _ _ marks (err,ef) (callee,tf)` >>
  rewrite_tac[gas_outcome_def] >> qexists `marks` >> disj2_tac >> disj2_tac >>
  qexistsl [`err`,`ef`,`callee`,`tf`] >>
  rewrite_tac[ignore_bind_def,bind_assoc] >>
  irule gas_exempt_cert_error_place >> simp[]
QED

Theorem tuple_place_head_gas_obs[simp]:
  tuple_place_head ctx func cenv cx st0 (es with gas_obs := gs)
    lo cs tys ltys ltvs vs elems w i s =
  tuple_place_head ctx func cenv cx st0 es lo cs tys ltys ltvs vs elems w i s
Proof
  `!regions : (bool # bytes32 # type_value) list.
     storage_well_formed_on cx (es with gas_obs := gs) regions <=>
             storage_well_formed_on cx es regions` by
    (gen_tac >> irule vyperStorageFootprintTheory.storage_well_formed_on_backends >>
     simp[]) >>
  simp[tuplePlaceHeadTheory.tuple_place_head_def,
       tuplePlacePrefixCertTheory.tuple_place_snapshot_def] >>
  qpat_x_assum `!regions. _` (fn th => rewrite_tac[th])
QED

Theorem tuple_place_target_post_gas_obs[simp]:
  (target_post H ctx func cenv cx (es with gas_obs := gs) sa sb s0 ee pv vt r s =
   target_post H ctx func cenv cx es sa sb s0 ee pv vt r s) /\
  (target_post H ctx func cenv cx es sa sb s0 (ee with gas_obs := hs) pv vt r s =
   target_post H ctx func cenv cx es sa sb s0 ee pv vt r s)
Proof
  `storage_well_formed_on cx (ee with gas_obs := hs) (FST H) <=>
   storage_well_formed_on cx ee (FST H)` by
    (irule vyperStorageFootprintTheory.storage_well_formed_on_backends >> simp[]) >>
  simp[loweringPostsTheory.target_post_def, loweringPostsTheory.locals_kept_def,
       loweringPostsTheory.popped_kept_def]
QED

Theorem tuple_place_write_gas_exit:
  write_place cx p v es = (INR ex,ff) /\
  gas_marked_path F ctx func s 0 r /\ exit_result r /\
  expr_exit (INR ex) r ==>
  gas_outcome F tops (ctx,func) cx st0 (ignore_bind (write_place cx p v) next)
    (es,s) Q (\H res ee r. expr_exit res r)
Proof
  strip_tac >>
  rewrite_tac[gas_outcome_def] >> qexists `[]` >> disj2_tac >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >> qexistsl [`INR ex`,`ff`,`r`] >>
  simp[gas_marked_exec_def] >> rpt strip_tac >>
  drule tuple_place_write_gas_obs >> disch_then (qspec_then `tail` assume_tac) >>
  simp[ignore_bind_def, bind_def] >>
  Cases_on `r` >> Cases_on `ex` >>
  gvs[exprSimDefsTheory.expr_exit_def] >>
  rename1 `Error err` >> Cases_on `err` >>
  gvs[exprSimDefsTheory.expr_exit_def]
QED

Theorem tuple_place_write_gas_prefix:
  write_place cx p v es = (INL (),ff) /\
  gas_marked_path F ctx func s 0 (OK t) /\
  gas_outcome F tops (ctx,func) cx st0 next (ff with gas_obs := [],t) Q R ==>
  gas_outcome F tops (ctx,func) cx st0 (ignore_bind (write_place cx p v) next)
    (es,s) Q R
Proof
  strip_tac >>
  `gas_marked_exec F (ctx,func) (write_place cx p v)
    (es,s) [] (INL ()) ff (OK t)` by
    (simp[gas_marked_exec_def] >> rpt strip_tac >>
     drule tuple_place_write_gas_obs >> simp[]) >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def] >>
  disch_then (qx_choose_then `right` (DISJ_CASES_THEN mp_tac))
  >- (strip_tac >> qexists `[] ++ right` >> disj1_tac >>
      rewrite_tac[ignore_bind_def] >>
      irule gasStorageTheory.gas_bad_storage_at_bind_right >>
      (metis_tac[])) >>
  disch_then (DISJ_CASES_THEN mp_tac)
  >- (rewrite_tac[gas_summary_at_def] >>
      disch_then (qx_choose_then `out` (qx_choose_then `fin`
        (qx_choose_then `r` (CONJUNCTS_THEN2 assume_tac assume_tac)))) >>
      qexists `[] ++ right` >> disj2_tac >> disj1_tac >>
      rewrite_tac[gas_summary_at_def] >>
      qexistsl [`out`,`fin`,`r`] >>
      conj_tac >- (rewrite_tac[ignore_bind_def] >>
                    irule gas_marked_exec_bind_normal >>
                    qexistsl [`ff`,`t`,`()`] >> simp[]) >>
      first_assum ACCEPT_TAC) >>
  strip_tac >>
  rename1 `gas_exempt_cert _ _ _ _ _ right (err,ef) (callee,tf)` >>
  qexists `[] ++ right` >> disj2_tac >> disj2_tac >>
  qexistsl [`err`,`ef`,`callee`,`tf`] >>
  rewrite_tac[ignore_bind_def,bind_assoc] >>
  irule gas_exempt_cert_bind_unit >>
  qexistsl [`ff`,`t`,`()`] >> simp[GSYM ignore_bind_def]
QED
