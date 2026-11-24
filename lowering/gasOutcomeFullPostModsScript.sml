(* Introductions and same-run post transformations for linked outcomes. *)
Theory gasOutcomeFullPostMods
Ancestors
  gasOutcomeFullMods gasOutcomeFull bodyFullShared gasStorage gasSummary
  fragGasOriginPtr fragGasOrigin fragGasMode fragGasPath fragExec
  bodyPtrDefs loweringPosts vyperStorageFootprint vyperState venomState

Theorem gas_outcome_full_mods_bad_nil:
  ~s.vs_halted /\
  (!tail. ~storage_trace_domain cx st0
            (SND (source (es with gas_obs := tail))).storage_trace) ==>
  gas_outcome_full_mods (DF, lo, explicit, ctx, func, PG) mods cx st0 source
    (es, s, G, tn) Q R
Proof
  strip_tac >> rewrite_tac[gas_outcome_full_mods_def] >>
  qexists_tac `[]` >> disj1_tac >> conj_tac
  >- simp[gas_bad_storage_at_def, gas_explicit_def] >>
  qexistsl_tac [`storage_trace_horizon es.storage_trace`, `func`, `PG`,
                `G`, `tn`, `s`] >>
  simp[gas_origin_ptr_focus_nil, storage_trace_domain_def]
QED

Theorem linked_outcome_nil_endpoint[local]:
  ~s.vs_halted /\
  (!tail. source (es with gas_obs := tail) = (res, ee with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
       (s, G, tn) [] (r, G', tn') /\
     ((?t. r = OK t /\ Q H res (ee with gas_obs := []) G' tn' t) \/
      (exit_result r /\ R H res (ee with gas_obs := []) (G', tn') r))) ==>
  gas_outcome_full_mods (DF, lo, explicit, ctx, func, PG) mods cx st0 source
    (es, s, G, tn) Q R
Proof
  strip_tac >> Cases_on `storage_trace_domain cx st0 ee.storage_trace`
  >- (rewrite_tac[gas_outcome_full_mods_def] >>
      qexists_tac `[]` >> disj2_tac >> disj1_tac >>
      qexistsl_tac [`res`, `ee`, `r`, `G'`, `tn'`] >>
      simp[gas_explicit_def]) >>
  irule gas_outcome_full_mods_bad_nil >> simp[]
QED

Theorem gas_outcome_full_mods_pure:
  ~s.vs_halted /\
  (!tail. source (es with gas_obs := tail) = (res, ee with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
       (s, G, tn) [] (OK t, G', tn') /\
     Q H res (ee with gas_obs := []) G' tn' t) ==>
  gas_outcome_full_mods (DF, lo, explicit, ctx, func, PG) mods cx st0 source
    (es, s, G, tn) Q R
Proof
  strip_tac >> irule linked_outcome_nil_endpoint >>
  (reverse conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`G'`, `ee`, `OK t`, `res`, `tn'`] >> simp[]
QED

Theorem gas_outcome_full_mods_exit:
  ~s.vs_halted /\
  (!tail. source (es with gas_obs := tail) = (res, ee with gas_obs := tail)) /\
  exit_result r /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
       (s, G, tn) [] (r, G', tn') /\
     R H res (ee with gas_obs := []) (G', tn') r) ==>
  gas_outcome_full_mods (DF, lo, explicit, ctx, func, PG) mods cx st0 source
    (es, s, G, tn) Q R
Proof
  strip_tac >> irule linked_outcome_nil_endpoint >>
  (reverse conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`G'`, `ee`, `r`, `res`, `tn'`] >> simp[]
QED

Theorem gas_outcome_full_mods_post_source:
  gas_outcome_full_mods (DF, lo, explicit, ctx, func, PG) mods cx st0 source
    (es, s, G, tn) Q R /\
  (!H res ee G' tn' t.
     (?xs. !tail. source (es with gas_obs := xs ++ tail) =
                  (res, ee with gas_obs := tail)) /\
     ee.gas_obs = [] /\ ~t.vs_halted /\
     valid_horizon cx st0 H ee.storage_trace /\ Q H res ee G' tn' t ==>
     Q' H res ee G' tn' t) /\
  (!H res ee gt r. R H res ee gt r ==> R' H res ee gt r) ==>
  gas_outcome_full_mods (DF, lo, explicit, ctx, func, PG) mods cx st0 source
    (es, s, G, tn) Q' R'
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_mods_def]) >>
  rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks`
  >- (disj1_tac >> metis_tac[])
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`res`, `ee`, `r`, `G'`, `tn'`] >>
      rpt conj_tac >- simp[] >- simp[] >>
      rpt strip_tac >> first_x_assum drule >> strip_tac >> gvs[]
      >- (disj1_tac >> first_x_assum irule >> simp[] >> conj_tac
          >- (qexists_tac `gas_explicit marks s.vs_gas_readings` >> simp[]) >>
          metis_tac[gas_origin_ptr_path_projections, gas_origin_path_erase,
                    gas_marked_path_exec, gas_path_normal]) >>
      disj2_tac >> metis_tac[]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

Theorem gas_outcome_full_mods_return_buf_allocas:
  gas_outcome_full_mods (DF, lo, explicit, ctx, func, PG) mods cx st0 source
    (es, s, G, tn) Q R /\
  return_buf_frame d cenv sa s /\ return_buf_sep d cenv es s ==>
  gas_outcome_full_mods (DF, lo, explicit, ctx, func, PG) mods cx st0 source
    (es, s, G, tn)
    (\H res ee G' tn' t.
      Q H res ee G' tn' t /\
      (!bw capacity. d = SOME (bw, capacity) ==>
         allocas_from (w2n bw + capacity) t)) R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_mods_def]) >>
  rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks`
  >- (disj1_tac >> metis_tac[])
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`res`, `ee`, `r`, `G'`, `tn'`] >>
      rpt conj_tac >- simp[] >- simp[] >>
      rpt strip_tac >> first_x_assum drule >> strip_tac >> gvs[] >>
      disj1_tac >> rpt strip_tac >>
      drule_all return_buf_allocas_path >> simp[]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED
