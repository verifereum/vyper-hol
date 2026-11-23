Theory linkedDefaultOutcomeBind
Ancestors
  gasOutcomeFullMods gasExemptCertMods gasStorage gasSummary fragGasOriginPtr fragGasOrigin fragGasMode gasOutcomeFull
  gasSummaryCompose vyperStorageTrace vyperStorageFootprint vyperState

Theorem gas_outcome_full_bind_all_path_mods:
  gas_outcome_full_mods (DF, lo, explicit, ctx, func, PG) mods cx st0 source
    (es, s, G, tn)
    Q1 (\H res ee gt r. ?exc. res = INR exc /\ R H (INR exc) ee gt r) /\
  (!marks res mid G1 tn1 t.
     (!tail. source (es with gas_obs :=
                       gas_explicit marks s.vs_gas_readings ++ tail) =
             (res, mid with gas_obs := tail)) /\
     storage_trace_domain cx st0 mid.storage_trace /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
          Q1 H res mid G1 tn1 t) /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
          gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
            (s, G, tn) marks (OK t, G1, tn1)) ==>
     (?v. res = INL v /\
          gas_outcome_full_mods (DF, lo, explicit, ctx, func, PG) mods cx st0
            (next v) (mid, t, G1, tn1) Q R) \/
     (?exc. res = INR exc /\
            !H. valid_horizon cx st0 H mid.storage_trace ==>
                Q H (INR exc) mid G1 tn1 t)) /\
  storage_trace_frame source /\
  (!v. storage_trace_frame (next v)) /\
  (!marks err ee leaf stop_state.
     gas_exempt_cert_mods T mods (ctx, func) (ignore_bind source (return ()))
       (es, s) marks (err, ee) (leaf, stop_state) ==>
     gas_exempt_cert_mods T mods (ctx, func)
       (bind source (\v. ignore_bind (next v) (return ())))
       (es, s) marks (err, ee) (leaf, stop_state)) /\
  (!left v mid t right err ee leaf stop_state.
     gas_marked_exec T (ctx, func) source (es, s) left (INL v) mid (OK t) /\
     gas_exempt_cert_mods T mods (ctx, func) (ignore_bind (next v) (return ()))
       (mid with gas_obs := [], t) right (err, ee) (leaf, stop_state) ==>
     gas_exempt_cert_mods T mods (ctx, func)
       (bind source (\v. ignore_bind (next v) (return ())))
       (es, s) (left ++ right) (err, ee) (leaf, stop_state)) ==>
  gas_outcome_full_mods (DF, lo, explicit, ctx, func, PG) mods cx st0
    (bind source next) (es, s, G, tn) Q R
Proof
  strip_tac >>
  `ignore_bind (bind source next) (return ()) =
     bind source (\v. ignore_bind (next v) (return ()))` by
    simp[ignore_bind_def, bind_assoc] >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ source _ _ _`
    (strip_assume_tac o BETA_RULE o ONCE_REWRITE_RULE [gas_outcome_full_mods_def])
  (* the left prefix already leaves the storage domain *)
  >~ [`gas_bad_storage_at _ _ source _ _ _`]
  >- (rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks` >>
      disj1_tac >> conj_tac
      >- (irule gas_bad_storage_at_bind_left >> simp[]) >>
      metis_tac[])
  (* the left exempt certificate covers the whole bind *)
  >~ [`gas_origin_ptr_focus _ _ _ _`]
  >- (asm_rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks` >>
      disj2_tac >> disj2_tac >> metis_tac[]) >>
  (* the left endpoint *)
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace)
     ee.storage_trace` by fs[storage_trace_domain_def] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       valid_horizon cx st0 H es.storage_trace` by
    (gen_tac >> strip_tac >>
     qpat_assum `!tail. source _ = _`
       (qspec_then `[]` (mp_then (Pos last) mp_tac storage_trace_frame_prefix)) >>
     impl_tac >- FIRST_ASSUM ACCEPT_TAC >> simp[] >> strip_tac >>
     qpat_assum `ee.storage_trace = es.storage_trace ++ _` (fn trace =>
       qpat_assum `valid_horizon cx st0 H ee.storage_trace`
         (ACCEPT_TAC o MATCH_MP valid_horizon_append o REWRITE_RULE [trace]))) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
         (s, G, tn) marks (r, G', tn') /\
       ((?t. r = OK t /\ Q1 H res (ee with gas_obs := []) G' tn' t) \/
        (exit_result r /\ ?exc. res = INR exc /\
           R H (INR exc) (ee with gas_obs := []) (G', tn') r))` by
    (rpt strip_tac >> res_tac >> fs[]) >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _ /\ ((?t. _) \/ _)`
    (fn th => assume_tac th >>
     qspec_then `storage_trace_horizon ee.storage_trace` mp_tac th) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  Cases_on `exit_result r`
  (* the left exits: the bind exits with it *)
  >- (strip_tac >> gvs[fragExecTheory.exit_result_def] >>
      rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks` >>
      disj2_tac >> disj1_tac >>
      qexistsl_tac [`INR exc`, `ee`, `r`, `G'`, `tn'`] >>
      conj_tac >- (irule gas_source_bind_exception >> simp[]) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      rpt strip_tac >> res_tac >> gvs[fragExecTheory.exit_result_def]) >>
  strip_tac >> gvs[] >>
  (* the left continues normally: every horizon's post feeds next v *)
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       Q1 H res (ee with gas_obs := []) G' tn' t` by
    (rpt strip_tac >> res_tac >> fs[fragExecTheory.exit_result_def]) >>
  qpat_x_assum `!marks res mid G1 tn1 t. _ /\ _ /\ _ ==> _`
    (qspecl_then [`marks`, `res`, `ee with gas_obs := []`, `G'`, `tn'`, `t`]
       mp_tac) >>
  impl_tac >- (fs[] >> rpt strip_tac >> res_tac >> fs[]) >>
  reverse strip_tac >> gvs[]
  (* the left lands with an abrupt source result: so does the bind *)
  >- (rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks` >>
      disj2_tac >> disj1_tac >>
      qexistsl_tac [`INR exc`, `ee`, `OK t`, `G'`, `tn'`] >>
      conj_tac >- (irule gas_source_bind_exception >> simp[]) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      rpt strip_tac >> res_tac >> fs[]) >>
  `gas_marked_exec T (ctx, func) source (es, s) marks (INL v) ee (OK t)` by
    (rewrite_tac[gas_marked_exec_def] >>
     metis_tac[gas_origin_ptr_path_projections, gas_origin_path_erase]) >>
  `gas_path ctx func s (LENGTH marks) (OK t)` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     metis_tac[gas_marked_path_exec]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
         (s, G, tn) marks (OK t, G', tn')` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ (next v) _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_mods_def])
  (* the right prefix leaves the storage domain *)
  >~ [`gas_bad_storage_at _ _ (next v) _ _ _`]
  >- (rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks ++ marks'` >>
      disj1_tac >> conj_tac
      >- (irule gas_bad_storage_at_bind_right >> metis_tac[]) >>
      `valid_horizon cx st0 H ee.storage_trace` by fs[] >>
      qexistsl_tac [`H`, `leaf`, `leaf_pg`, `leaf_g`, `leaf_tn`, `finish'`] >>
      conj_tac >- metis_tac[] >>
      irule (cj 2 gas_origin_ptr_focus_rules) >> metis_tac[])
  (* the right exempt certificate *)
  >~ [`gas_origin_ptr_focus _ _ _ _`]
  >- (asm_rewrite_tac[gas_outcome_full_mods_def] >>
      qexists_tac `marks ++ marks'` >> disj2_tac >> disj2_tac >>
      qexistsl_tac [`err`, `ee'`, `leaf`, `leaf_pg`, `leaf_g`, `leaf_tn`,
                    `finish'`] >>
      conj_tac >- metis_tac[] >>
      `valid_horizon cx st0 H ee.storage_trace` by fs[] >>
      qexists_tac `H` >> conj_tac >- metis_tac[] >>
      irule (cj 2 gas_origin_ptr_focus_rules) >> metis_tac[]) >>
  (* the right endpoint *)
  `!H. valid_horizon cx st0 H ee'.storage_trace ==>
       valid_horizon cx st0 H ee.storage_trace` by
    (gen_tac >> strip_tac >>
     qpat_assum `!tail. next v _ = _`
       (qspec_then `[]` (mp_then (Pos last) mp_tac storage_trace_frame_prefix)) >>
     impl_tac >- (qpat_assum `!v. storage_trace_frame (next v)`
                     (qspec_then `v` ACCEPT_TAC)) >>
     simp[] >> strip_tac >>
     qpat_assum `ee'.storage_trace = ee.storage_trace ++ _` (fn trace =>
       qpat_assum `valid_horizon cx st0 H ee'.storage_trace`
         (ACCEPT_TAC o MATCH_MP valid_horizon_append o REWRITE_RULE [trace]))) >>
  drule gas_explicit_append_path >>
  disch_then (qspec_then `marks'` assume_tac) >>
  rewrite_tac[gas_outcome_full_mods_def] >>
  qexists_tac `marks ++ marks'` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`res`, `ee'`, `r`, `G''`, `tn''`] >>
  conj_tac
  >- (asm_rewrite_tac[] >> irule gas_source_bind_normal >> simp[] >>
      qexistsl_tac [`ee`, `v`] >> fs[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >> res_tac >> simp[] >>
  irule gas_origin_ptr_path_append >> metis_tac[]
QED
