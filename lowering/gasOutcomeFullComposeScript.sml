(* Sequential source evaluation keeps one origin/memory/pointer witness.
   A horizon valid for the composed trace is valid for the left trace,
   since the right computation only appends storage observations. *)
Theory gasOutcomeFullCompose
Ancestors
  gasOutcomeFull fragGasOriginPtr fragGasOrigin gasOutcome gasExemptCert
  gasStorage gasSummaryCompose gasSummary fragGasPathPtr fragGasMode
  vyperStorageTrace vyperStorageFootprint
  vyperInterpreter vyperState venomState list arithmetic

(* The right computation only appends storage observations, so a horizon
   valid at its end is valid where it started. *)
Theorem valid_horizon_frame_obs[local]:
  storage_trace_frame f /\
  f (ee with gas_obs := xs) = (res, ee2 with gas_obs := ys) /\
  valid_horizon cx st0 H ee2.storage_trace ==>
  valid_horizon cx st0 H ee.storage_trace
Proof
  rpt strip_tac >> drule_all storage_trace_frame_prefix >> simp[] >>
  strip_tac >> gvs[] >> metis_tac[valid_horizon_append]
QED

(* The certificate premises are the existing type-specific bind/error
   constructors, as in gas_outcome_ptr_bind. They do not add an oracle
   or execution premise to any source-language theorem. *)
Theorem gas_outcome_full_bind:
  gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0 source
    (es, s, G, tn)
    (\H res mid G1 tn1 t. ?v. res = INL v /\
       gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0 (next v)
         (mid, t, G1, tn1) Q R)
    (\H res ee gt r. ?exc. res = INR exc /\ R H (INR exc) ee gt r) /\
  (!v. storage_trace_frame (next v)) /\
  (!marks err ee leaf stop_state.
     gas_exempt_cert T tops (ctx, func) (ignore_bind source (return ()))
       (es, s) marks (err, ee) (leaf, stop_state) ==>
     gas_exempt_cert T tops (ctx, func)
       (bind source (\v. ignore_bind (next v) (return ())))
       (es, s) marks (err, ee) (leaf, stop_state)) /\
  (!left v mid t right err ee leaf stop_state.
     gas_marked_exec T (ctx, func) source (es, s) left (INL v) mid (OK t) /\
     gas_exempt_cert T tops (ctx, func) (ignore_bind (next v) (return ()))
       (mid with gas_obs := [], t) right (err, ee) (leaf, stop_state) ==>
     gas_exempt_cert T tops (ctx, func)
       (bind source (\v. ignore_bind (next v) (return ())))
       (es, s) (left ++ right) (err, ee) (leaf, stop_state)) ==>
  gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0
    (bind source next) (es, s, G, tn) Q R
Proof
  strip_tac >>
  `ignore_bind (bind source next) (return ()) =
     bind source (\v. ignore_bind (next v) (return ()))` by
    simp[ignore_bind_def, bind_assoc] >>
  qpat_x_assum `gas_outcome_full _ _ _ _ source _ _ _`
    (strip_assume_tac o BETA_RULE o ONCE_REWRITE_RULE [gas_outcome_full_def])
  (* the left prefix already leaves the storage domain *)
  >- (rewrite_tac[gas_outcome_full_def] >> qexists_tac `marks` >>
      disj1_tac >> irule gas_bad_storage_at_bind_left >> simp[])
  (* the left exempt certificate covers the whole bind *)
  >~ [`gas_origin_ptr_focus _ _ _ _`]
  >- (asm_rewrite_tac[gas_outcome_full_def] >> qexists_tac `marks` >>
      disj2_tac >> disj2_tac >> metis_tac[]) >>
  (* the left endpoint *)
  Cases_on `storage_trace_domain cx st0 ee.storage_trace`
  >~ [`~storage_trace_domain _ _ _`]
  >- (rewrite_tac[gas_outcome_full_def] >> qexists_tac `marks` >>
      disj1_tac >> irule gas_bad_storage_at_bind_left >> simp[] >>
      irule gas_bad_storage_at_endpoint >> metis_tac[]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace)
     ee.storage_trace` by fs[storage_trace_domain_def] >>
  first_assum (drule_then strip_assume_tac) >> gvs[]
  (* the left exits: the bind exits with it *)
  >~ [`exit_result r`]
  >- (rewrite_tac[gas_outcome_full_def] >> qexists_tac `marks` >>
      disj2_tac >> disj1_tac >>
      qexistsl_tac [`INR exc`, `ee`, `r`, `G'`, `tn'`] >>
      conj_tac >- (irule gas_source_bind_exception >> simp[]) >>
      rpt strip_tac >> first_x_assum drule >> strip_tac >> gvs[]) >>
  (* the left continues normally into next v *)
  rename1 `gas_outcome_full _ _ _ _ (next v) (ee with gas_obs := [], t, G1, tn1) Q R` >>
  `gas_marked_exec T (ctx, func) source (es, s) marks (INL v) ee (OK t)` by
    (rewrite_tac[gas_marked_exec_def] >>
     metis_tac[gas_origin_ptr_path_projections, gas_origin_path_erase]) >>
  `gas_path ctx func s (LENGTH marks) (OK t)` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     metis_tac[gas_marked_path_exec]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
         (s, G, tn) marks (OK t, G1, tn1)` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ (next v) _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_def])
  (* the right prefix leaves the storage domain *)
  >- (rewrite_tac[gas_outcome_full_def] >> qexists_tac `marks ++ marks'` >>
      disj1_tac >> irule gas_bad_storage_at_bind_right >> metis_tac[])
  (* the right endpoint *)
  >- (`!H. valid_horizon cx st0 H ee'.storage_trace ==>
           valid_horizon cx st0 H ee.storage_trace` by
        (qpat_x_assum `!tail. next v _ = _`
           (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
         metis_tac[valid_horizon_frame_obs]) >>
      drule gas_explicit_append_path >>
      disch_then (qspec_then `marks'` assume_tac) >>
      rewrite_tac[gas_outcome_full_def] >>
      qexists_tac `marks ++ marks'` >> disj2_tac >> disj1_tac >>
      qexistsl_tac [`res`, `ee'`, `r`, `G'`, `tn'`] >>
      conj_tac
      >- (asm_rewrite_tac[] >> irule gas_source_bind_normal >> simp[] >>
          qexistsl_tac [`ee`, `v`] >> fs[]) >>
      rpt strip_tac >> res_tac >> simp[] >>
      irule gas_origin_ptr_path_append >> metis_tac[]) >>
  (* the right exempt certificate *)
  `!H. valid_horizon cx st0 H ee'.storage_trace ==>
       valid_horizon cx st0 H ee.storage_trace` by
    (qpat_assum `gas_exempt_cert T _ _ (ignore_bind (next v) _) _ _ _ _`
       (strip_assume_tac o MATCH_MP gas_exempt_cert_execution) >>
     qpat_x_assum `!tail. ignore_bind (next v) _ _ = _`
       (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
     `storage_trace_frame (ignore_bind (next v) (return ()))` by
       simp[storage_trace_frame_ignore_bind, storage_trace_frame_return] >>
     metis_tac[valid_horizon_frame_obs]) >>
  asm_rewrite_tac[gas_outcome_full_def] >>
  qexists_tac `marks ++ marks'` >> disj2_tac >> disj2_tac >>
  qexistsl_tac [`err`, `ee'`, `leaf`, `leaf_pg`, `leaf_g`, `leaf_tn`, `finish'`] >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >> res_tac >>
  irule (cj 2 gas_origin_ptr_focus_rules) >> metis_tac[]
QED
