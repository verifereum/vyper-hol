(* Sequential counted outcomes for a linked unit. The continuation uses
   the prefix's actual endpoint and the same horizon as the whole run. *)
Theory gasOutcomeFullBindMods
Ancestors
  gasOutcomeFullMods gasOutcomeFull gasExemptCertMods
  fragGasOriginPtr fragGasOrigin gasOutcome gasStorage gasSummaryCompose
  gasSummary fragGasPathPtr fragGasPathMem fragGasPath fragGasMode fragExec
  vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperState
  venomState list arithmetic

Theorem valid_horizon_frame_obs[local]:
  storage_trace_frame f /\
  f (ee with gas_obs := xs) = (res, ee2 with gas_obs := ys) /\
  valid_horizon cx st0 H ee2.storage_trace ==>
  valid_horizon cx st0 H ee.storage_trace
Proof
  rpt strip_tac >> drule_all storage_trace_frame_prefix >> simp[] >>
  strip_tac >> gvs[] >> metis_tac[valid_horizon_append]
QED

(* The two certificate premises select the bind and error rules for
   the source's result type; neither premise chooses a particular module. *)
Theorem gas_outcome_full_mods_bind_all:
  gas_outcome_full_mods (DF, lo, explicit, ctx, func, PG) mods cx st0 source
    (es, s, G, tn)
    Q1 (\H res ee gt r. ?exc. res = INR exc /\ R H (INR exc) ee gt r) /\
  (!marks res mid G1 tn1 t.
     (!tail. source (es with gas_obs :=
                       gas_explicit marks s.vs_gas_readings ++ tail) =
             (res, mid with gas_obs := tail)) /\
     storage_trace_domain cx st0 mid.storage_trace /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
          Q1 H res mid G1 tn1 t) ==>
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
  >~ [`gas_bad_storage_at _ _ source _ _ _`]
  >- (rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks` >>
      disj1_tac >> conj_tac
      >- (irule gas_bad_storage_at_bind_left >> simp[]) >>
      metis_tac[])
  >~ [`gas_origin_ptr_focus _ _ _ _`]
  >- (asm_rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks` >>
      disj2_tac >> disj2_tac >> metis_tac[]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace)
     ee.storage_trace` by fs[storage_trace_domain_def] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       valid_horizon cx st0 H es.storage_trace` by
    (qpat_assum `!tail. source _ = _`
       (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
     metis_tac[valid_horizon_frame_obs]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ ((?t. _) \/ _)`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  Cases_on `exit_result r`
  >- (strip_tac >> gvs[fragExecTheory.exit_result_def] >>
      rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks` >>
      disj2_tac >> disj1_tac >>
      qexistsl_tac [`INR exc`, `ee`, `r`, `G'`, `tn'`] >>
      conj_tac >- (irule gas_source_bind_exception >> simp[]) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      rpt strip_tac >> res_tac >> gvs[fragExecTheory.exit_result_def]) >>
  strip_tac >> gvs[] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       Q1 H res (ee with gas_obs := []) G' tn' t` by
    (rpt strip_tac >> res_tac >> fs[fragExecTheory.exit_result_def]) >>
  qpat_x_assum `!marks res mid G1 tn1 t. _ /\ _ /\ _ ==> _`
    (qspecl_then [`marks`, `res`, `ee with gas_obs := []`, `G'`, `tn'`, `t`]
       mp_tac) >>
  impl_tac >- fs[] >> reverse strip_tac >> gvs[]
  >- (rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks` >>
      disj2_tac >> disj1_tac >>
      qexistsl_tac [`INR exc`, `ee`, `OK t`, `G'`, `tn'`] >>
      conj_tac >- (irule gas_source_bind_exception >> simp[]) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      rpt strip_tac >> res_tac >> fs[]) >>
  suspend "right"
QED

Resume gas_outcome_full_mods_bind_all[right]:
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
  >~ [`gas_bad_storage_at _ _ (next v) _ _ _`]
  >- (rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks ++ marks'` >>
      disj1_tac >> conj_tac
      >- (irule gas_bad_storage_at_bind_right >> metis_tac[]) >>
      `valid_horizon cx st0 H ee.storage_trace` by fs[] >>
      qexistsl_tac [`H`, `leaf`, `leaf_pg`, `leaf_g`, `leaf_tn`, `finish'`] >>
      conj_tac >- metis_tac[] >>
      irule (cj 2 gas_origin_ptr_focus_rules) >> metis_tac[])
  >~ [`gas_origin_ptr_focus _ _ _ _`]
  >- (asm_rewrite_tac[gas_outcome_full_mods_def] >>
      qexists_tac `marks ++ marks'` >> disj2_tac >> disj2_tac >>
      qexistsl_tac [`err`, `ee'`, `leaf`, `leaf_pg`, `leaf_g`, `leaf_tn`,
                    `finish'`] >>
      conj_tac >- metis_tac[] >>
      `valid_horizon cx st0 H ee.storage_trace` by fs[] >>
      qexists_tac `H` >> conj_tac >- metis_tac[] >>
      irule (cj 2 gas_origin_ptr_focus_rules) >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H ee'.storage_trace ==>
       valid_horizon cx st0 H ee.storage_trace` by
    (qpat_assum `!tail. next v _ = _`
       (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
     metis_tac[valid_horizon_frame_obs]) >>
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

Finalise gas_outcome_full_mods_bind_all
