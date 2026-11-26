Theory gasOutcomeFullBindPathMods
Ancestors
  gasOutcomeFullMods gasExemptCertMods
  fragGasOriginPtr fragGasOrigin gasOutcome gasStorage gasSummaryCompose
  gasSummary fragGasPathPtr fragGasPathMem fragGasPath fragGasMode fragExec
  vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperState
  venomState list arithmetic

(* The continuation sees the same prefix marks in the source observation
   and in the origin path, at every horizon valid for the intermediate trace. *)
Theorem gas_outcome_full_mods_bind_all_path:
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
  suspend "prefix"
QED

Resume gas_outcome_full_mods_bind_all_path[prefix]:
  strip_tac >> gvs[] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
         (s, G, tn) marks (OK t, G', tn') /\
       Q1 H res (ee with gas_obs := []) G' tn' t` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
       drule >> simp[fragExecTheory.exit_result_def]) >>
  qpat_x_assum `!marks res mid G1 tn1 t. _ /\ _ /\ _ /\ _ ==> _`
    (qspecl_then [`marks`, `res`, `ee with gas_obs := []`, `G'`, `tn'`, `t`]
       mp_tac) >>
  impl_tac >- (simp[] >> rpt strip_tac >> res_tac) >>
  reverse strip_tac >> gvs[]
  >- (rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks` >>
      disj2_tac >> disj1_tac >>
      qexistsl_tac [`INR exc`, `ee`, `OK t`, `G'`, `tn'`] >>
      conj_tac >- (irule gas_source_bind_exception >> simp[]) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      rpt strip_tac >> res_tac >> fs[]) >>
  suspend "suffix"
QED

Resume gas_outcome_full_mods_bind_all_path[suffix]:
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       valid_horizon cx st0 H es.storage_trace` by
    (rpt strip_tac >>
     qpat_assum `!tail. source _ = _`
       (qspec_then `[]` (mp_then (Pat `f st = (res,st')`) mp_tac
          valid_horizon_frame)) >>
     simp[]) >>
  `gas_marked_exec T (ctx, func) source (es, s) marks (INL v) ee (OK t)` by
    (rewrite_tac[gas_marked_exec_def] >>
     metis_tac[gas_origin_ptr_path_projections, gas_origin_path_erase]) >>
  `gas_path ctx func s (LENGTH marks) (OK t)` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     metis_tac[gas_marked_path_exec]) >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ (next v) _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_mods_def])
  >~ [`gas_bad_storage_at _ _ (next v) _ _ _`]
  >- (rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks ++ marks'` >>
      disj1_tac >> conj_tac
      >- (irule gas_bad_storage_at_bind_right >> metis_tac[]) >>
      suspend "bad_suffix")
  >~ [`gas_origin_ptr_focus _ _ _ _`]
  >- suspend "exempt_suffix" >>
  `!H. valid_horizon cx st0 H ee'.storage_trace ==>
       valid_horizon cx st0 H ee.storage_trace` by
    (rpt strip_tac >>
     qpat_assum `!tail. next v _ = _`
       (qspec_then `[]` (mp_then (Pat `f st = (res,st')`) mp_tac
          valid_horizon_frame)) >>
     simp[]) >>
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

Resume gas_outcome_full_mods_bind_all_path[bad_suffix]:
  `valid_horizon cx st0 H ee.storage_trace` by fs[] >>
  qexistsl_tac [`H`, `leaf`, `leaf_pg`, `leaf_g`, `leaf_tn`, `finish'`] >>
  conj_tac >- metis_tac[] >>
  irule (cj 2 gas_origin_ptr_focus_rules) >> metis_tac[]
QED

Resume gas_outcome_full_mods_bind_all_path[exempt_suffix]:
  asm_rewrite_tac[gas_outcome_full_mods_def] >>
  qexists_tac `marks ++ marks'` >> disj2_tac >> disj2_tac >>
  qexistsl_tac [`err`, `ee'`, `leaf`, `leaf_pg`, `leaf_g`, `leaf_tn`, `finish'`] >>
  conj_tac >- metis_tac[] >>
  `valid_horizon cx st0 H ee.storage_trace` by fs[] >>
  qexists_tac `H` >> conj_tac >- metis_tac[] >>
  irule (cj 2 gas_origin_ptr_focus_rules) >> metis_tac[]
QED

Finalise gas_outcome_full_mods_bind_all_path
