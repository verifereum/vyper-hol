(* Sequential source evaluation keeps one origin/memory/pointer witness.
   A horizon valid for the composed trace is valid for the left trace,
   since the right computation only appends storage observations. *)
Theory gasOutcomeFullCompose
Ancestors
  gasOutcomeFull fragGasOriginPtr fragGasOrigin gasOutcome gasExemptCert
  gasStorage gasSummaryCompose gasSummary fragGasPathPtr fragGasPathMem
  fragGasPath fragGasMode fragExec
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

(* The continuation sees the left run's own source equation and its post on
   every valid horizon of one endpoint.
   The certificate premises are the existing type-specific bind/error
   constructors, as in gas_outcome_ptr_bind. They do not add an oracle
   or execution premise to any source-language theorem. *)
Theorem gas_outcome_full_bind_all:
  gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0 source
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
          gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0
            (next v) (mid, t, G1, tn1) Q R) \/
     (?exc. res = INR exc /\
            !H. valid_horizon cx st0 H mid.storage_trace ==>
                Q H (INR exc) mid G1 tn1 t)) /\
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
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
         (s, G, tn) marks (r, G', tn') /\
       ((?t. r = OK t /\ Q1 H res (ee with gas_obs := []) G' tn' t) \/
        (exit_result r /\ ?exc. res = INR exc /\
           R H (INR exc) (ee with gas_obs := []) (G', tn') r))` by
    (rpt strip_tac >> res_tac >> fs[]) >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _ /\ _` (fn th =>
    assume_tac th >>
    qspec_then `storage_trace_horizon ee.storage_trace` mp_tac th) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  Cases_on `exit_result r`
  (* the left exits: the bind exits with it *)
  >- (strip_tac >> gvs[fragExecTheory.exit_result_def] >>
      rewrite_tac[gas_outcome_full_def] >> qexists_tac `marks` >>
      disj2_tac >> disj1_tac >>
      qexistsl_tac [`INR exc`, `ee`, `r`, `G'`, `tn'`] >>
      conj_tac >- (irule gas_source_bind_exception >> simp[]) >>
      rpt strip_tac >> res_tac >> gvs[fragExecTheory.exit_result_def]) >>
  strip_tac >> gvs[] >>
  (* the left continues normally: every horizon's post feeds next v *)
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       Q1 H res (ee with gas_obs := []) G' tn' t` by
    (rpt strip_tac >> res_tac >> fs[fragExecTheory.exit_result_def]) >>
  qpat_x_assum `!marks res mid G1 tn1 t. _ /\ _ /\ _ ==> _`
    (qspecl_then [`marks`, `res`, `ee with gas_obs := []`, `G'`, `tn'`, `t`]
       mp_tac) >>
  impl_tac >- fs[] >> reverse strip_tac >> gvs[]
  (* the left lands with an abrupt source result: so does the bind *)
  >- (rewrite_tac[gas_outcome_full_def] >> qexists_tac `marks` >>
      disj2_tac >> disj1_tac >>
      qexistsl_tac [`INR exc`, `ee`, `OK t`, `G'`, `tn'`] >>
      conj_tac >- (irule gas_source_bind_exception >> simp[]) >>
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
      qexistsl_tac [`res`, `ee'`, `r`, `G''`, `tn''`] >>
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

(* The usual bind: each horizon's left post already holds the continuation's
   outcome. *)
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
  strip_tac >> irule gas_outcome_full_bind_all >>
  qpat_assum `gas_outcome_full _ _ _ _ source _ _ _` (irule_at Any) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  BETA_TAC >> rpt strip_tac >> disj1_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  fs[storage_trace_domain_def]
QED

Theorem origin_ptr_path_zero_suffix[local]:
  gas_origin_ptr_path cx st marks (OK t, G1, tn1) /\
  gas_origin_ptr_path cx (t, G1, tn1) [] out ==>
  gas_origin_ptr_path cx st marks out
Proof
  PairCases_on `out` >> strip_tac >>
  qpat_x_assum `gas_origin_ptr_path _ _ marks _`
    (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
  simp[] >> disch_then drule >> simp[]
QED

(* A no-GAS step after the normal endpoint. The step's endpoint is chosen
   once, from the posts of every valid horizon, before the horizon. *)
Theorem gas_outcome_full_zero_suffix:
  gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0 source
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
  gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0 source
    (es, s, G, tn) Q' R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_def])
  >- (rewrite_tac[gas_outcome_full_def] >> qexists_tac `marks` >>
      disj1_tac >> first_assum ACCEPT_TAC)
  >~ [`gas_origin_ptr_focus _ _ _ _`]
  >- (rewrite_tac[gas_outcome_full_def] >> qexists_tac `marks` >>
      disj2_tac >> disj2_tac >> metis_tac[]) >>
  rewrite_tac[gas_outcome_full_def] >> qexists_tac `marks` >>
  Cases_on `storage_trace_domain cx st0 ee.storage_trace`
  >~ [`~storage_trace_domain _ _ _`]
  >- (disj1_tac >> irule gas_bad_storage_at_endpoint >> metis_tac[]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace)
     ee.storage_trace` by fs[storage_trace_domain_def] >>
  Cases_on `exit_result r`
  (* an exit keeps its endpoint and exit post *)
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`res`, `ee`, `r`, `G'`, `tn'`] >>
      conj_tac >- fs[] >>
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
  conj_tac >- fs[] >>
  rpt strip_tac >> res_tac >> fs[] >>
  metis_tac[origin_ptr_path_zero_suffix]
QED

Theorem gas_outcome_full_pure:
  (!tail. source (es with gas_obs := tail) = (res, ee with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
       (s, G, tn) [] (OK t, G', tn') /\
     Q H res (ee with gas_obs := []) G' tn' t) ==>
  gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0 source
    (es, s, G, tn) Q R
Proof
  strip_tac >> rewrite_tac[gas_outcome_full_def] >>
  qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`res`, `ee`, `OK t`, `G'`, `tn'`] >> simp[] >>
  rpt strip_tac >> res_tac >> fs[]
QED

(* gas_outcome_full_post_mono, with the source run that reached the
   normal post, its emptied observations, the end state's running flag
   and the post's horizon. *)
Theorem gas_outcome_full_exit:
  (!tail. source (es with gas_obs := tail) = (res, ee with gas_obs := tail)) /\
  exit_result r /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
       (s, G, tn) [] (r, G', tn') /\
     R H res (ee with gas_obs := []) (G', tn') r) ==>
  gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0 source
    (es, s, G, tn) Q R
Proof
  strip_tac >> rewrite_tac[gas_outcome_full_def] >>
  qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`res`, `ee`, `r`, `G'`, `tn'`] >> simp[] >>
  rpt strip_tac >> res_tac >> fs[]
QED

Theorem gas_outcome_full_post_source:
  gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0 source
    (es, s, G, tn) Q R /\
  (!H res ee G' tn' t.
     (?xs. !tail. source (es with gas_obs := xs ++ tail) =
                  (res, ee with gas_obs := tail)) /\
     ee.gas_obs = [] /\ ~t.vs_halted /\
     valid_horizon cx st0 H ee.storage_trace /\ Q H res ee G' tn' t ==>
     Q' H res ee G' tn' t) /\
  (!H res ee gt r. R H res ee gt r ==> R' H res ee gt r) ==>
  gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0 source
    (es, s, G, tn) Q' R'
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_def]) >>
  rewrite_tac[gas_outcome_full_def] >> qexists_tac `marks`
  >- (disj1_tac >> first_assum ACCEPT_TAC)
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`res`, `ee`, `r`, `G'`, `tn'`] >>
      conj_tac >- fs[] >>
      rpt strip_tac >> first_x_assum drule >> strip_tac >> gvs[]
      >- (disj1_tac >> first_x_assum irule >> simp[] >> rpt conj_tac
          >~ [`~t.vs_halted`]
          >- metis_tac[gas_origin_ptr_path_projections, gas_origin_path_erase,
                       gas_marked_path_exec, gas_path_normal] >>
          qexists_tac `gas_explicit marks s.vs_gas_readings` >> simp[]) >>
      disj2_tac >> metis_tac[]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

Theorem gas_outcome_full_zero_suffix_mono:
  gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0 source
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
  gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0 source
    (es, s, G, tn) Q' R'
Proof
  strip_tac >> drule_all gas_outcome_full_zero_suffix >> strip_tac >>
  drule gas_outcome_full_post_mono >> disch_then irule >>
  conj_tac >- simp[] >> first_assum ACCEPT_TAC
QED

(* Bind whose left run may also land normally on an abrupt source result,
   which is then the whole bind's normal post. *)
Theorem gas_outcome_full_bind_lands:
  gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0 source
    (es, s, G, tn)
    (\H res mid G1 tn1 t.
       (?v. res = INL v /\
          gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0
            (next v) (mid, t, G1, tn1) Q R) \/
       (?exc. res = INR exc /\ Q H (INR exc) mid G1 tn1 t))
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
  strip_tac >> irule gas_outcome_full_bind_all >>
  qpat_assum `gas_outcome_full _ _ _ _ source _ _ _` (irule_at Any) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  BETA_TAC >> rpt strip_tac >>
  Cases_on `res` >> gvs[] >>
  metis_tac[storage_trace_domain_def]
QED

(* A source run with its explicit-GAS observations and one joint path to a
   common endpoint, valid on every horizon of the final trace, is a full
   outcome. *)
Theorem gas_outcome_full_intro:
  (!tail.
     source (es with gas_obs :=
               gas_explicit marks s.vs_gas_readings ++ tail) =
       (res, ee with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
       (s, G, tn) marks (r, G', tn') /\
     ((?t. r = OK t /\ Q H res (ee with gas_obs := []) G' tn' t) \/
      (exit_result r /\ R H res (ee with gas_obs := []) (G', tn') r))) ==>
  gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0 source
    (es, s, G, tn) Q R
Proof
  strip_tac >> rewrite_tac[gas_outcome_full_def] >>
  qexists_tac `marks` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`res`, `ee`, `r`, `G'`, `tn'`] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

(* A leaf may assume its input trace has an intrinsic horizon: otherwise the
   empty-marks bad-storage arm holds, since a framed source keeps a bad
   prefix bad. *)
Theorem gas_outcome_full_initial_domain:
  storage_trace_frame source /\
  (storage_trace_domain cx st0 es.storage_trace ==>
   gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0 source
     (es, s, G, tn) Q R) ==>
  gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0 source
    (es, s, G, tn) Q R
Proof
  strip_tac >>
  Cases_on `storage_trace_domain cx st0 es.storage_trace` >- fs[] >>
  rewrite_tac[gas_outcome_full_def] >> qexists_tac `[]` >> disj1_tac >>
  rw[gas_bad_storage_at_def] >>
  Cases_on `source (es with gas_obs := tail)` >> simp[] >>
  `(es with gas_obs := tail).storage_trace = es.storage_trace` by simp[] >>
  metis_tac[storage_trace_frame_preserves_bad_domain]
QED
