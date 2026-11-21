(* Route P uses the left outcome's control flow and the companion's sites. *)
Theory s1PrefixCompose
Ancestors
  s1PrefixDefs s1PrefixProps s1PrefixFrame
  bodyFullExtCallPackingReady gasOutcomeFull gasExemptCert
  gasStorage gasSummary gasSummaryCompose fragGasOriginPtr fragGasOrigin
  fragGasMode fragGasPath fragGasPathMem fragExec
  vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperState venomState
  list rich_list arithmetic sum pair

Triviality request_site_prepend_path:
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn)
    marks (OK t,G1,tn1) /\
  request_site (D,lo,explicit,ctx,func,PG) cx H (t,G1,tn1)
    k rq outcome ==>
  request_site (D,lo,explicit,ctx,func,PG) cx H (s,G,tn) k rq outcome
Proof
  rewrite_tac[request_site_def] >> strip_tac >>
  qexistsl_tac [`marks ++ left`, `leaf`, `leaf_pg`, `G'`, `tn'`,
    `t'`, `inst`, `fuel`, `t''`] >>
  simp[] >> irule (cj 2 gas_origin_ptr_focus_rules) >> metis_tac[]
QED

(* The outcome at a split is either in the completed left trace or in
   the appended suffix of the right trace. *)
Triviality bind_trace_outcome_split:
  left ++ suffix = obs_pre ++ StorageOutcome rq outcome :: rest ==>
  (?tail. left = obs_pre ++ StorageOutcome rq outcome :: tail) \/
  ?prefix. obs_pre = left ++ prefix /\
    suffix = prefix ++ StorageOutcome rq outcome :: rest
Proof
  simp[APPEND_EQ_APPEND] >> strip_tac >> simp[] >>
  Cases_on `l` >> gvs[] >> metis_tac[]
QED

(* A fixed left run agrees on its trace at the longer of its own marks
   and the left companion's marks. *)
Triviality left_site_at_fixed_trace:
  (!tail. source (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
    (res,mid with gas_obs := tail)) /\
  (!tail res ee obs_pre rq outcome sfx H.
    LENGTH es.requests = recorded_outcomes_count es.storage_trace /\
    source (es with gas_obs := gas_explicit left_marks s.vs_gas_readings ++ tail) =
      (res,ee) /\
    ee.storage_trace = obs_pre ++ StorageOutcome rq outcome :: sfx /\
    LENGTH es.storage_trace <= LENGTH obs_pre /\
    valid_horizon cx st0 H obs_pre /\ ~computed_precompile rq ==>
    request_site (DF H,lo,explicit,ctx,func,PG) cx H (s,G,tn)
      (recorded_outcomes_count obs_pre) rq outcome) ==>
  !obs_pre rq outcome sfx H.
    (isPREFIX marks left_marks \/ isPREFIX left_marks marks) /\
    LENGTH es.requests = recorded_outcomes_count es.storage_trace /\
    mid.storage_trace = obs_pre ++ StorageOutcome rq outcome :: sfx /\
    LENGTH es.storage_trace <= LENGTH obs_pre /\
    valid_horizon cx st0 H obs_pre /\ ~computed_precompile rq ==>
    request_site (DF H,lo,explicit,ctx,func,PG) cx H (s,G,tn)
      (recorded_outcomes_count obs_pre) rq outcome
Proof
  strip_tac >> rpt gen_tac >> strip_tac >> gvs[IS_PREFIX_APPEND]
  >- (qpat_x_assum `!tail. source _ = _` (qspec_then
        `gas_explicit l (DROP (LENGTH marks) s.vs_gas_readings) ++ []` assume_tac) >>
      qpat_x_assum `!tail ans ee pre request observed rest H. _`
        (qspecl_then [`[]`, `res`,
          `mid with gas_obs := gas_explicit l (DROP (LENGTH marks) s.vs_gas_readings) ++ []`,
          `obs_pre`, `rq`, `outcome`, `sfx`, `H`] mp_tac) >>
      PURE_REWRITE_TAC[gas_explicit_append, GSYM APPEND_ASSOC] >> simp[]) >>
  qpat_x_assum `!tail. source _ = _` (qspec_then `[]` mp_tac) >>
  PURE_REWRITE_TAC[gas_explicit_append, GSYM APPEND_ASSOC] >> strip_tac >>
  qpat_x_assum `!tail ans ee pre request observed rest H. _`
    (qspecl_then [`gas_explicit l (DROP (LENGTH left_marks) s.vs_gas_readings) ++ []`,
      `res`, `mid with gas_obs := []`, `obs_pre`, `rq`, `outcome`, `sfx`, `H`] mp_tac) >>
  simp[]
QED

fun left_site_at_fixed_trace_tac run_pattern suffix horizon =
  qpat_assum run_pattern (fn run =>
    qpat_assum `!tail res ee obs_pre rq outcome sfx H. _` (fn claims =>
      let
        val normalise = SIMP_RULE (srw_ss()) []
        val premises = CONJ (normalise run) (normalise claims)
      in
        qspecl_then [`obs_pre`,`rq`,`outcome`,suffix,horizon] mp_tac
          (MATCH_MP (normalise left_site_at_fixed_trace) premises)
      end))

Triviality bind_outcome_in_left:
  bind source next st = (res,ee) /\
  source st = (ans,mid) /\
  (!v. storage_trace_frame (next v)) /\
  ee.storage_trace = obs_pre ++ StorageOutcome rq outcome :: sfx /\
  (ISR ans \/ ~storage_trace_domain cx st0 mid.storage_trace) /\
  valid_horizon cx st0 H obs_pre ==>
  ?left_sfx. mid.storage_trace = obs_pre ++ StorageOutcome rq outcome :: left_sfx
Proof
  Cases_on `ans` >> rw[bind_def] >> gvs[] >>
  `storage_trace_frame (next x)` by simp[] >>
  drule_all storage_trace_frame_prefix >> strip_tac >>
  `mid.storage_trace ++ observations = obs_pre ++ StorageOutcome rq outcome :: sfx` by
    fs[] >>
  drule bind_trace_outcome_split >> strip_tac >> simp[] >>
  gvs[] >> metis_tac[valid_horizon_append, extcall_packing_observed_domain]
QED

Triviality bind_bad_trace_site:
  gas_bad_storage_at cx st0 source es s marks /\
  (!v. storage_trace_frame (next v)) /\
  (!tail res ee obs_pre rq outcome sfx H.
    LENGTH es.requests = recorded_outcomes_count es.storage_trace /\
    source (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (res,ee) /\
    ee.storage_trace = obs_pre ++ StorageOutcome rq outcome :: sfx /\
    LENGTH es.storage_trace <= LENGTH obs_pre /\
    valid_horizon cx st0 H obs_pre /\ ~computed_precompile rq ==>
    request_site (DF H,lo,explicit,ctx,func,PG) cx H (s,G,tn)
      (recorded_outcomes_count obs_pre) rq outcome) ==>
  !tail res ee obs_pre rq outcome sfx H.
    LENGTH es.requests = recorded_outcomes_count es.storage_trace /\
    bind source next (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (res,ee) /\
    ee.storage_trace = obs_pre ++ StorageOutcome rq outcome :: sfx /\
    LENGTH es.storage_trace <= LENGTH obs_pre /\
    valid_horizon cx st0 H obs_pre /\ ~computed_precompile rq ==>
    request_site (DF H,lo,explicit,ctx,func,PG) cx H (s,G,tn)
      (recorded_outcomes_count obs_pre) rq outcome
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  qabbrev_tac `st = es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail` >>
  Cases_on `source st` >> rename1 `source st = (ans,mid)` >>
  `~storage_trace_domain cx st0 mid.storage_trace` by
    (qpat_x_assum `gas_bad_storage_at _ _ source _ _ marks`
       (qspec_then `tail` mp_tac o REWRITE_RULE[gas_bad_storage_at_def]) >>
     fs[Abbr `st`]) >>
  `?left_sfx. mid.storage_trace = obs_pre ++ StorageOutcome rq outcome :: left_sfx` by
    (qpat_assum `bind source next st = (res,ee)`
       (mp_then Any irule bind_outcome_in_left) >>
     rpt conj_tac
     >- first_assum ACCEPT_TAC
     >- (qexists_tac `sfx` >> first_assum ACCEPT_TAC) >>
     qexistsl_tac [`H`, `ans`, `cx`, `st0`] >> simp[]) >>
  qpat_x_assum `!tail res ee obs_pre rq outcome sfx H. _`
    (qspecl_then [`tail`,`ans`,`mid`,`obs_pre`,`rq`,`outcome`,`left_sfx`,`H`] mp_tac) >>
  fs[Abbr `st`]
QED

fun bind_bad_trace_site_tac bad_pattern =
  qpat_assum bad_pattern (fn bad =>
    qpat_assum `!v. storage_trace_frame (next v)` (fn frame =>
      qpat_assum `!tail res ee obs_pre rq outcome sfx H. _` (fn claims =>
        let
          val normalise = SIMP_RULE (srw_ss()) []
          val premises = LIST_CONJ [bad,frame,normalise claims]
          val sites = MATCH_MP (normalise bind_bad_trace_site) premises
        in
          simp[NoAsms] >> MATCH_ACCEPT_TAC sites
        end)))

Theorem gas_prefix_full_bind:
  gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0 source
    (es, s, G, tn) Q1 R1 /\
  (!H res ee gt r. R1 H res ee gt r ==> ISR res) /\
  gas_prefix_full (DF, lo, explicit, ctx, func, PG) cx st0 source (es, s, G, tn) /\
  (!marks v mid G1 tn1 t.
     (!tail. source (es with gas_obs :=
                       gas_explicit marks s.vs_gas_readings ++ tail) =
             (INL v, mid with gas_obs := tail)) /\
     storage_trace_domain cx st0 mid.storage_trace /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==> Q1 H (INL v) mid G1 tn1 t) ==>
     gas_prefix_full (DF, lo, explicit, ctx, func, PG) cx st0 (next v) (mid, t, G1, tn1)) /\
  storage_trace_frame source /\ (!v. storage_trace_frame (next v)) /\
  requests_outcomes_frame source ==>
  gas_prefix_full (DF, lo, explicit, ctx, func, PG) cx st0 (bind source next) (es, s, G, tn)
Proof
  strip_tac >>
  qpat_x_assum `gas_prefix_full _ _ _ source _`
    (qx_choose_then `left_marks` strip_assume_tac o
     ONCE_REWRITE_RULE[gas_prefix_full_def]) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ source _ _ _`
    (qx_choose_then `marks` strip_assume_tac o
     ONCE_REWRITE_RULE[gas_outcome_full_def])
  >~ [`gas_bad_storage_at _ _ source _ _ _`]
  >- suspend "bad"
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- suspend "exempt"
  >> suspend "normal"
QED

Resume gas_prefix_full_bind[bad]:
  `isPREFIX marks left_marks \/ isPREFIX left_marks marks` by
    metis_tac[gas_origin_ptr_focus_marks_comparable] >>
  gvs[IS_PREFIX_APPEND] >>
  rewrite_tac[gas_prefix_full_def]
  >- (qexists_tac `marks ++ l` >> conj_tac
      >- metis_tac[] >>
      `gas_bad_storage_at cx st0 source es s (marks ++ l)` by
        (qpat_x_assum `gas_bad_storage_at _ _ source _ _ marks` mp_tac >>
         PURE_REWRITE_TAC[gas_bad_storage_at_def, gas_explicit_append, GSYM APPEND_ASSOC] >>
         metis_tac[]) >>
      bind_bad_trace_site_tac `gas_bad_storage_at _ _ source _ _ (marks ++ l)`) >>
  qexists_tac `left_marks ++ l` >> conj_tac
  >- metis_tac[] >>
  qpat_x_assum `!tail res ee obs_pre rq outcome sfx H. _` (fn claims =>
    let
      val (tail, body) = dest_forall (concl claims)
      val gas = ``gas_explicit left_marks s.vs_gas_readings ++ ^tail``
      val observations = genvar (type_of gas)
      val predicate = mk_abs (observations, subst [gas |-> observations] body)
      val extension =
        Q.SPECL [`^predicate`, `left_marks`, `s.vs_gas_readings`, `l`]
          gas_prefix_claims_extend
    in
      assume_tac (MATCH_MP (BETA_RULE extension) claims)
    end) >>
  bind_bad_trace_site_tac `gas_bad_storage_at _ _ source _ _ (left_marks ++ l)`
QED

Resume gas_prefix_full_bind[exempt]:
  drule gas_exempt_cert_execution >> strip_tac >>
  `!tail. source (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
    (INR (Error err),ee with gas_obs := tail)` by
    (gen_tac >> qpat_x_assum `!tail. ignore_bind source _ _ = _`
       (qspec_then `tail` assume_tac) >>
     Cases_on `source (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail)` >>
     rename1 `source _ = (ans,mid)` >> Cases_on `ans` >>
     gvs[ignore_bind_def, bind_def, return_def]) >>
  `isPREFIX marks left_marks \/ isPREFIX left_marks marks` by
    metis_tac[gas_origin_ptr_focus_marks_comparable] >>
  fs[IS_PREFIX_APPEND] >> rewrite_tac[gas_prefix_full_def]
  >- (qexists_tac `marks ++ l` >> conj_tac
      >- metis_tac[] >>
      PURE_REWRITE_TAC[gas_explicit_append, GSYM APPEND_ASSOC] >>
      rpt gen_tac >> strip_tac >>
      rename1 `valid_horizon cx st0 site_horizon obs_pre` >>
      `ee'.storage_trace = ee.storage_trace` by
        (qpat_assum `!tail. source _ = (INR (Error err),_)`
           (qspec_then `gas_explicit l (DROP (LENGTH marks) s.vs_gas_readings) ++ tail` assume_tac) >>
         gvs[bind_def]) >>
      left_site_at_fixed_trace_tac `!tail. source _ = (INR _,_)` `sfx` `site_horizon` >>
      fs[]) >>
  qexists_tac `left_marks ++ l` >> conj_tac
  >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  rename1 `valid_horizon cx st0 site_horizon obs_pre` >>
  `ee'.storage_trace = ee.storage_trace` by
    (qpat_assum `!tail. source _ = (INR (Error err),_)` (qspec_then `tail` assume_tac) >>
     gvs[bind_def]) >>
  left_site_at_fixed_trace_tac `!tail. source _ = (INR _,_)` `sfx` `site_horizon` >>
  fs[]
QED

Resume gas_prefix_full_bind[normal]:
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  `?appendix. ee.storage_trace = es.storage_trace ++ appendix` by
    (qpat_assum `!tail. source _ = _` (qspec_then `[]` assume_tac) >>
     drule_all storage_trace_frame_prefix >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> disch_then (CONJUNCTS_THEN ASSUME_TAC) >>
  `?exit_leaf exit_pg exit_g exit_tn exit_finish.
     gas_origin_ptr_focus (DF (storage_trace_horizon ee.storage_trace),
       lo,explicit,ctx,func,PG) (s,G,tn) marks (exit_leaf,exit_pg,exit_g,exit_tn,exit_finish)` by
    (drule gas_origin_ptr_path_focus >> metis_tac[]) >>
  Cases_on `res`
  >- suspend "success"
  >> suspend "error"
QED

Resume gas_prefix_full_bind[error]:
  rewrite_tac[gas_prefix_full_def] >> qexists_tac `marks` >> conj_tac
  >- (qexistsl_tac [`storage_trace_horizon ee.storage_trace`, `exit_leaf`, `exit_pg`,
      `exit_g`, `exit_tn`, `exit_finish`] >> simp[] >>
      metis_tac[valid_horizon_append]) >>
  rpt gen_tac >> strip_tac >>
  rename1 `valid_horizon cx st0 site_horizon obs_pre` >>
  `ee'.storage_trace = ee.storage_trace` by
    (qpat_assum `!tail. source _ = (INR _,_)` (qspec_then `tail` assume_tac) >> gvs[bind_def]) >>
  left_site_at_fixed_trace_tac `!tail. source _ = (INR _,_)` `sfx` `site_horizon` >>
  fs[] >> metis_tac[gas_origin_ptr_focus_marks_comparable]
QED

Resume gas_prefix_full_bind[success]:
  rename1 `source _ = (INL v,_)` >>
  `~exit_result r` by metis_tac[ISR, exit_result_def] >>
  qpat_x_assum `(?t. r = OK t /\ _) \/ _` strip_assume_tac >> gvs[] >>
  qabbrev_tac `mid = ee with gas_obs := []` >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn)
      marks (OK t,G',tn') /\ Q1 H (INL v) mid G' tn' t` by
    (qx_gen_tac `horizon` >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (qspec_then `horizon` mp_tac) >>
     impl_tac >- gvs[Abbr `mid`] >> simp[Abbr `mid`, exit_result_def]) >>
  qpat_x_assum `!marks v mid G1 tn1 t. _ ==> gas_prefix_full _ _ _ _ _`
    (qspecl_then [`marks`, `v`, `mid`, `G'`, `tn'`, `t`] mp_tac) >>
  impl_tac >- gvs[Abbr `mid`] >>
  rewrite_tac[gas_prefix_full_def] >>
  disch_then (qx_choose_then `right_marks`
    (CONJUNCTS_THEN2
      (qx_choosel_then [`right_horizon`,`right_leaf`,`right_pg`,`right_g`,`right_tn`,
                        `right_finish`] strip_assume_tac)
      assume_tac)) >>
  `storage_trace_domain cx st0 mid.storage_trace` by gvs[Abbr `mid`] >>
  `valid_horizon cx st0 right_horizon mid.storage_trace` by metis_tac[] >>
  `gas_origin_ptr_path (DF right_horizon,lo,explicit,ctx,func,PG)
     (s,G,tn) marks (OK t,G',tn')` by metis_tac[] >>
  qexists_tac `marks ++ right_marks` >> conj_tac
  >- (qexistsl_tac [`right_horizon`,`right_leaf`,`right_pg`,`right_g`,`right_tn`,
                    `right_finish`] >>
      conj_tac >- (gvs[Abbr `mid`] >> metis_tac[valid_horizon_append]) >>
      irule (cj 2 gas_origin_ptr_focus_rules) >> metis_tac[]) >>
  `gas_path ctx func s (LENGTH marks) (OK t)` by
    metis_tac[gas_origin_ptr_path_projections, gas_origin_path_erase, gas_marked_path_exec] >>
  drule gas_explicit_append_path >> disch_then (qspec_then `right_marks` assume_tac) >>
  rpt gen_tac >> strip_tac >> rename1 `valid_horizon cx st0 site_horizon obs_pre` >>
  `next v (mid with gas_obs := gas_explicit right_marks t.vs_gas_readings ++ tail) =
       (res,ee')` by
    (qpat_x_assum `bind source next _ = _` mp_tac >>
     asm_rewrite_tac[] >> PURE_REWRITE_TAC[bind_def, GSYM APPEND_ASSOC] >>
     qpat_assum `!tail. source _ = (INL _,_)`
       (qspec_then `gas_explicit right_marks t.vs_gas_readings ++ tail` assume_tac) >>
     gvs[Abbr `mid`]) >>
  `storage_trace_frame (next v)` by simp[] >>
  drule_all storage_trace_frame_prefix >> simp[] >> strip_tac >>
  `mid.storage_trace ++ observations = obs_pre ++ StorageOutcome rq outcome :: sfx` by fs[] >>
  drule bind_trace_outcome_split >> strip_tac
  >- (`ee.storage_trace = obs_pre ++ [StorageOutcome rq outcome] ++ tail'` by
        (qpat_assum `mid.storage_trace = obs_pre ++ StorageOutcome rq outcome :: tail'` mp_tac >>
         simp[NoAsms, Abbr `mid`]) >>
      left_site_at_fixed_trace_tac `!tail. source _ = (INL _,_)` `tail'` `site_horizon` >>
      simp[] >> metis_tac[gas_origin_ptr_focus_marks_comparable]) >>
  `valid_horizon cx st0 site_horizon mid.storage_trace` by metis_tac[valid_horizon_append] >>
  `LENGTH mid.requests = recorded_outcomes_count mid.storage_trace` by
    (qpat_assum `!tail. source _ = _`
       (qspec_then `[]` (mp_then Any mp_tac requests_outcomes_frame_result)) >>
     simp[Abbr `mid`]) >>
  `gas_origin_ptr_path (DF site_horizon,lo,explicit,ctx,func,PG) (s,G,tn) marks (OK t,G',tn')` by
    metis_tac[] >>
  drule_then irule request_site_prepend_path >>
  qpat_x_assum `!tail res ee obs_pre rq outcome sfx H. _ ==>
                request_site _ _ _ (t,G',tn') _ _ _`
    (qspecl_then [`tail`,`res`,`ee'`,`obs_pre`,`rq`,`outcome`,`sfx`,`site_horizon`] mp_tac) >>
  simp[]
QED

Finalise gas_prefix_full_bind

Theorem gas_prefix_full_bind_no_outcome:
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0 source
    (es,s,G,tn) Q1 R1 /\
  (!H res ee gt r. R1 H res ee gt r ==> ISR res) /\
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0 source (es,s,G,tn) /\
  (!H v mid G1 tn1 t. Q1 H (INL v) mid G1 tn1 t ==> ~t.vs_halted) /\
  storage_trace_frame source /\ (!v. storage_trace_frame (next v)) /\
  requests_outcomes_frame source /\
  (!v st gobs res ee. next v (st with gas_obs := gobs) = (res,ee) ==>
     EVERY (\ob. !rq oc. ob = StorageOutcome rq oc ==> computed_precompile rq)
       (DROP (LENGTH st.storage_trace) ee.storage_trace)) ==>
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0 (bind source next) (es,s,G,tn)
Proof
  strip_tac >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ Q1 R1`
    (mp_then Any irule gas_prefix_full_bind) >>
  simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `~t.vs_halted` by
        (`valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
            mid.storage_trace` by fs[storage_trace_domain_def] >>
         qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
           (qspec_then `storage_trace_horizon mid.storage_trace`
             (drule_then assume_tac)) >>
         qpat_assum `!H v mid G1 tn1 t. Q1 H (INL v) mid G1 tn1 t ==> ~t.vs_halted`
           (qspecl_then
             [`storage_trace_horizon mid.storage_trace`,`v`,`mid`,`G1`,`tn1`,`t`]
             (drule_then ACCEPT_TAC))) >>
      irule gas_prefix_full_no_outcome >> simp[] >>
      rpt gen_tac >> strip_tac >>
      first_x_assum drule >> simp[]) >>
  first_assum ACCEPT_TAC
QED

Theorem gas_prefix_full_ignore_bind:
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0 source
    (es,s,G,tn) Q1 R1 /\
  (!H res ee gt r. R1 H res ee gt r ==> ISR res) /\
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0 source (es,s,G,tn) /\
  (!marks v mid G1 tn1 t.
     (!tail. source (es with gas_obs :=
                       gas_explicit marks s.vs_gas_readings ++ tail) =
             (INL v,mid with gas_obs := tail)) /\
     storage_trace_domain cx st0 mid.storage_trace /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==> Q1 H (INL v) mid G1 tn1 t) ==>
     gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0 next (mid,t,G1,tn1)) /\
  storage_trace_frame source /\ storage_trace_frame next /\
  requests_outcomes_frame source ==>
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0 (ignore_bind source next) (es,s,G,tn)
Proof
  rewrite_tac[ignore_bind_def] >> strip_tac >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ Q1 R1`
    (mp_then Any irule gas_prefix_full_bind) >>
  simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem gas_prefix_full_stmts_cons:
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0 (eval_stmt cx stmt)
    (es,s,G,tn) Q1 R1 /\
  (!H res ee gt r. R1 H res ee gt r ==> ISR res) /\
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0 (eval_stmt cx stmt) (es,s,G,tn) /\
  (!marks v mid G1 tn1 t.
     (!tail. eval_stmt cx stmt (es with gas_obs :=
                       gas_explicit marks s.vs_gas_readings ++ tail) =
             (INL v,mid with gas_obs := tail)) /\
     storage_trace_domain cx st0 mid.storage_trace /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==> Q1 H (INL v) mid G1 tn1 t) ==>
     gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0 (eval_stmts cx stmts) (mid,t,G1,tn1)) ==>
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0 (eval_stmts cx (stmt::stmts)) (es,s,G,tn)
Proof
  rewrite_tac[Once evaluate_def] >> strip_tac >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ Q1 R1`
    (mp_then Any irule gas_prefix_full_ignore_bind) >>
  fs[evaluate_storage_trace_frame, evaluate_requests_outcomes_frame] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem gas_prefix_full_if:
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0 condition
    (es,s,G,tn) Q1 R1 /\
  (!H res ee gt r. R1 H res ee gt r ==> ISR res) /\
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0 condition (es,s,G,tn) /\
  (!marks b mid G1 tn1 t.
     (!tail. condition (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
             (INL b,mid with gas_obs := tail)) /\
     storage_trace_domain cx st0 mid.storage_trace /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==> Q1 H (INL b) mid G1 tn1 t) ==>
     gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
       (if b then yes else no) (mid,t,G1,tn1)) /\
  storage_trace_frame condition /\ storage_trace_frame yes /\ storage_trace_frame no /\
  requests_outcomes_frame condition ==>
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
    (bind condition (\b. if b then yes else no)) (es,s,G,tn)
Proof
  strip_tac >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ Q1 R1`
    (mp_then Any irule gas_prefix_full_bind) >>
  simp[storage_trace_frame_cond] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem gas_prefix_full_zero_prefix_guarded:
  storage_trace_frame source /\
  storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
         (s0,G0,tn0) [] (OK s1,G1,tn1)) /\
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0 source
    (es,s1,G1,tn1) ==>
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0 source (es,s0,G0,tn0)
Proof
  strip_tac >>
  `s1.vs_gas_readings = s0.vs_gas_readings` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ [] _`
       (qspec_then `storage_trace_horizon es.storage_trace` mp_tac) >>
     impl_tac >- fs[storage_trace_domain_def] >> strip_tac >>
     drule gas_origin_ptr_path_projections >> strip_tac >>
     drule gas_origin_path_erase >> strip_tac >>
     drule gas_marked_path_ok_suffix >> simp[]) >>
  qpat_x_assum `gas_prefix_full _ _ _ _ _`
    (qx_choose_then `marks` strip_assume_tac o
     ONCE_REWRITE_RULE[gas_prefix_full_def]) >>
  rewrite_tac[gas_prefix_full_def] >> qexists_tac `marks` >> conj_tac
  >- (qexistsl_tac [`H`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      `valid_horizon cx st0 H es.storage_trace` by metis_tac[] >>
      `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s0,G0,tn0) [] (OK s1,G1,tn1)` by
        metis_tac[] >>
      drule_then (irule o SIMP_RULE (srw_ss()) []) (cj 2 gas_origin_ptr_focus_rules) >>
      first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >> rename1 `valid_horizon cx st0 site_horizon obs_pre` >>
  `valid_horizon cx st0 site_horizon es.storage_trace` by
    (drule_all storage_trace_frame_prefix >> simp[] >> strip_tac >>
     `es.storage_trace ++ observations = obs_pre ++ StorageOutcome rq outcome :: sfx` by fs[] >>
     drule bind_trace_outcome_split >> strip_tac
     >- (qpat_x_assum `LENGTH es.storage_trace <= LENGTH obs_pre` mp_tac >>
         qpat_assum `es.storage_trace = obs_pre ++ StorageOutcome rq outcome :: tail'`
           (fn trace => PURE_REWRITE_TAC[trace,LENGTH_APPEND,LENGTH]) >>
         decide_tac) >>
     metis_tac[valid_horizon_append]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ [] _`
    (qspec_then `site_horizon` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  drule_then irule request_site_prepend_path >>
  qpat_x_assum `!tail res ee obs_pre rq outcome sfx H. _`
    (qspecl_then [`tail`,`res`,`ee`,`obs_pre`,`rq`,`outcome`,`sfx`,`site_horizon`] mp_tac) >>
  simp[]
QED
