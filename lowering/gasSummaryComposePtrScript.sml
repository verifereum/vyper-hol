(* Sequential source evaluation over counted pointer-checked paths: the
 * twins of gasSummary's and gasSummaryCompose's marked executions and
 * their bind, exception and cleanup rules, with the ghost threaded from
 * one segment to the next; and gas_outcome_ptr's sequencing, where an
 * exempt prefix or suffix makes the whole exempt.
 *
 * TOP-LEVEL:
 *   gas_marked_exec_ptr -- gas_marked_exec over gas_path_ptr, with the
 *     ghost before and after
 *   gas_marked_exec_ptr_bind_normal, _bind_exception, _finally -- its
 *     composition
 *   gas_summary_ptr_at_bind_normal, _bind_exception, gas_outcome_ptr_bind
 *     -- bind for summaries and outcomes
 *   gas_outcome_ptr_prefix -- a path that reads no source gas in front of
 *     an outcome
 *   gas_outcome_ptr_erase -- the gas_outcome F an outcome gives, without
 *     the ghost or the check
 *)
Theory gasSummaryComposePtr
Ancestors
  fragGasSeqPtr fragGasPathPtr gasOutcome gasStorage gasExemptCert stmtSimDeclGas
  vyperStorageFootprint vyperStorageTrace
  gasSummaryCompose gasSummary fragGasMode fragGasPath gasCount
  vyperState vyperInterpreter list rich_list arithmetic

(* The source run on the marked explicit reads gives res, and the target
   takes a pointer-checked path from s0 with the ghost (G0, tn0) to r,
   with the ghost (G, tn) where it ends. *)
Definition gas_marked_exec_ptr_def:
  gas_marked_exec_ptr D (ctx, func) PG source (es, s0, G0, tn0) marks
    res es_end G tn r <=>
    (!tail.
       source (es with gas_obs :=
                 gas_explicit marks s0.vs_gas_readings ++ tail) =
         (res, es_end with gas_obs := tail)) /\
    gas_path_ptr D 0 ctx func PG G0 tn0 s0 (LENGTH marks) G tn r
End

Theorem gas_summary_ptr_at_marked:
  gas_summary_ptr_at D (ctx, func) PG cx st0 marks source (es, s0, G0, tn0)
    Q R <=>
    ?res es_end G tn r.
      (!tail.
         source (es with gas_obs :=
                   gas_explicit marks s0.vs_gas_readings ++ tail) =
           (res, es_end with gas_obs := tail)) /\
      !H. valid_horizon cx st0 H es_end.storage_trace ==>
        gas_marked_exec_ptr (D H) (ctx, func) PG source (es, s0, G0, tn0)
          marks res es_end G tn r /\
        ((?t. r = OK t /\ Q H res (es_end with gas_obs := []) G tn t) \/
         (exit_result r /\ R H res (es_end with gas_obs := []) (G, tn) r))
Proof
  rewrite_tac[gas_summary_ptr_at_def, gas_marked_exec_ptr_def] >>
  eq_tac >> strip_tac >>
  qexistsl_tac [`res`, `es_end`, `G`, `tn`, `r`] >> asm_rewrite_tac[] >>
  gen_tac >> disch_tac >> first_x_assum drule >> simp[]
QED

Theorem gas_marked_exec_ptr_exec:
  gas_marked_exec_ptr D (ctx, func) PG source (es, s0, G0, tn0) marks
    res es_end G tn r ==>
  gas_marked_exec F (ctx, func) source (es, s0) marks res es_end r
Proof
  simp[gas_marked_exec_ptr_def, gas_marked_exec_def, gas_marked_path_def] >>
  metis_tac[gas_path_ptr_erase]
QED

Theorem gas_marked_exec_ptr_no_source_read:
  (!tail. source (es with gas_obs := tail) =
            (res, es_end with gas_obs := tail)) /\
  gas_path_ptr D 0 ctx func PG G0 tn0 s0 n G tn r ==>
  gas_marked_exec_ptr D (ctx, func) PG source (es, s0, G0, tn0)
    (REPLICATE n F) res es_end G tn r
Proof
  simp[gas_marked_exec_ptr_def]
QED

Theorem gas_marked_exec_ptr_bind_normal:
  gas_marked_exec_ptr D (ctx, func) PG source (es, s0, G0, tn0) left
    (INL v) mid G1 tn1 (OK t) /\
  gas_marked_exec_ptr D (ctx, func) PG (next v)
    (mid with gas_obs := [], t, G1, tn1) right res fin G tn r ==>
  gas_marked_exec_ptr D (ctx, func) PG (bind source next)
    (es, s0, G0, tn0) (left ++ right) res fin G tn r
Proof
  rewrite_tac[gas_marked_exec_ptr_def] >> strip_tac >> conj_tac
  >- (`gas_path ctx func s0 (LENGTH left) (OK t)` by
        metis_tac[gas_path_ptr_erase] >>
      drule gas_explicit_append_path >>
      disch_then (qspec_then `right` SUBST1_TAC) >>
      irule gas_source_bind_normal >>
      qexistsl_tac [`mid`, `v`] >> simp[]) >>
  simp[LENGTH_APPEND] >> metis_tac[gas_path_ptr_then]
QED

Theorem gas_marked_exec_ptr_bind_exception:
  gas_marked_exec_ptr D (ctx, func) PG source (es, s0, G0, tn0) marks
    (INR exc) fin G tn r ==>
  gas_marked_exec_ptr D (ctx, func) PG (bind source next)
    (es, s0, G0, tn0) marks (INR exc) fin G tn r
Proof
  simp[gas_marked_exec_ptr_def, gas_source_bind_exception]
QED

(* Scope and call cleanup can change the source frame without reading gas. *)
Theorem gas_marked_exec_ptr_finally:
  gas_marked_exec_ptr D (ctx, func) PG source (es, s0, G0, tn0) marks
    res mid G tn r /\
  (!tail. cleanup ((mid with gas_obs := []) with gas_obs := tail) =
     (INL (), fin with gas_obs := tail)) ==>
  gas_marked_exec_ptr D (ctx, func) PG (finally source cleanup)
    (es, s0, G0, tn0) marks res fin G tn r
Proof
  rewrite_tac[gas_marked_exec_ptr_def] >> strip_tac >>
  `!tail. ((mid with gas_obs := []) with gas_obs := tail) =
          (mid with gas_obs := tail)` by
    simp[evaluation_state_component_equality] >>
  gvs[] >> gen_tac >> simp[finally_def] >> Cases_on `res` >>
  simp[ignore_bind_def, bind_def, return_def, raise_def]
QED

Theorem gas_summary_ptr_at_conseq:
  gas_summary_ptr_at D (ctx, func) PG cx st0 marks source (es, s0, G0, tn0)
    Q R /\
  (!H res ee G tn t.
     valid_horizon cx st0 H ee.storage_trace /\ Q H res ee G tn t ==>
     Q' H res ee G tn t) /\
  (!H res ee gt r.
     valid_horizon cx st0 H ee.storage_trace /\ R H res ee gt r ==>
     R' H res ee gt r) ==>
  gas_summary_ptr_at D (ctx, func) PG cx st0 marks source (es, s0, G0, tn0)
    Q' R'
Proof
  rewrite_tac[gas_summary_ptr_at_def] >> strip_tac >>
  qexistsl_tac [`res`, `es_end`, `G`, `tn`, `r`] >> asm_rewrite_tac[] >>
  gen_tac >> disch_tac >>
  last_x_assum drule >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem gas_outcome_ptr_conseq:
  gas_outcome_ptr D tops (ctx, func) PG cx st0 source (es, s0, G0, tn0) Q R /\
  (!H res ee G tn t.
     valid_horizon cx st0 H ee.storage_trace /\ Q H res ee G tn t ==>
     Q' H res ee G tn t) /\
  (!H res ee gt r.
     valid_horizon cx st0 H ee.storage_trace /\ R H res ee gt r ==>
     R' H res ee gt r) ==>
  gas_outcome_ptr D tops (ctx, func) PG cx st0 source (es, s0, G0, tn0) Q' R'
Proof
  rewrite_tac[gas_outcome_ptr_def] >> strip_tac >> qexists_tac `marks`
  >- simp[]
  >- (disj2_tac >> disj1_tac >> irule gas_summary_ptr_at_conseq >>
      metis_tac[]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

(* A source run whose end has no valid horizon is a bad storage prefix. *)
Theorem gas_bad_storage_at_no_horizon:
  (!tail.
     source (es with gas_obs :=
               gas_explicit marks s0.vs_gas_readings ++ tail) =
       (res, es_end with gas_obs := tail)) /\
  (!H. ~valid_horizon cx st0 H es_end.storage_trace) ==>
  gas_bad_storage_at cx st0 source es s0 marks
Proof
  rw[gas_bad_storage_at_def, storage_trace_domain_def]
QED

Theorem gas_summary_ptr_at_erase:
  gas_summary_ptr_at D (ctx, func) PG cx st0 marks source (es, s0, G0, tn0)
    Q R ==>
  gas_bad_storage_at cx st0 source es s0 marks \/
  gas_summary_at F (ctx, func) marks source (es, s0)
    (\res ee t. !H. valid_horizon cx st0 H ee.storage_trace ==>
       ?G tn. Q H res ee G tn t)
    (\res ee r. !H. valid_horizon cx st0 H ee.storage_trace ==>
       ?gt. R H res ee gt r)
Proof
  rewrite_tac[gas_summary_ptr_at_def] >> strip_tac >>
  Cases_on `?H. valid_horizon cx st0 H es_end.storage_trace`
  >- (disj2_tac >> pop_assum strip_assume_tac >>
      first_assum drule >> strip_tac >>
      drule gas_path_ptr_erase >> strip_tac >>
      simp[gas_summary_at_def, gas_marked_exec_def, gas_marked_path_def] >>
      qexistsl_tac [`res`, `es_end`, `r`] >>
      Cases_on `r` >> gvs[fragExecTheory.exit_result_def] >> metis_tac[]) >>
  disj1_tac >> irule gas_bad_storage_at_no_horizon >> fs[] >>
  metis_tac[]
QED

Theorem gas_outcome_ptr_erase:
  gas_outcome_ptr D tops (ctx, func) PG cx st0 source (es, s0, G0, tn0) Q R ==>
  gas_outcome F tops (ctx, func) cx st0 source (es, s0)
    (\H res ee t. ?G tn. Q H res ee G tn t)
    (\H res ee r. ?gt. R H res ee gt r)
Proof
  rewrite_tac[gas_outcome_ptr_def, gas_outcome_def] >> strip_tac >>
  qexists_tac `marks` >> simp[]
  >- (drule gas_summary_ptr_at_erase >> strip_tac >> simp[]) >>
  metis_tac[]
QED

(* How a pointer outcome is proved: with no valid horizon where it starts
   the storage is bad; otherwise one valid horizon gives the facts that fix
   the endpoint, and one valid where it ends fixes the ghost and the Venom
   result that every horizon valid there checks. *)
Theorem gas_outcome_ptr_lo_intro:
  storage_trace_frame source /\
  ((?H1. valid_horizon cx st0 H1 es.storage_trace) ==>
   ?marks res es_end.
     (!tail.
        source (es with gas_obs :=
                  gas_explicit marks s0.vs_gas_readings ++ tail) =
          (res,es_end with gas_obs := tail)) /\
     !H2. valid_horizon cx st0 H2 es_end.storage_trace ==>
       ?G tn r. !H. valid_horizon cx st0 H es_end.storage_trace ==>
         gas_path_ptr (D H) lo ctx func PG G0 tn0 s0 (LENGTH marks) G tn r /\
         ((?t. r = OK t /\ Q H res (es_end with gas_obs := []) G tn t) \/
          (exit_result r /\ R H res (es_end with gas_obs := []) (G,tn) r))) ==>
  gas_outcome_ptr_lo D lo tops (ctx,func) PG cx st0 source (es,s0,G0,tn0) Q R
Proof
  rewrite_tac[gas_outcome_ptr_lo_def, gas_summary_ptr_lo_def] >> strip_tac >>
  Cases_on `?H1. valid_horizon cx st0 H1 es.storage_trace`
  >- (fs[] >> qexists_tac `marks` >> disj2_tac >> disj1_tac >>
      qexistsl_tac [`res`, `es_end`] >> simp[] >>
      Cases_on `?H2. valid_horizon cx st0 H2 es_end.storage_trace` >> fs[] >>
      metis_tac[]) >>
  qexists_tac `[]` >> disj1_tac >> irule gas_bad_storage_at_initial >>
  fs[storage_trace_domain_def] >> metis_tac[]
QED

Theorem gas_summary_ptr_at_bind_normal:
  gas_marked_exec F (ctx, func) source (es, s0) left (INL v) mid (OK t) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
       gas_path_ptr (D H) 0 ctx func PG G0 tn0 s0 (LENGTH left) G1 tn1
         (OK t)) /\
  storage_trace_frame (next v) /\
  gas_summary_ptr_at D (ctx, func) PG cx st0 right (next v)
    (mid with gas_obs := [], t, G1, tn1) Q R ==>
  gas_summary_ptr_at D (ctx, func) PG cx st0 (left ++ right)
    (bind source next) (es, s0, G0, tn0) Q R
Proof
  rewrite_tac[gas_summary_ptr_at_def, gas_marked_exec_def,
              gas_marked_path_def] >> strip_tac >>
  qexistsl_tac [`res`, `es_end`, `G`, `tn`, `r`] >> conj_tac
  >- (drule gas_explicit_append_path >>
      disch_then (qspec_then `right` SUBST1_TAC) >>
      irule gas_source_bind_normal >> qexistsl_tac [`mid`, `v`] >> simp[]) >>
  gen_tac >> strip_tac >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (qpat_assum `!tail. next v _ = _` (qspec_then `[]` assume_tac) >>
     `valid_horizon cx st0 H (es_end with gas_obs := []).storage_trace` by
       simp[] >>
     drule_all valid_horizon_frame >> simp[]) >>
  last_x_assum drule >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  simp[LENGTH_APPEND] >> metis_tac[gas_path_ptr_then]
QED

Theorem gas_summary_ptr_at_bind_exception:
  (!tail.
     source (es with gas_obs :=
               gas_explicit marks s0.vs_gas_readings ++ tail) =
       (INR exc, fin with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H fin.storage_trace ==>
       gas_path_ptr (D H) 0 ctx func PG G0 tn0 s0 (LENGTH marks) G tn r /\
       exit_result r /\ R H (INR exc) (fin with gas_obs := []) (G, tn) r) ==>
  gas_summary_ptr_at D (ctx, func) PG cx st0 marks (bind source next)
    (es, s0, G0, tn0) Q R
Proof
  rewrite_tac[gas_summary_ptr_at_def] >> strip_tac >>
  qexistsl_tac [`INR exc`, `fin`, `G`, `tn`, `r`] >>
  simp[gas_source_bind_exception] >> metis_tac[]
QED

(* gas_exempt_cert_zero_prefix for a prefix of generated reads only. *)
Theorem gas_exempt_cert_path_prefix:
  gas_path ctx func s0 n (OK s1) /\
  gas_exempt_cert F tops (ctx, func) source (es, s1) marks (err, ee)
    (leaf, fstate) ==>
  gas_exempt_cert F tops (ctx, func) source (es, s0)
    (REPLICATE n F ++ marks) (err, ee) (leaf, fstate)
Proof
  strip_tac >>
  `gas_marked_exec F (ctx, func) (return ()) (es, s0) (REPLICATE n F)
     (INL ()) es (OK s1)` by
    simp[gas_marked_exec_def, gas_marked_path_def, return_def] >>
  drule gas_exempt_cert_start_gas_obs >>
  disch_then (qspec_then `[]` assume_tac) >> fs[] >>
  drule gas_exempt_cert_bind_unit >>
  disch_then (qspecl_then [`tops`, `\u. source`] mp_tac) >>
  simp[bind_return] >> disch_then irule >> simp[]
QED

Theorem gas_bad_storage_at_path_prefix[local]:
  gas_path ctx func s0 n (OK s1) /\
  gas_bad_storage_at cx st0 source es s1 marks ==>
  gas_bad_storage_at cx st0 source es s0 (REPLICATE n F ++ marks)
Proof
  rewrite_tac[gas_bad_storage_at_def] >> strip_tac >>
  `s1.vs_gas_readings = DROP n s0.vs_gas_readings` by
    (drule gas_path_suffix >> simp[gas_count_suffix_def]) >>
  `gas_explicit (REPLICATE n F ++ marks) s0.vs_gas_readings =
     gas_explicit marks s1.vs_gas_readings` by
    simp[gas_explicit_append] >>
  fs[]
QED

(* Generated reads in front (an allocation, say) keep an outcome: the
   prefix path is checked under every horizon. *)
Theorem gas_summary_ptr_at_prefix:
  (!H. gas_path_ptr (D H) 0 ctx func PG G0 tn0 s0 n G1 tn1 (OK s1)) /\
  gas_summary_ptr_at D (ctx, func) PG cx st0 marks source (es, s1, G1, tn1)
    Q R ==>
  gas_summary_ptr_at D (ctx, func) PG cx st0 (REPLICATE n F ++ marks) source
    (es, s0, G0, tn0) Q R
Proof
  rewrite_tac[gas_summary_ptr_at_def] >> strip_tac >>
  qexistsl_tac [`res`, `es_end`, `G`, `tn`, `r`] >>
  `gas_explicit (REPLICATE n F ++ marks) s0.vs_gas_readings =
     gas_explicit marks s1.vs_gas_readings` by
    (`s1.vs_gas_readings = DROP n s0.vs_gas_readings` by
       metis_tac[gas_path_ptr_ok_suffix] >>
     simp[gas_explicit_append]) >>
  asm_rewrite_tac[LENGTH_APPEND, LENGTH_REPLICATE] >>
  gen_tac >> strip_tac >> first_x_assum drule >> strip_tac >>
  asm_rewrite_tac[] >> metis_tac[gas_path_ptr_then]
QED

Theorem gas_outcome_ptr_prefix:
  (!H. gas_path_ptr (D H) 0 ctx func PG G0 tn0 s0 n G1 tn1 (OK s1)) /\
  gas_outcome_ptr D tops (ctx, func) PG cx st0 source (es, s1, G1, tn1) Q R ==>
  gas_outcome_ptr D tops (ctx, func) PG cx st0 source (es, s0, G0, tn0) Q R
Proof
  rewrite_tac[gas_outcome_ptr_def] >> strip_tac >>
  qexists_tac `REPLICATE n F ++ marks` >>
  `gas_path ctx func s0 n (OK s1)` by metis_tac[gas_path_ptr_erase]
  >- (disj1_tac >> irule gas_bad_storage_at_path_prefix >> metis_tac[])
  >- (disj2_tac >> disj1_tac >> irule gas_summary_ptr_at_prefix >>
      metis_tac[]) >>
  disj2_tac >> disj2_tac >> qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  irule gas_exempt_cert_path_prefix >> metis_tac[]
QED

(* The continuation's outcome after a prefix that goes on.  The cert
   premise is gas_exempt_cert's bind_<ty> rule for the prefix's result
   type, with k = \v. ignore_bind (next v) (return ()). *)
Theorem gas_outcome_ptr_bind_normal:
  gas_marked_exec F (ctx, func) source (es, s0) left (INL v) mid (OK t) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
       gas_path_ptr (D H) 0 ctx func PG G0 tn0 s0 (LENGTH left) G1 tn1
         (OK t)) /\
  storage_trace_frame (next v) /\
  gas_outcome_ptr D tops (ctx, func) PG cx st0 (next v)
    (mid with gas_obs := [], t, G1, tn1) Q R /\
  (!right err ee leaf fstate.
     gas_exempt_cert F tops (ctx, func) (ignore_bind (next v) (return ()))
       (mid with gas_obs := [], t) right (err, ee) (leaf, fstate) ==>
     gas_exempt_cert F tops (ctx, func)
       (bind source (\v. ignore_bind (next v) (return ())))
       (es, s0) (left ++ right) (err, ee) (leaf, fstate)) ==>
  gas_outcome_ptr D tops (ctx, func) PG cx st0 (bind source next)
    (es, s0, G0, tn0) Q R
Proof
  rewrite_tac[gas_outcome_ptr_def] >> strip_tac >>
  qexists_tac `left ++ marks`
  >- (disj1_tac >> irule gas_bad_storage_at_bind_right >> metis_tac[])
  >- (disj2_tac >> disj1_tac >> irule gas_summary_ptr_at_bind_normal >>
      metis_tac[]) >>
  disj2_tac >> disj2_tac >>
  `ignore_bind (bind source next) (return ()) =
     bind source (\v. ignore_bind (next v) (return ()))` by
    simp[ignore_bind_def, bind_assoc] >>
  asm_rewrite_tac[] >> metis_tac[]
QED

(* Bind of outcomes.  The two cert premises are gas_exempt_cert's
   error_<ty> and bind_<ty> rules for the source's result type, with
   k = \v. ignore_bind (next v) (return ()):
   ignore_bind (bind source next) (return ()) is bind source k.  The
   continuation keeps the storage trace's prefix, so a horizon valid where
   the whole run ends is valid where the first part ends. *)
Theorem gas_outcome_ptr_bind:
  gas_outcome_ptr D tops (ctx, func) PG cx st0 source (es, s0, G0, tn0)
    (\H res es_mid G tn t. ?v. res = INL v /\
       gas_outcome_ptr D tops (ctx, func) PG cx st0 (next v)
         (es_mid, t, G, tn) Q R)
    (\H res es_end gt r. ?exc. res = INR exc /\ R H (INR exc) es_end gt r) /\
  (!v. storage_trace_frame (next v)) /\
  (!marks err ee leaf fstate.
     gas_exempt_cert F tops (ctx, func) (ignore_bind source (return ()))
       (es, s0) marks (err, ee) (leaf, fstate) ==>
     gas_exempt_cert F tops (ctx, func)
       (bind source (\v. ignore_bind (next v) (return ())))
       (es, s0) marks (err, ee) (leaf, fstate)) /\
  (!left v mid t right err ee leaf fstate.
     gas_marked_exec F (ctx, func) source (es, s0) left (INL v) mid (OK t) /\
     gas_exempt_cert F tops (ctx, func) (ignore_bind (next v) (return ()))
       (mid with gas_obs := [], t) right (err, ee) (leaf, fstate) ==>
     gas_exempt_cert F tops (ctx, func)
       (bind source (\v. ignore_bind (next v) (return ())))
       (es, s0) (left ++ right) (err, ee) (leaf, fstate)) ==>
  gas_outcome_ptr D tops (ctx, func) PG cx st0 (bind source next)
    (es, s0, G0, tn0) Q R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ source _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_ptr_def])
  >- (rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `marks` >>
      disj1_tac >> irule gas_bad_storage_at_bind_left >> simp[])
  >- (pop_assum (strip_assume_tac o REWRITE_RULE [gas_summary_ptr_at_def]) >>
      Cases_on `?H. valid_horizon cx st0 H es_end.storage_trace`
      >- (pop_assum strip_assume_tac >>
          first_assum drule >> strip_tac >> gvs[]
          >- (`gas_path ctx func s0 (LENGTH marks) (OK t)` by
                metis_tac[gas_path_ptr_erase] >>
              mp_tac (Q.INST [`left` |-> `marks`, `mid` |-> `es_end`,
                              `G1` |-> `G`, `tn1` |-> `tn`]
                        gas_outcome_ptr_bind_normal) >>
              impl_tac
              >- (rpt conj_tac
                  >- simp[gas_marked_exec_def, gas_marked_path_def]
                  >- fs[]
                  >- fs[]
                  >- fs[] >>
                  rpt strip_tac >>
                  qpat_x_assum `!left v mid t right err ee leaf fstate. _`
                    (qspecl_then [`marks`, `v`, `es_end`, `t`, `right`,
                                  `err`, `ee`, `leaf`, `fstate`] mp_tac) >>
                  simp[gas_marked_exec_def, gas_marked_path_def]) >>
              simp[]) >>
          rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `marks` >>
          disj2_tac >> disj1_tac >>
          mp_tac (Q.INST [`fin` |-> `es_end`]
                    gas_summary_ptr_at_bind_exception) >>
          impl_tac
          >- (simp[] >> rpt strip_tac >> first_x_assum drule >> strip_tac >>
              gvs[fragExecTheory.exit_result_def]) >>
          simp[]) >>
      rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `marks` >>
      disj1_tac >> irule gas_bad_storage_at_bind_left >> simp[] >>
      irule gas_bad_storage_at_no_horizon >> fs[] >> metis_tac[]) >>
  `ignore_bind (bind source next) (return ()) =
     bind source (\v. ignore_bind (next v) (return ()))` by
    simp[ignore_bind_def, bind_assoc] >>
  asm_rewrite_tac[gas_outcome_ptr_def] >> metis_tac[]
QED

(* Recording a storage event before source: the run is source's from the
   extended trace, and no instruction is spent on the event. *)
Theorem record_storage_event_then[local]:
  ignore_bind (record_storage_event ev) source (es with gas_obs := g) =
    source ((es with storage_trace := es.storage_trace ++ [ev])
              with gas_obs := g)
Proof
  simp[vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_def,
       vyperStateTheory.record_storage_event_def,
       vyperStateTheory.return_def]
QED

Theorem gas_outcome_ptr_record_storage_event:
  gas_outcome_ptr D tops (ctx,func) PG cx st0 source
    (es with storage_trace := es.storage_trace ++ [ev], s0, G0, tn0) Q R /\
  ~s0.vs_halted ==>
  gas_outcome_ptr D tops (ctx,func) PG cx st0
    (ignore_bind (record_storage_event ev) source) (es, s0, G0, tn0) Q R
Proof
  rewrite_tac[gas_outcome_ptr_def] >> strip_tac >> qexists_tac `marks`
  >- (disj1_tac >> fs[gas_bad_storage_at_def, record_storage_event_then])
  >- (disj2_tac >> disj1_tac >>
      fs[gas_summary_ptr_at_def, record_storage_event_then] >>
      metis_tac[]) >>
  disj2_tac >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  `ignore_bind (ignore_bind (record_storage_event ev) source) (return ()) =
   bind (record_storage_event ev) (\u. ignore_bind source (return ()))` by
    simp[vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_assoc] >>
  pop_assum SUBST1_TAC >>
  qspecl_then [`F`, `tops`, `ctx`, `func`, `record_storage_event ev`,
    `\u. ignore_bind source (return ())`, `es`, `s0`, `[]`, `()`,
    `es with storage_trace := es.storage_trace ++ [ev]`, `s0`, `marks`,
    `err`, `ee`, `leaf`, `finish'`] mp_tac gas_exempt_cert_bind_unit >>
  impl_tac
  >- (conj_tac
      >- simp[gas_marked_exec_def, gas_marked_path_def, gas_path_rules,
              vyperStateTheory.record_storage_event_def,
              vyperStateTheory.return_def] >>
      drule gas_exempt_cert_start_gas_obs >> simp[]) >>
  simp[]
QED
