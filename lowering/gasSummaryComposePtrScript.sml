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
  fragGasSeqPtr fragGasPathPtr gasOutcome gasExemptCert stmtSimDeclGas
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
  gas_summary_ptr_at D (ctx, func) PG marks source (es, s0, G0, tn0) Q R <=>
    ?res es_end G tn r.
      gas_marked_exec_ptr D (ctx, func) PG source (es, s0, G0, tn0) marks
        res es_end G tn r /\
      ((?t. r = OK t /\ Q res (es_end with gas_obs := []) G tn t) \/
       (exit_result r /\ R res (es_end with gas_obs := []) (G, tn) r))
Proof
  rewrite_tac[gas_summary_ptr_at_def, gas_marked_exec_ptr_def, CONJ_ASSOC]
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
  gas_summary_ptr_at D (ctx, func) PG marks source (es, s0, G0, tn0) Q R /\
  (!res ee G tn t. Q res ee G tn t ==> Q' res ee G tn t) /\
  (!res ee gt r. R res ee gt r ==> R' res ee gt r) ==>
  gas_summary_ptr_at D (ctx, func) PG marks source (es, s0, G0, tn0) Q' R'
Proof
  rewrite_tac[gas_summary_ptr_at_def] >> metis_tac[]
QED

Theorem gas_outcome_ptr_conseq:
  gas_outcome_ptr D tops (ctx, func) PG source (es, s0, G0, tn0) Q R /\
  (!res ee G tn t. Q res ee G tn t ==> Q' res ee G tn t) /\
  (!res ee gt r. R res ee gt r ==> R' res ee gt r) ==>
  gas_outcome_ptr D tops (ctx, func) PG source (es, s0, G0, tn0) Q' R'
Proof
  rewrite_tac[gas_outcome_ptr_def] >> metis_tac[gas_summary_ptr_at_conseq]
QED

Theorem gas_summary_ptr_at_erase:
  gas_summary_ptr_at D (ctx, func) PG marks source (es, s0, G0, tn0) Q R ==>
  gas_summary_at F (ctx, func) marks source (es, s0)
    (\res ee t. ?G tn. Q res ee G tn t) (\res ee r. ?gt. R res ee gt r)
Proof
  rw[gas_summary_ptr_at_def, gas_summary_at_def, gas_marked_exec_def,
     gas_marked_path_def] >>
  metis_tac[gas_path_ptr_erase]
QED

Theorem gas_outcome_ptr_erase:
  gas_outcome_ptr D tops (ctx, func) PG source (es, s0, G0, tn0) Q R ==>
  gas_outcome F tops (ctx, func) source (es, s0)
    (\res ee t. ?G tn. Q res ee G tn t) (\res ee r. ?gt. R res ee gt r)
Proof
  rw[gas_outcome_ptr_def, gas_outcome_def] >>
  metis_tac[gas_summary_ptr_at_erase]
QED

Theorem gas_summary_ptr_at_bind_normal:
  gas_marked_exec_ptr D (ctx, func) PG source (es, s0, G0, tn0) left
    (INL v) mid G1 tn1 (OK t) /\
  gas_summary_ptr_at D (ctx, func) PG right (next v)
    (mid with gas_obs := [], t, G1, tn1) Q R ==>
  gas_summary_ptr_at D (ctx, func) PG (left ++ right) (bind source next)
    (es, s0, G0, tn0) Q R
Proof
  rw[gas_summary_ptr_at_marked] >>
  metis_tac[gas_marked_exec_ptr_bind_normal]
QED

Theorem gas_summary_ptr_at_bind_exception:
  gas_marked_exec_ptr D (ctx, func) PG source (es, s0, G0, tn0) marks
    (INR exc) fin G tn r /\
  exit_result r /\ R (INR exc) (fin with gas_obs := []) (G, tn) r ==>
  gas_summary_ptr_at D (ctx, func) PG marks (bind source next)
    (es, s0, G0, tn0) Q R
Proof
  rw[gas_summary_ptr_at_marked] >>
  metis_tac[gas_marked_exec_ptr_bind_exception]
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

Theorem gas_summary_ptr_at_prefix:
  gas_path_ptr D 0 ctx func PG G0 tn0 s0 n G1 tn1 (OK s1) /\
  gas_summary_ptr_at D (ctx, func) PG marks source (es, s1, G1, tn1) Q R ==>
  gas_summary_ptr_at D (ctx, func) PG (REPLICATE n F ++ marks) source
    (es, s0, G0, tn0) Q R
Proof
  rewrite_tac[gas_summary_ptr_at_def] >> strip_tac >>
  qexistsl_tac [`res`, `es_end`, `G`, `tn`, `r`] >>
  `s1.vs_gas_readings = DROP n s0.vs_gas_readings` by
    metis_tac[gas_path_ptr_ok_suffix] >>
  `gas_explicit (REPLICATE n F ++ marks) s0.vs_gas_readings =
     gas_explicit marks s1.vs_gas_readings` by
    simp[gas_explicit_append] >>
  asm_rewrite_tac[LENGTH_APPEND, LENGTH_REPLICATE] >>
  metis_tac[gas_path_ptr_then]
QED

(* Generated reads in front (an allocation, say) keep an outcome. *)
Theorem gas_outcome_ptr_prefix:
  gas_path_ptr D 0 ctx func PG G0 tn0 s0 n G1 tn1 (OK s1) /\
  gas_outcome_ptr D tops (ctx, func) PG source (es, s1, G1, tn1) Q R ==>
  gas_outcome_ptr D tops (ctx, func) PG source (es, s0, G0, tn0) Q R
Proof
  rewrite_tac[gas_outcome_ptr_def] >> strip_tac >>
  qexists_tac `REPLICATE n F ++ marks`
  >- (disj1_tac >> irule gas_summary_ptr_at_prefix >> metis_tac[]) >>
  disj2_tac >> qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  irule gas_exempt_cert_path_prefix >> metis_tac[gas_path_ptr_erase]
QED

(* The continuation's outcome after a prefix that goes on.  The cert
   premise is gas_exempt_cert's bind_<ty> rule for the prefix's result
   type, with k = \v. ignore_bind (next v) (return ()). *)
Theorem gas_outcome_ptr_bind_normal:
  gas_marked_exec_ptr D (ctx, func) PG source (es, s0, G0, tn0) left
    (INL v) mid G1 tn1 (OK t) /\
  gas_outcome_ptr D tops (ctx, func) PG (next v)
    (mid with gas_obs := [], t, G1, tn1) Q R /\
  (!right err ee leaf fstate.
     gas_marked_exec F (ctx, func) source (es, s0) left (INL v) mid (OK t) /\
     gas_exempt_cert F tops (ctx, func) (ignore_bind (next v) (return ()))
       (mid with gas_obs := [], t) right (err, ee) (leaf, fstate) ==>
     gas_exempt_cert F tops (ctx, func)
       (bind source (\v. ignore_bind (next v) (return ())))
       (es, s0) (left ++ right) (err, ee) (leaf, fstate)) ==>
  gas_outcome_ptr D tops (ctx, func) PG (bind source next) (es, s0, G0, tn0)
    Q R
Proof
  rewrite_tac[gas_outcome_ptr_def] >> strip_tac
  >- (qexists_tac `left ++ marks` >> disj1_tac >>
      irule gas_summary_ptr_at_bind_normal >> metis_tac[]) >>
  qexists_tac `left ++ marks` >> disj2_tac >>
  `ignore_bind (bind source next) (return ()) =
     bind source (\v. ignore_bind (next v) (return ()))` by
    simp[ignore_bind_def, bind_assoc] >>
  asm_rewrite_tac[] >> metis_tac[gas_marked_exec_ptr_exec]
QED

(* Bind of outcomes.  The two cert premises are gas_exempt_cert's
   error_<ty> and bind_<ty> rules for the source's result type, with
   k = \v. ignore_bind (next v) (return ()):
   ignore_bind (bind source next) (return ()) is bind source k. *)
Theorem gas_outcome_ptr_bind:
  gas_outcome_ptr D tops (ctx, func) PG source (es, s0, G0, tn0)
    (\res es_mid G tn t. ?v. res = INL v /\
       gas_outcome_ptr D tops (ctx, func) PG (next v) (es_mid, t, G, tn) Q R)
    (\res es_end gt r. ?exc. res = INR exc /\ R (INR exc) es_end gt r) /\
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
  gas_outcome_ptr D tops (ctx, func) PG (bind source next) (es, s0, G0, tn0)
    Q R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ source _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_ptr_def])
  >- (pop_assum (strip_assume_tac o
        SIMP_RULE (srw_ss()) [gas_summary_ptr_at_marked]) >> gvs[]
      >~ [`exit_result r`]
      >- (rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `marks` >>
          disj1_tac >> irule gas_summary_ptr_at_bind_exception >>
          metis_tac[]) >>
      irule gas_outcome_ptr_bind_normal >> metis_tac[]) >>
  `ignore_bind (bind source next) (return ()) =
     bind source (\v. ignore_bind (next v) (return ()))` by
    simp[ignore_bind_def, bind_assoc] >>
  asm_rewrite_tac[gas_outcome_ptr_def] >> metis_tac[]
QED
