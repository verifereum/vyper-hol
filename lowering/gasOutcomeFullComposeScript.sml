(* Sequential source evaluation keeps one origin/memory/pointer witness. *)
Theory gasOutcomeFullCompose
Ancestors
  gasOutcomeFull fragGasOriginPtr fragGasOrigin gasOutcome gasExemptCert
  gasSummaryCompose gasSummary fragGasPathPtr fragGasPathMem fragGasPath
  fragGasMode fragExec bodyDeclMemoryCompose
  vyperInterpreter vyperState venomState list arithmetic

(* The certificate premises are the existing type-specific bind/error
   constructors, as in gas_outcome_ptr_bind. They do not add an oracle
   or execution premise to any source-language theorem. *)
Theorem gas_outcome_full_bind:
  gas_outcome_full (D, lo, explicit, ctx, func, PG) tops source
    (es, s, G, tn)
    (\res mid G1 tn1 t. ?v. res = INL v /\
       gas_outcome_full (D, lo, explicit, ctx, func, PG) tops (next v)
         (mid, t, G1, tn1) Q R)
    (\res ee gt r. ?exc. res = INR exc /\ R (INR exc) ee gt r) /\
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
  gas_outcome_full (D, lo, explicit, ctx, func, PG) tops (bind source next)
    (es, s, G, tn) Q R
Proof
  strip_tac >>
  `ignore_bind (bind source next) (return ()) =
     bind source (\v. ignore_bind (next v) (return ()))` by
    simp[ignore_bind_def, bind_assoc] >>
  qpat_x_assum `gas_outcome_full _ _ source _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_def])
  >- (gvs[] >>
      qpat_x_assum `gas_outcome_full _ _ (next _) _ _ _`
        (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_def])
      >- (gvs[] >>
          `gas_path ctx func s (LENGTH marks) (OK t)` by
            metis_tac[gas_origin_ptr_path_projections,
                      gas_origin_path_erase, gas_marked_path_exec] >>
          drule gas_explicit_append_path >>
          disch_then (qspec_then `marks'` assume_tac) >>
          rewrite_tac[gas_outcome_full_def] >>
          qexists_tac `marks ++ marks'` >> disj1_tac >>
          qexistsl_tac [`res`, `ee'`, `OK t'`, `G''`, `tn''`] >>
          conj_tac
          >- (asm_rewrite_tac[] >> irule gas_source_bind_normal >> simp[] >> metis_tac[]) >>
          conj_tac
          >- (irule gas_origin_ptr_path_append >> metis_tac[]) >>
          metis_tac[])
      >- (gvs[] >>
          `gas_path ctx func s (LENGTH marks) (OK t)` by
            metis_tac[gas_origin_ptr_path_projections,
                      gas_origin_path_erase, gas_marked_path_exec] >>
          drule gas_explicit_append_path >>
          disch_then (qspec_then `marks'` assume_tac) >>
          rewrite_tac[gas_outcome_full_def] >>
          qexists_tac `marks ++ marks'` >> disj1_tac >>
          qexistsl_tac [`res`, `ee'`, `r`, `G''`, `tn''`] >>
          conj_tac
          >- (asm_rewrite_tac[] >> irule gas_source_bind_normal >>
              simp[] >> metis_tac[]) >>
          conj_tac
          >- (irule gas_origin_ptr_path_append >> metis_tac[]) >>
          metis_tac[]) >>
      `gas_marked_exec T (ctx, func) source (es, s) marks (INL v) ee (OK t)` by
        (rewrite_tac[gas_marked_exec_def] >>
         metis_tac[gas_origin_ptr_path_projections, gas_origin_path_erase]) >>
      asm_rewrite_tac[gas_outcome_full_def] >>
      qexists_tac `marks ++ marks'` >> disj2_tac >>
      qexistsl_tac [`err`, `ee'`, `leaf`, `leaf_pg`, `leaf_g`, `leaf_tn`, `finish'`] >>
      conj_tac >- metis_tac[] >>
      irule (cj 2 gas_origin_ptr_focus_rules) >> metis_tac[])
  >- (gvs[] >> rewrite_tac[gas_outcome_full_def] >>
      qexists_tac `marks` >> disj1_tac >>
      qexistsl_tac [`INR exc`, `ee`, `r`, `G'`, `tn'`] >>
      simp[] >> metis_tac[gas_source_bind_exception])
  >> asm_rewrite_tac[gas_outcome_full_def] >> metis_tac[]
QED

(* Generic combinators shared by the full body leaves, which compose through
   these and never unfold gas_outcome_full_def.  Target steps that record no
   GAS site around a joint outcome: a prefix before it, a suffix after its
   normal ending, and a source step that takes no GAS observation. *)

Theorem origin_ptr_path_zero_prefix[local]:
  gas_origin_ptr_path cx st [] (OK s1, G1, tn1) /\
  gas_origin_ptr_path cx (s1, G1, tn1) marks out ==>
  gas_origin_ptr_path cx st marks out
Proof
  PairCases_on `out` >> strip_tac >>
  qpat_x_assum `gas_origin_ptr_path _ _ [] _`
    (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
  simp[] >> disch_then drule >> simp[]
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

Theorem gas_outcome_full_zero_prefix:
  gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
    (s0, G0, tn0) [] (OK s1, G1, tn1) /\
  gas_outcome_full (D, lo, explicit, ctx, func, PG) tops source
    (es, s1, G1, tn1) Q R ==>
  gas_outcome_full (D, lo, explicit, ctx, func, PG) tops source
    (es, s0, G0, tn0) Q R
Proof
  strip_tac >>
  `gas_path_mem ctx func s0 0 (OK s1)` by
    (drule gas_origin_ptr_path_projections >> strip_tac >>
     drule gas_origin_path_erase >> simp[gas_marked_path_def]) >>
  `s1.vs_gas_readings = s0.vs_gas_readings` by
    (drule gas_path_mem_ok_suffix >> simp[]) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_def]) >>
  rewrite_tac[gas_outcome_full_def] >> qexists_tac `marks`
  >- (disj1_tac >> qexistsl_tac [`res`, `ee`, `OK t`, `G'`, `tn'`] >>
      gvs[] >> metis_tac[origin_ptr_path_zero_prefix])
  >- (disj1_tac >> qexistsl_tac [`res`, `ee`, `r`, `G'`, `tn'`] >>
      gvs[] >> metis_tac[origin_ptr_path_zero_prefix]) >>
  disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `leaf_pg`, `leaf_g`, `leaf_tn`,
                `finish'`] >>
  conj_tac >- (irule gas_exempt_cert_zero_prefix_mem >> metis_tac[]) >>
  drule (cj 2 gas_origin_ptr_focus_rules) >> disch_then drule >> simp[]
QED

Theorem gas_outcome_full_zero_suffix:
  gas_outcome_full (D, lo, explicit, ctx, func, PG) tops source
    (es, s, G, tn) Q R /\
  (!res ee G1 tn1 t. Q res ee G1 tn1 t ==>
     ?t' G2 tn2.
       gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
         (t, G1, tn1) [] (OK t', G2, tn2) /\
       Q' res ee G2 tn2 t') ==>
  gas_outcome_full (D, lo, explicit, ctx, func, PG) tops source
    (es, s, G, tn) Q' R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_def]) >>
  rewrite_tac[gas_outcome_full_def] >> qexists_tac `marks`
  >- (first_x_assum drule >> strip_tac >>
      disj1_tac >> qexistsl_tac [`res`, `ee`, `OK t'`, `G2`, `tn2`] >>
      gvs[] >> metis_tac[origin_ptr_path_zero_suffix])
  >- (disj1_tac >> qexistsl_tac [`res`, `ee`, `r`, `G'`, `tn'`] >> gvs[]) >>
  disj2_tac >> metis_tac[]
QED

Theorem gas_outcome_full_pure:
  (!tail. source (es with gas_obs := tail) = (res, ee with gas_obs := tail)) /\
  gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
    (s, G, tn) [] (OK t, G', tn') /\
  Q res (ee with gas_obs := []) G' tn' t ==>
  gas_outcome_full (D, lo, explicit, ctx, func, PG) tops source
    (es, s, G, tn) Q R
Proof
  strip_tac >> rewrite_tac[gas_outcome_full_def] >>
  qexists_tac `[]` >> disj1_tac >>
  qexistsl_tac [`res`, `ee`, `OK t`, `G'`, `tn'`] >> simp[]
QED

(* gas_outcome_full_post_mono, with the source run that reached the
   normal post, its emptied observations and the end state's running
   flag. *)
Theorem gas_outcome_full_post_source:
  gas_outcome_full (D, lo, explicit, ctx, func, PG) tops source
    (es, s, G, tn) Q R /\
  (!res ee G' tn' t.
     (?xs. !tail. source (es with gas_obs := xs ++ tail) =
                  (res, ee with gas_obs := tail)) /\
     ee.gas_obs = [] /\ ~t.vs_halted /\ Q res ee G' tn' t ==>
     Q' res ee G' tn' t) /\
  (!res ee gt r. R res ee gt r ==> R' res ee gt r) ==>
  gas_outcome_full (D, lo, explicit, ctx, func, PG) tops source
    (es, s, G, tn) Q' R'
Proof
  rw[gas_outcome_full_def] >> qexists_tac `marks`
  >- (disj1_tac >> qexistsl_tac [`res`, `ee`, `OK t`, `G'`, `tn'`] >>
      simp[] >> disj1_tac >> first_x_assum irule >> simp[] >>
      rpt conj_tac
      >~ [`~t.vs_halted`]
      >- metis_tac[gas_origin_ptr_path_projections, gas_origin_path_erase,
                   gas_marked_path_exec, gas_path_normal] >>
      qexists_tac `gas_explicit marks s.vs_gas_readings` >> simp[])
  >- (disj1_tac >> metis_tac[]) >>
  disj2_tac >> metis_tac[]
QED

Theorem gas_outcome_full_zero_suffix_mono:
  gas_outcome_full (D, lo, explicit, ctx, func, PG) tops source
    (es, s, G, tn) Q R /\
  (!res ee G1 tn1 t. Q res ee G1 tn1 t ==>
     ?u G2 tn2.
       gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
         (t, G1, tn1) [] (OK u, G2, tn2) /\
       Q' res ee G2 tn2 u) /\
  (!res ee gt r. R res ee gt r ==> R' res ee gt r) ==>
  gas_outcome_full (D, lo, explicit, ctx, func, PG) tops source
    (es, s, G, tn) Q' R'
Proof
  strip_tac >> drule_all gas_outcome_full_zero_suffix >> strip_tac >>
  drule gas_outcome_full_post_mono >> disch_then irule >>
  conj_tac >- simp[] >> first_assum ACCEPT_TAC
QED

Theorem gas_outcome_full_bind_lands:
  gas_outcome_full (D, lo, explicit, ctx, func, PG) tops source
    (es, s, G, tn)
    (\res mid G1 tn1 t.
       (?v. res = INL v /\
          gas_outcome_full (D, lo, explicit, ctx, func, PG) tops (next v)
            (mid, t, G1, tn1) Q R) \/
       (?exc. res = INR exc /\ Q (INR exc) mid G1 tn1 t))
    (\res ee gt r. ?exc. res = INR exc /\ R (INR exc) ee gt r) /\
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
  gas_outcome_full (D, lo, explicit, ctx, func, PG) tops (bind source next)
    (es, s, G, tn) Q R
Proof
  strip_tac >>
  `ignore_bind (bind source next) (return ()) =
     bind source (\v. ignore_bind (next v) (return ()))` by
    simp[ignore_bind_def, bind_assoc] >>
  qpat_x_assum `gas_outcome_full _ _ source _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_def])
  >- (gvs[]
      >- (qpat_x_assum `gas_outcome_full _ _ (next _) _ _ _`
        (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_def])
      >- (gvs[] >>
          `gas_path ctx func s (LENGTH marks) (OK t)` by
            metis_tac[gas_origin_ptr_path_projections,
                      gas_origin_path_erase, gas_marked_path_exec] >>
          drule gas_explicit_append_path >>
          disch_then (qspec_then `marks'` assume_tac) >>
          rewrite_tac[gas_outcome_full_def] >>
          qexists_tac `marks ++ marks'` >> disj1_tac >>
          qexistsl_tac [`res`, `ee'`, `OK t'`, `G''`, `tn''`] >>
          conj_tac
          >- (asm_rewrite_tac[] >> irule gas_source_bind_normal >> simp[] >>
              metis_tac[]) >>
          conj_tac
          >- (irule gas_origin_ptr_path_append >> metis_tac[]) >>
          metis_tac[])
      >- (gvs[] >>
          `gas_path ctx func s (LENGTH marks) (OK t)` by
            metis_tac[gas_origin_ptr_path_projections,
                      gas_origin_path_erase, gas_marked_path_exec] >>
          drule gas_explicit_append_path >>
          disch_then (qspec_then `marks'` assume_tac) >>
          rewrite_tac[gas_outcome_full_def] >>
          qexists_tac `marks ++ marks'` >> disj1_tac >>
          qexistsl_tac [`res`, `ee'`, `r`, `G''`, `tn''`] >>
          conj_tac
          >- (asm_rewrite_tac[] >> irule gas_source_bind_normal >>
              simp[] >> metis_tac[]) >>
          conj_tac
          >- (irule gas_origin_ptr_path_append >> metis_tac[]) >>
          metis_tac[]) >>
      `gas_marked_exec T (ctx, func) source (es, s) marks (INL v) ee (OK t)` by
        (rewrite_tac[gas_marked_exec_def] >>
         metis_tac[gas_origin_ptr_path_projections, gas_origin_path_erase]) >>
      asm_rewrite_tac[gas_outcome_full_def] >>
      qexists_tac `marks ++ marks'` >> disj2_tac >>
      qexistsl_tac [`err`, `ee'`, `leaf`, `leaf_pg`, `leaf_g`, `leaf_tn`,
                    `finish'`] >>
      conj_tac >- metis_tac[] >>
      irule (cj 2 gas_origin_ptr_focus_rules) >> metis_tac[]) >>
      rewrite_tac[gas_outcome_full_def] >>
      qexists_tac `marks` >> disj1_tac >>
      qexistsl_tac [`INR exc`, `ee`, `OK t`, `G'`, `tn'`] >>
      simp[] >> metis_tac[gas_source_bind_exception])
  >- (gvs[] >> rewrite_tac[gas_outcome_full_def] >>
      qexists_tac `marks` >> disj1_tac >>
      qexistsl_tac [`INR exc`, `ee`, `r`, `G'`, `tn'`] >>
      simp[] >> metis_tac[gas_source_bind_exception])
  >> asm_rewrite_tac[gas_outcome_full_def] >> metis_tac[]
QED
