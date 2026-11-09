(* Sequential source evaluation keeps one origin/memory/pointer witness. *)
Theory gasOutcomeFullCompose
Ancestors
  gasOutcomeFull fragGasOriginPtr fragGasOrigin gasOutcome gasExemptCert
  gasSummaryCompose gasSummary fragGasPathPtr fragGasMode
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
