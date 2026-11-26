(* Scope cleanup for the selected arm of a linked If. *)
Theory gasOutcomeIfScopeMods
Ancestors
  gasOutcomeFullMods stmtSimIfProps gasExemptCertMods gasSummaryCompose
  gasSummary gasStorage fragGasOriginPtr fragGasOrigin vyperEvalPreservesScopes
  vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperState list

Theorem gas_bad_storage_at_finally[local]:
  gas_bad_storage_at cx st0 f es s0 marks /\ storage_trace_frame g ==>
  gas_bad_storage_at cx st0 (finally f g) es s0 marks
Proof
  rewrite_tac[gas_bad_storage_at_def] >> strip_tac >> gen_tac >>
  first_x_assum (qspec_then `tail` mp_tac) >>
  qmatch_goalsub_abbrev_tac `finally f g esx` >>
  Cases_on `f esx` >> rename1 `f esx = (res, ee)` >>
  Cases_on `res` >> asm_simp_tac (srw_ss()) [finally_def] >> strip_tac >>
  qmatch_goalsub_abbrev_tac `SND (h ee)` >>
  `storage_trace_frame h` by
    simp[Abbr `h`, storage_trace_frame_ignore_bind,
         storage_trace_frame_return, storage_trace_frame_raise] >>
  Cases_on `h ee` >> simp[] >>
  metis_tac[storage_trace_frame_preserves_bad_domain]
QED

Theorem scope_cleanup_bad_storage[local]:
  gas_bad_storage_at cx st0 (eval_stmts cx ss)
    (es with scopes := FEMPTY :: es.scopes) s0 marks /\ ~s0.vs_halted ==>
  gas_bad_storage_at cx st0
    (ignore_bind push_scope (finally (eval_stmts cx ss) pop_scope))
    es s0 marks
Proof
  strip_tac >>
  `gas_marked_exec T (ARB, ARB) push_scope (es, s0) [] (INL ())
     (es with scopes := FEMPTY :: es.scopes) (OK s0)` by
    simp[if_push_scope_marked] >>
  simp[ignore_bind_def] >>
  `marks = [] ++ marks` by simp[] >> pop_assum SUBST1_TAC >>
  irule gas_bad_storage_at_bind_right >>
  first_assum (irule_at Any) >> simp[] >>
  irule gas_bad_storage_at_finally >>
  fs[gas_bad_storage_at_def, storage_trace_frame_pop_scope]
QED

Theorem if_branch_cert_scopes_mods[local]:
  !memory mods ctx func cx ss es s0 marks err ee leaf finish.
  gas_exempt_cert_mods memory mods (ctx,func)
    (ignore_bind (eval_stmts cx ss) (return ()))
    (es with scopes := FEMPTY :: es.scopes,s0)
    marks (err,ee) (leaf,finish) ==>
  ?top rest. ee.scopes = top :: rest
Proof
  rpt strip_tac >> drule gas_exempt_cert_execution_mods >> strip_tac >>
  qpat_x_assum `!tail. ignore_bind _ _ _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE std_ss [APPEND_NIL])) >>
  drule vyperStatePreservationTheory.ignore_bind_split >>
  simp[return_def] >> strip_tac >>
  drule eval_stmts_preserves_scopes_len >> simp[] >>
  Cases_on `ee.scopes` >> simp[]
QED

Theorem if_branch_cert_cleanup_mods[local]:
  !memory mods ctx func cx ss es s0 marks err ee leaf finish top rest.
  gas_exempt_cert_mods memory mods (ctx,func)
    (ignore_bind (eval_stmts cx ss) (return ()))
    (es with scopes := FEMPTY :: es.scopes,s0) marks (err,ee) (leaf,finish) /\
  ee.scopes = top :: rest /\ es.gas_obs = [] /\ ~s0.vs_halted ==>
  gas_exempt_cert_mods memory mods (ctx,func)
    (ignore_bind (ignore_bind push_scope
       (finally (eval_stmts cx ss) pop_scope)) (return ()))
    (es,s0) marks (err,ee with scopes := rest) (leaf,finish)
Proof
  rpt strip_tac >>
  `gas_marked_exec memory (ctx,func) push_scope (es,s0) [] (INL ())
     (es with scopes := FEMPTY :: es.scopes) (OK s0)` by
    simp[if_push_scope_marked] >>
  rewrite_tac[ignore_bind_def, bind_assoc] >>
  drule gas_exempt_cert_mods_bind_unit >> simp[] >>
  disch_then irule >>
  rewrite_tac[GSYM ignore_bind_def, ignore_bind_finally_unit] >>
  irule gas_exempt_cert_mods_cleanup >> qexists_tac `ee` >>
  conj_tac >- simp[pop_scope_def, return_def, evaluation_state_component_equality] >>
  `es with <|scopes := FEMPTY :: es.scopes; gas_obs := []|> =
   es with scopes := FEMPTY :: es.scopes` by
    simp[evaluation_state_component_equality] >>
  simp[]
QED

Theorem gas_outcome_full_mods_scope_cleanup:
  gas_outcome_full_mods (DF, lo, explicit, ctx, func, PG) mods cx st0
    (eval_stmts cx ss)
    (es with scopes := FEMPTY :: es.scopes, s0, G0, tn0) Q R /\
  es.gas_obs = [] /\ ~s0.vs_halted ==>
  gas_outcome_full_mods (DF, lo, explicit, ctx, func, PG) mods cx st0
    (ignore_bind push_scope (finally (eval_stmts cx ss) pop_scope))
    (es, s0, G0, tn0)
    (\H res ee G tn t. ?sc.
       Q H res (ee with scopes := sc :: ee.scopes) G tn t /\
       !n. n IN FDOM sc ==> lookup_scopes n ee.scopes = NONE)
    (\H res ee gt r. ?sc. R H res (ee with scopes := sc :: ee.scopes) gt r)
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_mods_def])
  >~ [`gas_bad_storage_at _ _ _ _ _ _`]
  >- (rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks` >>
      disj1_tac >> conj_tac >- (irule scope_cleanup_bad_storage >> simp[]) >>
      fs[] >> metis_tac[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (drule if_branch_cert_scopes_mods >> strip_tac >>
      rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks` >>
      disj2_tac >> disj2_tac >>
      qexistsl_tac [`err`, `ee with scopes := rest`, `leaf`, `leaf_pg`,
                    `leaf_g`, `leaf_tn`, `finish'`] >>
      (conj_tac >- (irule if_branch_cert_cleanup_mods >> metis_tac[])) >>
      qexists_tac `H` >> fs[]) >>
  rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks` >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace)
     ee.storage_trace` by fs[storage_trace_domain_def] >>
  `gas_marked_exec T (ctx, func) (eval_stmts cx ss)
     (es with scopes := FEMPTY :: es.scopes, s0) marks res ee r` by
    (rewrite_tac[gas_marked_exec_def] >>
     metis_tac[gas_origin_ptr_path_projections, gas_origin_path_erase]) >>
  drule if_branch_marked_scopes >> strip_tac >>
  drule_all if_branch_marked_cleanup >> strip_tac >>
  disj2_tac >> disj1_tac >>
  qexistsl_tac [`res`, `ee with scopes := rest`, `r`, `G'`, `tn'`] >>
  conj_tac >- fs[gas_marked_exec_def] >>
  conj_tac >- fs[] >>
  rpt strip_tac >> fs[] >> res_tac >>
  `ee with gas_obs := [] =
   (ee with <|scopes := rest; gas_obs := []|>) with scopes := sc :: rest` by
    simp[evaluation_state_component_equality] >>
  pop_assum (fn th => RULE_ASSUM_TAC (ONCE_REWRITE_RULE [th])) >>
  fs[] >> metis_tac[]
QED
