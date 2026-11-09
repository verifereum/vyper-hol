(* Source invariant at an iteration endpoint, including break. *)
Theory bodyIntCallFamStmtForScope
Ancestors
  bodySimDeclCases bodyExprPreFacts exprSimHypsDefs
  vyperTypeEvalSoundness vyperTypeEnvPreservation vyperTypeInvariants
  vyperTypeSystem vyperTypeExprSoundness vyperTypeStoragePreservation
  vyperEvalOutcomeSuffix stmtPoppedKeys finite_map list
  vyperInterpreter vyperState

Theorem intcall_for_expr_sim_inv_pop:
  !cenv cx env es id fty tyv v ret_ty body env_b r2 es2 sc rest tops
   bindings.
    expr_sim_inv cenv cx env es /\ id NOTIN FDOM env.var_types /\
    evaluate_type (get_tenv cx) fty = SOME tyv /\ value_has_type tyv v /\
    type_stmts (extend_local env id fty F) ret_ty body = SOME env_b /\
    call_evaluation_safe cx (int_calls_stmts body) /\
    eval_stmts cx body
      (es with scopes :=
         (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v;
                           popped := []|>)) :: es.scopes) = (r2, es2) /\
    (r2 = INL () \/ r2 = INR ContinueException \/ r2 = INR BreakException) /\
    es2.scopes = sc :: rest /\
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    supported_stmts tops bindings body ==>
    expr_sim_inv cenv cx env (es2 with scopes := rest)
Proof
  rpt gen_tac >> strip_tac
  >- (metis_tac[expr_sim_inv_for_pop])
  >- (metis_tac[expr_sim_inv_for_pop]) >>
  gvs[] >>
  qmatch_asmsub_abbrev_tac `eval_stmts cx body_stmts pushed` >>
  `env_consistent (extend_local env id fty F) cx pushed` by
    (simp[Abbr `pushed`, scopes_CONS_updated] >>
     irule push_scope_with_var_env_consistent >> fs[expr_sim_inv_def]) >>
  `state_well_typed pushed` by
    (simp[Abbr `pushed`, scopes_CONS_updated] >>
     irule for_pushed_state_well_typed >>
     fs[expr_sim_inv_def] >>
     metis_tac[vyperTypingTheory.evaluate_type_well_formed]) >>
  drule (cj 2 eval_scc_type_sound_mutual) >>
  disch_then (qspecl_then [`cx`, `pushed`, `INR BreakException`, `es2`] mp_tac) >>
  (impl_tac >- fs[expr_sim_inv_def, Abbr `pushed`]) >>
  simp[] >> strip_tac >> suspend "break"
QED

Resume intcall_for_expr_sim_inv_pop[break]:
  `env_consistent env cx (es2 with scopes := rest)` by
    (`rest = TL es2.scopes` by simp[] >> pop_assum SUBST1_TAC >>
     irule for_cons_popped_env_consistent_from_stmt_case >>
     simp[] >> goal_assum (drule_at Any) >>
     fs[expr_sim_inv_def, Abbr `pushed`, scopes_CONS_updated] >>
     metis_tac[]) >>
  `contract_storage_well_formed cx es2 /\ oracle_storage_ok cx es2 /\
   IS_SOME es2.outcomes` by
    (drule (cj 2 eval_stmts_storage_conjs) >>
     disch_then drule >> disch_then drule >>
     disch_then drule >>
     disch_then (qspec_then `pushed` mp_tac) >>
     disch_then (qspecl_then [`INR BreakException`, `es2`] mp_tac) >>
     (impl_tac >- (fs[expr_sim_inv_def, Abbr `pushed`,
       runtime_storage_consistent_def, runtime_consistent_def,
       extend_local_def, scopes_CONS_updated] >>
       irule storage_conjs_scopes >> simp[])) >> simp[]) >>
  `outcomes_accounts_typed es2.outcomes` by
    (rw[outcomes_accounts_typed_def] >>
     drule (cj 2 eval_outcome_suffix_mutual) >> strip_tac >>
     drule_then irule outcome_suffix_EVERY >>
     fs[expr_sim_inv_def, outcomes_accounts_typed_def, Abbr `pushed`]) >>
  suspend "keys"
QED

Resume intcall_for_expr_sim_inv_pop[keys]:
  `popped_keys_indexed pushed.scopes` by
    (fs[Abbr `pushed`, expr_sim_inv_def, popped_keys_indexed_def,
        FLOOKUP_UPDATE, vyperPlaceInvariantsTheory.popped_history_typed_def] >>
     rpt strip_tac >> gvs[]) >>
  `runtime_consistent (extend_local env id fty F) cx pushed` by
    fs[runtime_consistent_def, expr_sim_inv_def, Abbr `pushed`] >>
  `popped_keys_indexed es2.scopes` by
    (fs[expr_sim_inv_def] >>
     drule_all (cj 2 eval_stmts_popped_keys_indexed) >> simp[]) >>
  fs[expr_sim_inv_def, state_well_typed_def, popped_keys_indexed_def] >>
  fs[] >>
  `es2 with scopes := rest = es2 with scopes updated_by (K rest)` by simp[] >>
  pop_assum SUBST1_TAC >>
  qspecl_then [`cx`, `es2`, `K rest`] mp_tac storage_conjs_scopes >>
  (impl_tac >- simp[]) >> simp[] >> strip_tac >>
  qpat_x_assum `es2.scopes = _` (fn th => fs[th]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==> _` drule >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!src id ty. FLOOKUP env.bare_globals (src,id) = SOME ty ==> _` drule >> simp[]
QED

Finalise intcall_for_expr_sim_inv_pop
