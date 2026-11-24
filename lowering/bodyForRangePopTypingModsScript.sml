(* Source typing for resuming a linked loop after its iteration scope is popped. *)
Theory bodyForRangePopTypingMods
Ancestors
  bodyExprPreFacts exprSimHypsDefs vyperEvalPreservesScopes vyperEvalOutcomeSuffix
  vyperTypeEnvPreservation vyperTypeEvalSoundness vyperTypeEvalProofs
  vyperTypeScopePop vyperTypeEnvExtension vyperTypeInvariants vyperTypeExprSoundness
  vyperTypeValues vyperInterpreter vyperState finite_map list

val _ = Parse.hide "body";

Theorem range_typed_pop[local]:
  expr_sim_inv_mods mods cenv cx env es /\ id NOTIN FDOM env.var_types /\
  evaluate_type (get_tenv cx) fty = SOME tyv /\ value_has_type tyv v /\
  type_stmts (extend_local env id fty F) ret_ty body = SOME env_b /\
  call_evaluation_safe cx (int_calls_stmts body) /\
  eval_stmts cx body
    (es with scopes updated_by
       CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v;
                             popped := []|>))) = (raw,pre) /\
  pre.scopes = sc :: rest /\ (raw = INL () \/ raw = INR ContinueException) ==>
  expr_sim_inv_mods mods cenv cx env (pre with scopes := rest)
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  qpat_x_assum `expr_sim_inv_mods _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_sim_inv_mods_def]) >>
  `well_formed_type_value tyv` by
    (irule evaluate_type_well_formed_type_value >> metis_tac[]) >>
  qabbrev_tac `pushed = es with scopes updated_by
      CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v;
                            popped := []|>))` >>
  `env_consistent (extend_local env id fty F) cx pushed` by
    (simp[Abbr `pushed`] >> irule push_scope_with_var_env_consistent >> simp[]) >>
  `state_well_typed pushed` by
    (simp[Abbr `pushed`] >> irule for_pushed_state_well_typed >> simp[]) >>
  `accounts_well_typed pushed.accounts` by simp[Abbr `pushed`] >>
  drule_all (cj 2 eval_scc_type_sound_mutual) >> strip_tac >>
  `env_maps_wf env` by metis_tac[env_consistent_env_maps_wf] >>
  `env_consistent env cx (pre with scopes := TL pre.scopes)` by
    (qpat_x_assum `_ \/ _` strip_assume_tac >> rpt BasicProvers.VAR_EQ_TAC >>
     qpat_x_assum `sum_CASE _ _ _` mp_tac >> simp_tac (srw_ss()) [] >>
     strip_tac >> unabbrev_all_tac
     >- (irule for_body_env_consistent_after_pop >> metis_tac[]) >>
     irule for_body_env_extends_consistent_after_pop >> metis_tac[]) >>
  `state_well_typed (pre with scopes := TL pre.scopes)` by
    (irule scope_bracket_preserves_swt >> fs[Abbr `pushed`] >> metis_tac[]) >>
  `outcome_suffix pushed.outcomes pre.outcomes` by
    drule_then ACCEPT_TAC (cj 2 eval_outcome_suffix_mutual) >>
  `outcomes_accounts_typed pre.outcomes` by
    (rw[outcomes_accounts_typed_def] >> drule_then irule outcome_suffix_EVERY >>
     fs[outcomes_accounts_typed_def, Abbr `pushed`]) >>
  `IS_SOME pre.outcomes` by
    (drule_then mp_tac outcome_suffix_modes >>
     fs[Abbr `pushed`, optionTheory.IS_SOME_EQ_NOT_NONE]) >>
  `runtime_consistent (extend_local env id fty F) cx pushed` by simp[runtime_consistent_def] >>
  `popped_keys_indexed pushed.scopes` by
    (fs[Abbr `pushed`, popped_keys_indexed_def, FLOOKUP_UPDATE] >>
     rw[] >> gvs[]) >>
  drule_all_then assume_tac (cj 2 eval_stmts_popped_keys_indexed) >>
  `popped_keys_indexed rest` by gvs[popped_keys_indexed_def] >>
  qpat_x_assum `pre.scopes = _` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th, TL])) >>
  ASM_REWRITE_TAC [expr_sim_inv_mods_def] >> simp[]
QED

Theorem range_pop_gas_obs[local]:
  expr_sim_inv_mods mods cenv cx env (es with gas_obs := gs) <=>
  expr_sim_inv_mods mods cenv cx env es
Proof
  simp[expr_sim_inv_mods_def]
QED

Theorem range_body_pop_typing_mods:
  expr_sim_inv_mods mods cenv cx env es /\ lookup_scopes id es.scopes = NONE /\
  id NOTIN FDOM env.var_types /\
  evaluate_type (get_tenv cx) fty = SOME tyv /\ value_has_type tyv v /\
  type_stmts (extend_local env id fty F) ret_ty body = SOME env_b /\
  call_evaluation_safe cx (int_calls_stmts body) /\
  eval_stmts cx body
    ((es with scopes :=
       (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v;
                         popped := []|>)) :: es.scopes) with gas_obs := gs) = (raw,pre) /\
  pre.scopes = sc :: rest /\ (raw = INL () \/ raw = INR ContinueException) ==>
  expr_sim_inv_mods mods cenv cx env (pre with scopes := rest) /\
  lookup_scopes id rest = NONE
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >> conj_tac
  >- (qabbrev_tac `binding =
        FEMPTY |+ (id, <|assignable := F; type := tyv; value := v; popped := []|>)` >>
      `((es with scopes := binding :: es.scopes) with gas_obs := gs) =
       (es with gas_obs := gs) with scopes updated_by CONS binding` by
        simp[evaluation_state_component_equality] >>
      `expr_sim_inv_mods mods cenv cx env (es with gas_obs := gs)` by
        simp[range_pop_gas_obs] >>
      qpat_x_assum `_ with gas_obs := _ = _` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
      unabbrev_all_tac >>
      drule_all range_typed_pop >> simp[]) >>
  drule eval_stmts_preserves_scopes_dom >> simp[preserves_scopes_dom_def] >>
  strip_tac >> irule lookup_scopes_none_map_fdom >>
  qexists_tac `es.scopes` >> simp[]
QED
