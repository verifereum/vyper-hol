(* Transport the compiler's source invariant through effect-free evaluation. *)
Theory bodyIntCallJointPureSourceInv
Ancestors
  bodyIntCallJointPureSource exprSimHypsDefs vyperTypeEnvPreservation
  vyperEvalOutcomeSuffix exprOracleStorageInterfaces vyperCallOutcomeStorage
  vyperStorageLayoutSafety vyperLookupStorage vyperStorageBackend vyperState
  vyperTypeInvariants

Theorem effect_free_eval_expr_sim_inv:
  expr_sim_inv ce cx env es /\ ~expr_has_effect e /\
  eval_expr cx e es = (res,ee) ==> expr_sim_inv ce cx env ee
Proof
  strip_tac >>
  `ee with <|gas_obs := []; outcomes := NONE|> =
   es with <|gas_obs := []; outcomes := NONE|>` by
    (drule_all effect_free_eval_expr_frame >> simp[]) >>
  `outcome_suffix es.outcomes ee.outcomes` by
    (metis_tac[eval_outcome_suffix_mutual]) >>
  `env_consistent env cx ee` by
    (irule eval_expr_preserves_ec >>
     qexistsl [`e`, `res`, `es`] >> gvs[expr_sim_inv_def]) >>
  `contract_storage_well_formed cx ee` by
    (irule contract_storage_well_formed_storage_frame >>
     qexists `es` >> gvs[expr_sim_inv_def, get_storage_def,
                         evaluation_state_component_equality] >>
     Cases_on `b` >> simp[get_storage_def]) >>
  gvs[expr_sim_inv_def, state_well_typed_def,
      evaluation_state_component_equality] >>
  rpt conj_tac
  >- metis_tac[]
  >- (gvs[outcomes_accounts_typed_def] >>
      metis_tac[outcome_suffix_EVERY])
  >- (irule outcome_suffix_IS_SOME >> qexists `es.outcomes` >> simp[])
  >- (irule oracle_storage_ok_suffix >> qexists `es` >> simp[]) >>
  metis_tac[]
QED
