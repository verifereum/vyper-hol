Theory augAssignFullImmutableSetup
Ancestors
  bodySim bodyInvCodeProps exprBodyPreProps alist bodyStorageMetadata exprSimHypsDefs stmtSimAugAssignPlace supportedDecls
  vyperTypeEnv vyperTypeInvariants vyperTypeSystem finite_map list

(* A typed immutable target must be in the assignable bare-global map,
   which is empty outside deployment. *)
Theorem augassign_immutable_place_mods:
  contract_inv mods exps ctx cenv cx /\ ALOOKUP mods src = SOME tops /\
  expr_sim_inv_mods mods cenv cx env es /\
  supported_immutable_type tops (NONE,id) = SOME ity /\
  type_stmt env ret_ty
    (AugAssign ty (TopLevelNameTarget (src,id)) bop e) = SOME env'
  ==> cx.in_deploy /\ FLOOKUP env.bare_globals (src,id) = SOME ity /\
      FLOOKUP env.bare_global_assignable (src,id) = SOME ity
Proof
  strip_tac >>
  drule aug_place_typing >> strip_tac >>
  qpat_x_assum `supported_immutable_type _ _ = _` mp_tac >>
  simp[supported_immutable_type_def, AllCaseEqs()] >> strip_tac >>
  drule_then strip_assume_tac supported_variable_decl_mem >> gvs[] >>
  `get_module_code cx src = SOME tops` by metis_tac[contract_inv_module_codes] >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  `bare_globals_complete env.bare_globals cx /\
   bare_global_assignable_complete env.bare_global_assignable cx` by
    fs[env_consistent_def, env_context_consistent_def] >>
  `FLOOKUP env.bare_globals (src,id) = SOME ity` by
    metis_tac[bare_globals_complete_def] >>
  `cx.in_deploy` by
    (gvs[type_place_target_TopLevelNameTarget] >>
     spose_not_then assume_tac >> fs[bare_global_assignable_complete_def]) >>
  simp[] >> metis_tac[bare_global_assignable_complete_def]
QED

Theorem augassign_immutable_in_deploy_mods:
  contract_inv mods exps ctx cenv cx /\ ALOOKUP mods src = SOME tops /\
  expr_sim_inv_mods mods cenv cx env es /\
  supported_immutable_type tops (NONE,id) = SOME ity /\
  type_stmt env ret_ty
    (AugAssign ty (TopLevelNameTarget (src,id)) bop e) = SOME env'
  ==> cx.in_deploy
Proof
  metis_tac[augassign_immutable_place_mods]
QED

Theorem augassign_immutable_in_deploy:
  body_inv tops ctx cenv cx /\
  expr_sim_inv cenv cx env es /\
  supported_immutable_type tops (src,id) = SOME ity /\
  type_stmt env ret_ty
    (AugAssign ty (TopLevelNameTarget (src,id)) bop e) = SOME env'
  ==> cx.in_deploy
Proof
  strip_tac >>
  `src = NONE` by
    (spose_not_then assume_tac >>
     drule_then strip_assume_tac supported_lookup_other_module >>
     fs[supported_immutable_type_def]) >>
  gvs[] >>
  drule_then strip_assume_tac body_inv_main_code >>
  drule_then assume_tac body_inv_contract >>
  fs[expr_sim_inv_split_def] >>
  irule (SIMP_RULE (srw_ss()) [ALOOKUP_def] (Q.INST
    [`mods` |-> `[(NONE,tops)]`, `src` |-> `NONE`, `exps` |-> `[]`]
    (SPEC_ALL augassign_immutable_in_deploy_mods))) >> simp[] >> metis_tac[]
QED
