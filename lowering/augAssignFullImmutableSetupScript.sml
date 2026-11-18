Theory augAssignFullImmutableSetup
Ancestors
  bodySim bodyStorageMetadata exprSimHypsDefs stmtSimAugAssignPlace supportedDecls
  vyperTypeEnv vyperTypeInvariants vyperTypeSystem finite_map list

(* A typed immutable target must be in the assignable bare-global map,
   which is empty outside deployment. *)
Theorem augassign_immutable_in_deploy:
  body_inv tops ctx cenv cx /\
  expr_sim_inv cenv cx env es /\
  supported_immutable_type tops (src,id) = SOME ity /\
  type_stmt env ret_ty
    (AugAssign ty (TopLevelNameTarget (src,id)) bop e) = SOME env'
  ==> cx.in_deploy
Proof
  strip_tac >>
  drule aug_place_typing >> strip_tac >>
  qpat_x_assum `supported_immutable_type _ _ = _` mp_tac >>
  simp[supported_immutable_type_def] >>
  Cases_on `supported_variable_decl tops (src,id)` >> simp[] >>
  rename1 `_ = SOME decl` >> PairCases_on `decl` >>
  Cases_on `decl0` >> Cases_on `decl1` >> Cases_on `decl3` >>
  simp[] >> strip_tac >> gvs[] >>
  drule_then strip_assume_tac supported_variable_decl_mem >> gvs[] >>
  rename1 `supported_value_type tops ity` >>
  `get_module_code cx NONE = SOME tops /\
   bare_globals_complete env.bare_globals cx /\
   bare_global_assignable_complete env.bare_global_assignable cx` by
    fs[body_inv_def, expr_sim_inv_def, env_consistent_def,
       env_context_consistent_def] >>
  `FLOOKUP env.bare_globals (NONE,id) = SOME ity` by
    metis_tac[bare_globals_complete_def] >>
  gvs[type_place_target_TopLevelNameTarget] >>
  spose_not_then assume_tac >>
  fs[bare_global_assignable_complete_def]
QED
