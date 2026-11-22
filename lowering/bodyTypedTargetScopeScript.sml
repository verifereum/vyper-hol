(* Resolve a typed top-level target in the source unit that owns it. *)
Theory bodyTypedTargetScope
Ancestors
  bodyInvCodeProps bodySim exprSimHypsDefs targetPlaceSim
  vyperTypeEnv vyperTypeInvariants vyperTypeSystem vyperContext vyperAST
  alist finite_map option pair

Theorem typed_toplevel_target_module:
  expr_sim_inv_mods mods cenv cx env es /\
  type_place_target env (TopLevelNameTarget (src,id)) = SOME vt ==>
  ?tops. get_module_code cx src = SOME tops
Proof
  strip_tac >>
  `env_consistent env cx es` by fs[expr_sim_inv_mods_def] >>
  fs[type_place_target_TopLevelNameTarget]
  >- (fs[env_consistent_def, env_context_consistent_def] >> res_tac >> simp[]) >>
  Cases_on `vt` >>
  metis_tac[env_consistent_toplevel_storage_static, env_consistent_toplevel_hashmap_static]
QED

Theorem body_inv_qualified_module_absent:
  body_inv tops ctx cenv cx ==> !src. get_module_code cx (SOME src) = NONE
Proof
  strip_tac >> drule body_inv_contract >>
  drule_then assume_tac contract_inv_module_codes >> fs[ALOOKUP_def]
QED

Theorem body_inv_toplevel_target_main:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  IS_SOME (type_place_target env (TopLevelNameTarget (src,id))) ==>
  src = NONE
Proof
  strip_tac >> Cases_on `src` >> simp[] >>
  drule_then assume_tac body_inv_qualified_module_absent >>
  fs[expr_sim_inv_split_def, IS_SOME_EXISTS] >>
  metis_tac[typed_toplevel_target_module, NOT_SOME_NONE]
QED

Theorem body_inv_immutable_target_main:
  body_inv tops ctx cenv cx /\ immutable_root cx t /\
  target_root t = TopLevelNameTarget (src,id) ==>
  src = NONE
Proof
  strip_tac >> Cases_on `src` >> simp[] >>
  drule_then assume_tac body_inv_qualified_module_absent >>
  fs[immutable_root_def] >> metis_tac[NOT_SOME_NONE]
QED
