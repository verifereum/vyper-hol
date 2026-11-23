(* Resolve a typed top-level target in the source unit that owns it. *)
Theory bodyTypedTargetScope
Ancestors
  bodyInvCodeProps bodySim exprSimHypsDefs targetPlaceSim
  vyperTypeEnv vyperTypeInvariants vyperTypeSystem vyperContext vyperAST
  alist finite_map option pair

Theorem typed_toplevel_lookup_module:
  env_consistent env cx es /\
  (IS_SOME (FLOOKUP env.bare_globals (src,id)) \/
   IS_SOME (FLOOKUP env.toplevel_vtypes (src,id))) ==>
  ?tops. get_module_code cx src = SOME tops
Proof
  strip_tac
  >- (fs[IS_SOME_EXISTS] >>
      drule_all_then strip_assume_tac env_consistent_bare_global_find_NONE >>
      simp[]) >>
  fs[IS_SOME_EXISTS] >>
  rename1 `FLOOKUP env.toplevel_vtypes (src,id) = SOME vt` >>
  Cases_on `FLOOKUP env.bare_globals (src,id)` >>
  Cases_on `vt` >>
  metis_tac[env_consistent_bare_global_find_NONE,
            env_consistent_toplevel_storage_static,
            env_consistent_toplevel_hashmap_static]
QED

Theorem typed_toplevel_target_module:
  expr_sim_inv_mods mods cenv cx env es /\
  type_place_target env (TopLevelNameTarget (src,id)) = SOME vt ==>
  ?tops. get_module_code cx src = SOME tops
Proof
  strip_tac >>
  `env_consistent env cx es` by fs[expr_sim_inv_mods_def] >>
  fs[type_place_target_TopLevelNameTarget]
  >- (fs[env_consistent_def, env_context_consistent_def] >> res_tac >> simp[]) >>
  metis_tac[typed_toplevel_lookup_module, IS_SOME_EXISTS]
QED

Theorem body_inv_qualified_module_absent:
  body_inv tops ctx cenv cx ==> !src. get_module_code cx (SOME src) = NONE
Proof
  strip_tac >> drule_then assume_tac body_inv_contract >>
  drule contract_inv_module_codes >> simp[ALOOKUP_def]
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

Theorem body_inv_toplevel_read_main:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  well_typed_expr env (TopLevelName ty (src,id)) ==>
  src = NONE
Proof
  strip_tac >> Cases_on `src` >> simp[] >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  `?ts. get_module_code cx (SOME x) = SOME ts` by
    (irule typed_toplevel_lookup_module >>
     fs[well_typed_expr_def, IS_SOME_EXISTS] >> metis_tac[]) >>
  drule_then assume_tac body_inv_qualified_module_absent >> gvs[]
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
