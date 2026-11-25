(* A successful memory target is live at the endpoint of the linked run. *)
Theory bodyWritePlaceLiveMods
Ancestors
  bodyWriteArrayMemoryMods bodyWriteTargetStageMods bodyWriteSubscriptSourceMods
  exprBodyPreProps exprSimHypsDefs bodyFullPredsMods loweringPosts
  vyperTypeEnv vyperTypeInvariants vyperTypeSystem vyperInterpreter vyperState
  allocLimits targetPlaceSim exprSimProps option
Libs
  monadsyntax

Theorem write_place_memory_live_mods:
  expr_sim_inv_mods mods cenv cx env es /\
  body_const_cells_agree_mods mods cx env es /\
  alloc_limits_target cenv bt /\
  (!i st. MEM i (target_indices bt) /\ expr_sim_inv_mods mods cenv cx env st ==>
          expr_body_pre_mods mods cenv cx env i st) /\
  type_place_target env bt = SOME (Type ty) /\
  eval_base_place cx bt (es with gas_obs := gs) =
    (INL (PlaceR (MemoryPlace id path)),mid) /\
  write_target_location_mods cenv cx bt mid (PlaceR (MemoryPlace id path))
    (Type ty) r G t ==>
  ?entry v. lookup_scopes id mid.scopes = SOME entry /\
            evaluate_subscripts entry.type entry.value path = INL v
Proof
  strip_tac >>
  `expr_sim_inv_mods mods cenv cx env (es with gas_obs := gs)` by simp[] >>
  `body_const_cells_agree_mods mods cx env (es with gas_obs := gs)` by simp[] >>
  `IS_SOME (type_place_target env bt)` by simp[] >>
  drule_all_then strip_assume_tac write_base_reached_source_mods >>
  qpat_x_assum `write_target_location_mods _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[write_target_location_mods_def, place_ptr_rel_def] >> strip_tac >>
  drule_then strip_assume_tac mem_path_offset_sound >>
  `?entry. lookup_scopes id mid.scopes = SOME entry` by
    (qpat_x_assum `place_readable _ _ _` mp_tac >>
     simp[place_readable_def, read_place_def, get_scopes_def, bind_def,
          lift_option_type_def, lift_sum_def, return_def, raise_def] >>
     Cases_on `lookup_scopes id mid.scopes` >> simp[return_def, raise_def]) >>
  `entry.type = tv0 /\ well_formed_type_value entry.type /\
     value_has_type entry.type entry.value` by
    (qpat_assum `expr_sim_inv_mods _ _ _ _ mid`
       (mp_tac o REWRITE_RULE [expr_sim_inv_mods_def]) >>
     simp[env_consistent_def, env_scopes_consistent_def, IS_SOME_EXISTS] >>
     strip_tac >>
     `?vty. FLOOKUP env.var_types id = SOME vty` by
       (first_assum (drule_then strip_assume_tac) >> simp[]) >>
     `cenv.ce_var_type id = SOME vty` by simp[] >>
     `evaluate_type (get_tenv cx) vty = SOME entry.type` by
       (first_assum (qspecl_then [`id`,`vty`,`entry`] mp_tac) >> simp[]) >>
     gvs[state_well_typed_def] >> drule_all scope_well_typed_lookup_scopes >> simp[]) >>
  `?v. evaluate_subscripts entry.type entry.value path = INL v` by
    (irule write_memory_base_live >>
     qpat_assum `eval_base_place _ _ _ = _` (irule_at Any) >>
     qpat_assum `expr_sim_inv_mods _ _ _ _ es` (irule_at Any) >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  qexistsl_tac [`entry`,`v`] >> simp[]
QED
