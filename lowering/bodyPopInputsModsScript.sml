(* Static inputs for simulating a linked Pop target. *)
Theory bodyPopInputsMods
Ancestors
  popTargetPre exprBodyPreProps exprSimHypsDefs targetPlaceSim allocLimits
  vyperTypeAssignContext vyperTypeEnv vyperTypeInvariants vyperInterpreter
  vyperContext vyperAST compileEnv finite_map

Theorem pop_target_root_assignable[local]:
  env_context_consistent env cx /\
  type_place_target env bt = SOME vt /\
  target_root bt = TopLevelNameTarget (src,id) /\
  get_module_code cx src = SOME tops /\ find_var_decl_by_name id tops = NONE ==>
  ?ty. FLOOKUP env.bare_global_assignable (src,id) = SOME ty /\
       FLOOKUP env.bare_globals (src,id) = SOME ty
Proof
  strip_tac >>
  `?rt. type_place_target env (TopLevelNameTarget (src,id)) = SOME rt` by
    (Cases_on `type_place_target env (TopLevelNameTarget (src,id))` >> simp[] >>
     `type_place_target env bt = NONE` by (irule target_root_untyped >> simp[]) >>
     fs[]) >>
  fs[type_place_target_TopLevelNameTarget] >-
    (qpat_x_assum `env_context_consistent _ _`
       (strip_assume_tac o REWRITE_RULE [env_context_consistent_def]) >>
     qpat_assum `!a b t. FLOOKUP env.bare_global_assignable (a,b) = _ ==> _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `env_context_consistent _ _`
    (strip_assume_tac o REWRITE_RULE [env_context_consistent_def]) >>
  Cases_on `rt` >> gvs[]
  >- (qpat_assum `!a b t. FLOOKUP env.toplevel_vtypes (a,b) = SOME (Type t) /\ _ ==> _`
        (drule_all_then strip_assume_tac) >> gvs[]) >>
  qpat_assum `!a b k t. FLOOKUP env.toplevel_vtypes (a,b) = SOME (HashMapT k t) ==> _`
    (drule_then strip_assume_tac) >> gvs[]
QED

Theorem pop_immutable_root_excluded_mods[local]:
  expr_body_pre_mods mods cenv cx env (Pop ann bt) es /\
  type_place_target env bt = SOME vt ==> ~immutable_root cx bt
Proof
  simp[immutable_root_def] >> rpt strip_tac >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then (strip_assume_tac o REWRITE_RULE [env_consistent_def])
    expr_sim_inv_mods_env >>
  drule_all_then strip_assume_tac pop_target_root_assignable >>
  `IS_SOME (FLOOKUP env.bare_global_assignable (src,id))` by simp[] >>
  drule_all_then assume_tac pop_target_root_allocated_mods >>
  qpat_x_assum `expr_sim_inv_mods _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_sim_inv_mods_def]) >>
  qpat_assum `!a b ty. FLOOKUP env.bare_globals (a,b) = _ /\ _ ==> _`
    (qspecl_then [`src`,`id`,`ty`] mp_tac) >> (impl_tac >- simp[]) >>
  strip_tac >>
  qpat_assum `IS_SOME (FLOOKUP cenv.ce_module_vars _) ==> _`
    (drule_then strip_assume_tac) >>
  `target_in_immutables cenv.ce_module_vars bt` by
    (simp[target_in_immutables_root] >> qexists_tac `off` >> simp[]) >>
  fs[expr_body_pre_mods_def, alloc_limits_expr_def]
QED

Theorem pop_target_inputs_mods:
  expr_body_pre_mods mods cenv cx env (Pop ann bt) es ==>
  (?n. type_place_target env bt = SOME (Type (ArrayT ann (Dynamic n)))) /\
  ~immutable_root cx bt /\ expr_sim_inv_mods mods cenv cx env es /\
  alloc_limits_target cenv bt /\
  (!e st. MEM e (target_indices bt) /\ expr_sim_inv_mods mods cenv cx env st ==>
          expr_body_pre_mods mods cenv cx env e st)
Proof
  strip_tac >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_then strip_assume_tac well_typed_expr_Pop_dynamic_target >>
  drule_all_then assume_tac pop_immutable_root_excluded_mods >>
  drule_all_then strip_assume_tac target_pre_of_pop_mods >>
  simp[]
QED
