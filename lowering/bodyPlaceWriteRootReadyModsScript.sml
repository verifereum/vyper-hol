(* The write allocation guard selects the actual qualified immutable root. *)
Theory bodyPlaceWriteRootReadyMods
Ancestors
  targetPlaceSim targetPlaceSimCasesBase constSubstCorrect exprBodyPreProps exprSimHypsDefs
  vyperSubscriptOverlap vyperTypeEnv vyperTypeInvariants vyperTypeSystem
  vyperAST compileEnv finite_map list option

Theorem place_write_target_root_access[local]:
  !bt. target_root bt = TopLevelNameTarget key ==>
    MEM (WriteAcc (StateRef key)) (accesses_target bt)
Proof
  recInduct base_assignment_target_induct >>
  simp[target_root_def, accesses_expr_def]
QED

Theorem place_write_typed_root[local]:
  IS_SOME (type_place_target env bt) ==>
  IS_SOME (type_place_target env (target_root bt))
Proof
  `!bt. base_target_root bt = target_root bt` by
    (recInduct base_assignment_target_induct >>
     simp[base_target_root_def, target_root_def]) >>
  strip_tac >> drule_then mp_tac type_place_target_root >> simp[]
QED

Theorem place_write_root_assignable[local]:
  env_consistent env cx es /\
  get_module_code cx owner = SOME ts /\ find_var_decl_by_name id ts = NONE /\
  IS_SOME (type_place_target env (TopLevelNameTarget (owner,id))) ==>
  ?ty. FLOOKUP env.bare_global_assignable (owner,id) = SOME ty
Proof
  strip_tac >>
  qpat_x_assum `IS_SOME (type_place_target _ _)` mp_tac >>
  simp[IS_SOME_EXISTS, type_place_target_TopLevelNameTarget] >> strip_tac
  >- (qexists_tac `ty` >> simp[]) >>
  rename1 `FLOOKUP env.toplevel_vtypes (owner,id) = SOME vt` >>
  Cases_on `vt`
  >- (drule_all_then strip_assume_tac env_consistent_toplevel_storage_static >> gvs[]) >>
  drule_all_then strip_assume_tac env_consistent_toplevel_hashmap_static >> gvs[]
QED

Theorem place_write_allocated_root[local]:
  expr_sim_inv_mods mods cenv cx env es /\
  FLOOKUP env.bare_global_assignable (owner,id) = SOME ty /\
  IS_SOME (FLOOKUP cenv.ce_module_vars (owner,id)) ==>
  cenv.ce_is_ctor /\ ?off. FLOOKUP cenv.ce_module_vars (owner,id) = SOME (ImmutableLoc off)
Proof
  strip_tac >> drule_then assume_tac expr_sim_inv_mods_env >>
  `FLOOKUP env.bare_globals (owner,id) = SOME ty` by
    (fs[env_consistent_def, env_context_consistent_def] >>
     qpat_assum `!src id ty. FLOOKUP env.bare_global_assignable _ = SOME _ ==> _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `cx.in_deploy` by
    (Cases_on `cx.in_deploy` >>
     fs[env_consistent_def, env_context_consistent_def, bare_global_assignable_complete_def]) >>
  qpat_x_assum `expr_sim_inv_mods _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[expr_sim_inv_mods_def]) >>
  conj_tac
  >- (fs[bare_globals_layout_def] >>
      qpat_assum `!src id ty. FLOOKUP env.bare_global_assignable _ = SOME _ ==> _`
        (drule_then assume_tac) >> simp[]) >>
  qpat_assum `!src id ty. FLOOKUP env.bare_globals _ = SOME _ /\ _ ==> _`
    (qspecl_then [`owner`, `id`, `ty`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qpat_x_assum `IS_SOME (FLOOKUP cenv.ce_module_vars _) ==> _`
    (drule_then strip_assume_tac) >>
  qexists_tac `off` >> simp[]
QED

Theorem place_write_stmt_target_typed[local]:
  ((?e. s = Assign (BaseTarget bt) e) \/ (?e. s = Append bt e) \/
   (?ty op e. s = AugAssign ty bt op e)) /\
  type_stmt env ret_ty s = SOME env' ==>
  IS_SOME (type_place_target env bt)
Proof
  strip_tac >>
  Cases_on `type_place_target env bt` >>
  gvs[type_stmt_def, atarget_accepts_def, well_typed_target_def]
QED

Theorem place_write_immutable_root_ready_mods:
  ((?e. s = Assign (BaseTarget bt) e) \/ (?e. s = Append bt e) \/
   (?ty op e. s = AugAssign ty bt op e)) /\
  type_stmt env ret_ty s = SOME env' /\
  expr_sim_inv_mods mods cenv cx env es /\
  (!key. MEM (WriteAcc (StateRef key)) (accesses_stmt s) /\
         IS_SOME (FLOOKUP env.bare_global_assignable key) ==>
         IS_SOME (FLOOKUP cenv.ce_module_vars key)) ==>
  (immutable_root cx bt ==>
   ?owner id off. target_root bt = TopLevelNameTarget (owner,id) /\
     cenv.ce_is_ctor /\ FLOOKUP cenv.ce_module_vars (owner,id) = SOME (ImmutableLoc off))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then assume_tac place_write_stmt_target_typed >>
  drule_then assume_tac place_write_typed_root >>
  disch_then (strip_assume_tac o REWRITE_RULE[immutable_root_def]) >>
  `IS_SOME (type_place_target env (TopLevelNameTarget (src,id)))` by fs[] >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_all_then (qx_choose_then `ty` assume_tac) place_write_root_assignable >>
  `MEM (WriteAcc (StateRef (src,id))) (accesses_stmt s)` by
    (drule_then assume_tac place_write_target_root_access >>
     qpat_x_assum `(?e. s = Assign (BaseTarget bt) e) \/ _` strip_assume_tac >>
     fs[accesses_stmt_def, accesses_atarget_def]) >>
  `IS_SOME (FLOOKUP cenv.ce_module_vars (src,id))` by
    (qpat_assum `!key. MEM (WriteAcc (StateRef key)) _ /\ _ ==> _`
       (qspec_then `(src,id)` mp_tac) >> simp[]) >>
  drule_all_then strip_assume_tac place_write_allocated_root >>
  qexistsl_tac [`src`, `id`, `off`] >> simp[]
QED
