Theory bodyFullForIteratorRoot
Ancestors
  bodySim bodyStorageMetadata exprSimHypsDefs supportedExprs
  supportedExprForms supportedDecls supportedExprTraverse targetPlaceSim
  gasContext constSubst vyperAST list
  bodyTypedTargetScope vyperTypeSystem vyperTypeInvariants finite_map pair
  vyperTypeContract[qualified,ignore_grammar]
  bodyInvSplit[qualified] bodyInvCodeProps entryStateRel[qualified]
  vyperTypeInitialState[qualified]

Theorem loop_iterator_root_occurs[local]:
  !e t nid.
    loop_iterator_place e = SOME t /\ target_root t = TopLevelNameTarget nid ==>
    !p. (!ty. p (TopLevelName ty nid)) ==> supported_expr_exists p e
Proof
  measureInduct_on `expr_size e` >> Cases_on `e` >>
  simp[vyperTypeContractTheory.loop_iterator_place_def, target_root_def, expr_size_def,
    supported_expr_exists_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[target_root_def] >>
  first_x_assum (qspec_then `e'` mp_tac) >>
  simp[expr_size_def] >> metis_tac[]
QED

Theorem supported_iterator_place_root[local]:
  !e t nid.
    (supported_place_expr tops e \/ supported_effect_place_expr tops e) /\
    loop_iterator_place e = SOME t /\ target_root t = TopLevelNameTarget nid ==>
    supported_place_root tops nid
Proof
  measureInduct_on `expr_size e` >> Cases_on `e` >>
  simp[vyperTypeContractTheory.loop_iterator_place_def, target_root_def, expr_size_def, AllCaseEqs()] >>
  simp[supportedExprsTheory.supported_pure_expr_def,
       supportedExprsTheory.supported_effect_expr_def] >>
  rpt strip_tac >> gvs[target_root_def] >>
  first_x_assum (qspec_then `e'` mp_tac) >>
  simp[expr_size_def] >> metis_tac[]
QED

Theorem nested_iterator_supported_root[local]:
  supported_expr tops e /\ (~(?ty nid. e = TopLevelName ty nid)) /\
  loop_iterator_place e = SOME t /\ target_root t = TopLevelNameTarget nid ==>
  supported_place_root tops nid
Proof
  Cases_on `e` >>
  simp[vyperTypeContractTheory.loop_iterator_place_def, target_root_def, AllCaseEqs()] >>
  simp[supported_expr_def, supportedExprsTheory.supported_pure_expr_def,
       supportedExprsTheory.supported_effect_expr_def] >>
  rpt strip_tac >> gvs[target_root_def] >>
  metis_tac[supported_iterator_place_root]
QED

Theorem iterator_constant_decl_member[local]:
  !tops acc id vis e ty slot. MEM (VariableDecl vis (Constant e) id ty slot) tops ==>
    MEM id (MAP FST (module_consts_env tops acc))
Proof
  recInduct module_consts_env_ind >> simp[module_consts_env_def] >>
  rpt strip_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac `module_consts_env rest acc'` >>
  qspecl_then [`rest`, `acc'`] strip_assume_tac module_consts_env_acc_prefix >>
  simp[Abbr `acc'`] >>
  first_x_assum (drule_then mp_tac) >> simp[]
QED

Triviality typed_iterator_root_declared:
  !e t nid.
    (well_typed_expr env e \/ IS_SOME (type_place_expr env e)) /\
    loop_iterator_place e = SOME t /\ target_root t = TopLevelNameTarget nid ==>
    IS_SOME (FLOOKUP env.bare_globals nid) \/
    IS_SOME (FLOOKUP env.toplevel_vtypes nid)
Proof
  measureInduct_on `expr_size e` >> Cases_on `e` >>
  simp[vyperTypeContractTheory.loop_iterator_place_def, target_root_def,
       well_typed_expr_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[target_root_def, optionTheory.IS_SOME_EXISTS, AllCaseEqs()]
  >~ [`FLOOKUP env.bare_globals p`]
  >- (PairCases_on `p` >>
      gvs[well_typed_expr_def, AllCaseEqs()] >> metis_tac[])
  >~ [`FLOOKUP env.bare_globals p`]
  >- (PairCases_on `p` >>
      gvs[well_typed_expr_def, AllCaseEqs()] >> metis_tac[]) >>
  first_x_assum (qspec_then `e'` mp_tac) >>
  simp[expr_size_def] >> metis_tac[]
QED

Theorem supported_nested_iterator_root_kind:
  contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env es /\
  well_typed_expr env e /\ ~supported_expr_exists (const_name_root_mods mods) e /\
  loop_iterator_place e = SOME t /\ target_root t = TopLevelNameTarget (src,id) ==>
  ?ts. ALOOKUP mods src = SOME ts /\
    (is_immutable_decl id ts \/
     (?tr ty slot.
        find_var_decl_by_name id ts = SOME (StorageVarDecl tr ty,id) /\
        lookup_var_slot_from_layout cx tr src id = SOME slot) \/
     (?tr kt vt slot.
        find_var_decl_by_name id ts = SOME (HashMapVarDecl tr kt vt,id) /\
        lookup_var_slot_from_layout cx tr src id = SOME slot))
Proof
  strip_tac >>
  `env_context_consistent env cx` by
    fs[expr_sim_inv_mods_def, env_consistent_def] >>
  Cases_on `FLOOKUP env.bare_globals (src,id)`
  >- suspend "storage"
  >> suspend "declared"
QED

Resume supported_nested_iterator_root_kind[storage]:
  `?vt. FLOOKUP env.toplevel_vtypes (src,id) = SOME vt` by
    (qspecl_then [`e`,`t`,`(src,id)`] mp_tac typed_iterator_root_declared >>
     simp[optionTheory.IS_SOME_EXISTS]) >>
  rename1 `FLOOKUP env.toplevel_vtypes (src,id) = SOME vt` >>
  drule_then (assume_tac o Q.SPEC `src`) contract_inv_module_codes >>
  Cases_on `vt` >>
  fs[env_context_consistent_def, optionTheory.IS_SOME_EXISTS]
  >- (qpat_assum `!src id ty. _ /\ _ ==> ?ts tr id_str.
          _ /\ find_var_decl_by_name _ _ = SOME (StorageVarDecl _ _,_) /\ _`
        (drule_all_then strip_assume_tac) >>
      drule_then (assume_tac o CONJUNCT1) entryStateRelTheory.find_var_decl_by_name_mem >>
      gvs[] >> metis_tac[]) >>
  qpat_assum `!src id kt vt. _ ==> ?ts tr id_str.
       _ /\ find_var_decl_by_name _ _ = SOME (HashMapVarDecl _ _ _,_) /\ _`
    (drule_then strip_assume_tac) >>
  metis_tac[entryStateRelTheory.find_var_decl_by_name_mem]
QED

Resume supported_nested_iterator_root_kind[declared]:
  gvs[optionTheory.IS_SOME_EXISTS] >>
  drule_all_then strip_assume_tac env_context_consistent_bare_global_find_NONE >>
  drule_then (assume_tac o Q.SPEC `src`) contract_inv_module_codes >>
  `ALOOKUP mods src = SOME ts` by metis_tac[] >>
  qexists_tac `ts` >> simp[] >>
  drule_then strip_assume_tac vyperTypeInitialStateTheory.is_bare_global_decl_cases
  >- (gvs[] >>
      `supported_expr_exists (const_name_root_mods mods) e` by
        (mp_tac (Q.SPECL [`e`,`t`,`(src,id)`] loop_iterator_root_occurs) >>
         (impl_tac >- simp[]) >>
         disch_then (qspec_then `const_name_root_mods mods` irule) >>
         simp[const_name_root_mods_def,cx_const_name_mods_def] >>
         irule iterator_constant_decl_member >> goal_assum (drule_at Any)) >>
      gvs[]) >>
  simp[]
QED

Finalise supported_nested_iterator_root_kind

Theorem singleton_supported_nested_iterator_root_kind:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  well_typed_expr env e /\ supported_expr tops e /\
  ~supported_expr_exists (const_name_root cx) e /\
  (~(?ty nid. e = TopLevelName ty nid)) /\
  loop_iterator_place e = SOME t /\ target_root t = TopLevelNameTarget nid ==>
  IS_SOME (supported_immutable_type tops nid) \/
  (?vis kind ty slot.
     supported_variable_decl tops nid = SOME (vis,kind,ty,SOME slot) /\
     (kind = Storage \/ kind = Transient)) \/
  (?vis transient kt vt slot.
     supported_hashmap_decl tops nid = SOME (vis,transient,kt,vt,SOME slot))
Proof
  strip_tac >>
  `FST nid = NONE` by
    (PairCases_on `nid` >> Cases_on `nid0` >> simp[] >>
     `env_consistent env cx es` by fs[expr_sim_inv_def] >>
     `?ts. get_module_code cx (SOME x) = SOME ts` by
       (irule typed_toplevel_lookup_module >>
        metis_tac[typed_iterator_root_declared]) >>
     drule_then assume_tac body_inv_qualified_module_absent >> gvs[]) >>
  drule_all nested_iterator_supported_root >> strip_tac >>
  `~cx_const_name cx nid` by
    (strip_tac >>
     qspecl_then [`e`,`t`,`nid`] mp_tac loop_iterator_root_occurs >>
     (impl_tac >- simp[]) >>
     disch_then (qspec_then `const_name_root cx` mp_tac) >>
     simp[const_name_root_def]) >>
  Cases_on `supported_variable_decl tops nid`
  >- (Cases_on `supported_hashmap_decl tops nid` >>
      gvs[supported_place_root_def] >>
      PairCases_on `x` >> Cases_on `x4` >> gvs[supported_place_root_def]) >>
  PairCases_on `x` >> Cases_on `x1` >> Cases_on `x3` >>
  gvs[supported_place_root_def, supported_immutable_type_def] >>
  PairCases_on `nid` >>
  drule supported_variable_decl_mem >> strip_tac >> gvs[] >>
  `cx_tops cx = tops` by
    (fs[body_inv_def] >> metis_tac[cx_tops_module]) >>
  fs[cx_const_name_def] >> metis_tac[iterator_constant_decl_member]
QED
