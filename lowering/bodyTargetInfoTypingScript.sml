Theory bodyTargetInfoTyping
Ancestors
  bodyAugPlaceTarget whitelistVisibility entryReachBodySourceSupport
  targetStorageDomain vyperTypeInvariants vyperTypeSystem exprSimHypsDefs
  bodySim supportedTargets supportedTypes supportedProgram supportedDecls supportedExprForms

Theorem target_decl_typing[local]:
  env_context_consistent env cx /\
  get_module_code cx src = SOME tops /\
  find_var_decl_by_name id tops = SOME (decl,key) /\
  type_place_target env (TopLevelNameTarget (src,id)) = SOME vt ==>
  vt = (case decl of StorageVarDecl tr ty => Type ty
       | HashMapVarDecl tr kt value => HashMapT kt value)
Proof
  simp[Once well_typed_expr_def] >> rpt strip_tac >>
  Cases_on `vt` >>
  gvs[AllCaseEqs(), env_context_consistent_def]
  >~ [`FLOOKUP env.bare_global_assignable (src,id) = SOME _`] >- (
    qpat_x_assum `!src id ty. FLOOKUP _.bare_global_assignable _ = SOME _ ==> _`
      drule >> strip_tac >> gvs[]) 
  >~ [`FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type t)`] >- (
    qpat_x_assum `!src id ty. _ /\ _ ==> _` drule_all >>
    strip_tac >> gvs[]) >>
  qpat_x_assum `!src id kt vt. FLOOKUP _ _ = SOME (HashMapT _ _) ==> _`
    drule >> strip_tac >> gvs[]
QED

Theorem supported_root_typing[local]:
  body_inv tops ctx cenv cx /\ env_context_consistent env cx /\
  supported_target_info tops bindings (TopLevelNameTarget nid) = SOME pt /\
  type_place_target env (TopLevelNameTarget nid) = SOME vt ==>
  vt = (case pt of ValPT ty => Type ty | MapPT kt value => HashMapT kt value)
Proof
  Cases_on `nid` >> rpt strip_tac >>
  gvs[supported_target_info_def, AllCaseEqs()]
  >~ [`supported_hashmap_decl tops _ = SOME _`] >- (
    drule aug_place_hashmap_build >> strip_tac >> gvs[] >>
    `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
     get_module_code cx NONE = SOME tops` by gvs[body_inv_def] >>
    `supported_program tops` by gvs[body_inv_def] >>
    `EVERY (supported_declaration_header tops) tops` by
      gvs[supported_program_def, supported_declaration_headers_def] >>
    drule_all supported_hashmap_decl_header >> strip_tac >>
    gvs[optionTheory.IS_SOME_EXISTS] >>
    drule_all supported_hashmap_decl_storage_binding >> strip_tac >>
    drule_all target_decl_typing >> simp[]) >>
  gvs[supported_place_root_def, optionTheory.option_case_compute] >>
  rename1 `supported_variable_decl tops _ = SOME (_,mut,_,slot)` >>
  Cases_on `mut` >> gvs[] >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
   get_module_code cx NONE = SOME tops` by gvs[body_inv_def] >>
  gvs[optionTheory.IS_SOME_EXISTS] >>
  drule supported_variable_decl_storage_binding >> simp[] >>
  disch_then drule >> strip_tac >> gvs[] >>
  drule_all target_decl_typing >> simp[]
QED

Theorem body_type_env_lookup[local]:
  body_inv tops ctx cenv cx /\ FLOOKUP (type_env tops) key = SOME value ==>
  FLOOKUP (get_tenv cx) key = SOME value
Proof
  rpt strip_tac >>
  `get_module_code cx NONE = SOME tops /\
   (!src ts. get_module_code cx src = SOME ts ==> src = NONE)` by
    gvs[body_inv_def] >>
  Cases_on `ALOOKUP cx.sources cx.txn.target` >>
  gvs[vyperContextTheory.get_module_code_def] >>
  Cases_on `x` >> gvs[] >> PairCases_on `h` >>
  qpat_x_assum `!src ts. ALOOKUP _ src = SOME ts ==> src = NONE`
    (qspecl_then [`h0`, `h1`] mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  simp[vyperContextTheory.get_tenv_def, vyperContextTheory.type_env_all_modules_def,
       GSYM vyperContextTheory.type_env_def, finite_mapTheory.FLOOKUP_FUNION]
QED

Theorem supported_target_info_typing:
  !bt pt vt nid.
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  supported_target_info tops bindings bt = SOME pt /\
  target_root bt = TopLevelNameTarget nid /\
  type_place_target env bt = SOME vt ==>
  vt = (case pt of ValPT ty => Type ty | MapPT kt value => HashMapT kt value)
Proof
  `(!e:expr. T) /\ (!bt. !pt vt nid.
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  supported_target_info tops bindings bt = SOME pt /\
  target_root bt = TopLevelNameTarget nid /\
  type_place_target env bt = SOME vt ==>
  vt = (case pt of ValPT ty => Type ty | MapPT kt value => HashMapT kt value))`
    suffices_by simp[] >>
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >>
  simp[targetPlaceSimTheory.target_root_def] >> rpt strip_tac
  >~ [`type_place_target env (TopLevelNameTarget _) = SOME _`] >- (
    irule supported_root_typing >> goal_assum (drule_at Any) >>
    gvs[expr_sim_inv_def, env_consistent_def] >> metis_tac[]) >>
  gvs[supported_target_info_def, AllCaseEqs()]
  >~ [`type_place_target env (SubscriptTarget bt e) = SOME vt`] >- (
    qpat_x_assum `type_place_target env (SubscriptTarget bt e) = SOME vt` mp_tac >>
    simp[Once well_typed_expr_def] >> strip_tac >> gvs[AllCaseEqs()] >>
    gvs[subscript_vtype_def] >>
    Cases_on `vt` >> gvs[exprLoweringTheory.value_type_place_def])
  >~ [`type_place_target env (SubscriptTarget bt e) = SOME vt`] >- (
    qpat_x_assum `type_place_target env (SubscriptTarget bt e) = SOME vt` mp_tac >>
    simp[Once well_typed_expr_def] >> strip_tac >>
    gvs[AllCaseEqs(), subscript_vtype_def]) >>
  qpat_x_assum `type_place_target env (AttributeTarget bt s) = SOME vt` mp_tac >>
  simp[Once well_typed_expr_def] >> strip_tac >>
  gvs[AllCaseEqs(), attribute_type_def] >>
  `FLOOKUP (type_env tops) id = SOME (StructArgs fields)` by
    simp[GSYM entry_supported_struct_fields] >>
  drule_all body_type_env_lookup >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  strip_tac >> gvs[]
QED
