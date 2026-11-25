Theory augAssignFullTargetRoutes
Ancestors
  bodyTypedTargetScope bodyInvCodeProps moduleVariableKeyProps linkedStorageMetadataProps
  bodyAugPlaceTarget supportedStmts supportedTargets supportedTypes
  supportedExprForms supportedDecls bodySim targetPlaceSim list alist
  exprSimHypsDefs vyperTypeSystem

Theorem augassign_name_target_info:
  supported_stmt tops bindings (AugAssign ty (NameTarget id) bop e) ==>
  ?pt. supported_target_info tops bindings (NameTarget id) = SOME pt
Proof
  simp[supported_stmt_def, supported_target_def, supported_aug_target_def,
       supported_target_info_def] >>
  Cases_on `ALOOKUP bindings id` >> simp[]
QED

Theorem augassign_scalar_target_route_mods:
  contract_inv mods exps ctx cenv cx /\ ALOOKUP mods src = SOME tops /\
  supported_scalar_target tops (NONE,id) ==>
  ?vis ity slot mut.
    supported_variable_decl tops (NONE,id) = SOME (vis,mut,ity,SOME slot) /\
    (mut = Storage \/ mut = Transient) /\
    supported_target_info tops bindings (TopLevelNameTarget (NONE,id)) =
      SOME (ValPT ity) /\
    ~immutable_root cx (TopLevelNameTarget (src,id))
Proof
  strip_tac >>
  drule_then assume_tac contract_inv_module_codes >>
  drule_all_then assume_tac contract_inv_unqualified_variable_keys >>
  Cases_on `supported_variable_decl tops (NONE,id)` >>
  gvs[supported_scalar_target_def] >>
  rename1 `SOME decl` >> PairCases_on `decl` >>
  Cases_on `decl3` >> Cases_on `decl1` >> gvs[] >>
  `IS_SOME (find_var_decl_by_name id tops)` by
    (irule aug_place_supported_root_decl >> metis_tac[]) >>
  drule_all_then strip_assume_tac aug_place_variable_excludes_hashmap >>
  gvs[supported_target_info_def, supportedExprFormsTheory.supported_place_root_def,
      immutable_root_def, target_root_def, optionTheory.IS_SOME_EXISTS]
QED

Theorem augassign_scalar_target_route:
  body_inv tops ctx cenv cx /\ FST nsid = NONE /\
  supported_scalar_target tops nsid ==>
  ?vis ity slot mut.
    supported_variable_decl tops nsid = SOME (vis,mut,ity,SOME slot) /\
    (mut = Storage \/ mut = Transient) /\
    supported_target_info tops bindings (TopLevelNameTarget nsid) =
      SOME (ValPT ity) /\
    ~immutable_root cx (TopLevelNameTarget nsid)
Proof
  PairCases_on `nsid` >> strip_tac >>
  gvs[] >> drule_then assume_tac body_inv_contract >>
  mp_tac (Q.INST [`mods` |-> `[(NONE,tops)]`, `exps` |-> `[]`,
                  `ctx` |-> `ctx`, `src` |-> `NONE`, `id` |-> `nsid1`]
          augassign_scalar_target_route_mods) >> simp[ALOOKUP_def]
QED

Theorem augassign_other_target_routes:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (AugAssign ty t bop e) /\
  expr_sim_inv cenv cx env es /\ target_mutable env t /\
  (immutable_root cx t ==> ?nsid. t = TopLevelNameTarget nsid) /\
  ~(?id. t = NameTarget id) /\
  ~(?nsid. t = TopLevelNameTarget nsid /\ supported_scalar_target tops nsid) /\
  ~(?id fld. t = AttributeTarget (NameTarget id) fld) /\
  ~(?nsid fld. t = AttributeTarget (TopLevelNameTarget nsid) fld /\
               supported_storage_field_write tops nsid fld) ==>
  ((?pt. supported_target_info tops bindings t = SOME pt) /\
   ~immutable_root cx t) \/
  (?nsid ity. t = TopLevelNameTarget nsid /\
             supported_immutable_type tops nsid = SOME ity)
Proof
  rpt strip_tac >>
  Cases_on `t`
  >- gvs[]
  >- suspend "toplevel"
  >- (disj1_tac >> gvs[] >> metis_tac[aug_place_supported_stmt_target_info]) >>
  disj1_tac >> gvs[] >> metis_tac[aug_place_supported_stmt_target_info]
QED

Resume augassign_other_target_routes[toplevel]:
  rename1 `TopLevelNameTarget nsid` >>
  qpat_x_assum `supported_stmt _ _ _` mp_tac >>
  simp[Once supported_stmt_def, supported_target_def] >>
  rpt strip_tac
  >- gvs[]
  >- (disj2_tac >> Cases_on `supported_immutable_type tops nsid` >> gvs[]) >>
  disj1_tac >>
  `?pt. supported_target_info tops bindings (TopLevelNameTarget nsid) = SOME pt` by
    (Cases_on `supported_target_info tops bindings (TopLevelNameTarget nsid)` >>
     gvs[supported_aug_target_def]) >>
  metis_tac[aug_place_supported_toplevel_mutable]
QED

Finalise augassign_other_target_routes
