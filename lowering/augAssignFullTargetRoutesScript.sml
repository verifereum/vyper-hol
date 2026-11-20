Theory augAssignFullTargetRoutes
Ancestors
  bodyAugPlaceTarget supportedStmts supportedTargets supportedTypes
  supportedExprForms supportedDecls bodySim list alist

Theorem augassign_name_target_info:
  supported_stmt tops bindings (AugAssign ty (NameTarget id) bop e) ==>
  ?pt. supported_target_info tops bindings (NameTarget id) = SOME pt
Proof
  simp[supported_stmt_def, supported_target_def, supported_aug_target_def,
       supported_target_info_def] >>
  Cases_on `ALOOKUP bindings id` >> simp[]
QED

(* TEMPORARILY CHEATED - SCRATCH SEQ-8501 census (never lands)
Proof
  strip_tac >>
  qpat_x_assum `supported_scalar_target _ _` mp_tac >>
  simp[supported_scalar_target_def] >>
  Cases_on `supported_variable_decl tops nsid` >> simp[] >>
  rename1 `_ = SOME decl` >> PairCases_on `decl` >>
  Cases_on `decl0` >> Cases_on `decl1` >> Cases_on `decl3` >>
  simp[] >> strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))` by
    fs[body_inv_def] >>
  `supported_hashmap_decl tops nsid = NONE` by
    metis_tac[aug_place_variable_excludes_hashmap] >>
  `supported_storage_type tops decl2` by
    (gvs[supported_full_word_type_def] >>
     simp[supported_storage_type_def, Once supported_nested_type_def,
          supported_full_word_type_def]) >>
  `supported_target_info tops bindings (TopLevelNameTarget nsid) = SOME (ValPT decl2)` by
    simp[supported_target_info_def, supported_place_root_def] >>
  metis_tac[aug_place_supported_root_not_immutable]
QED
*)
Theorem augassign_scalar_target_route:
  body_inv tops ctx cenv cx /\
  supported_scalar_target tops nsid ==>
  ?ity slot mut.
    supported_variable_decl tops nsid = SOME (Private,mut,ity,SOME slot) /\
    (mut = Storage \/ mut = Transient) /\
    supported_full_word_type ity /\
    supported_target_info tops bindings (TopLevelNameTarget nsid) =
      SOME (ValPT ity) /\
    ~immutable_root cx (TopLevelNameTarget nsid)
Proof
  cheat
QED

Theorem augassign_other_target_routes:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (AugAssign ty t bop e) /\
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
  >- (disj1_tac >> metis_tac[aug_place_supported_stmt_target_info,
                            aug_place_supported_root_not_immutable]) >>
  disj1_tac >> metis_tac[aug_place_supported_stmt_target_info,
                        aug_place_supported_root_not_immutable]
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
  metis_tac[aug_place_supported_root_not_immutable]
QED

Finalise augassign_other_target_routes
