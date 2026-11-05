(* Proof interfaces for declaration-order constant inlining. *)
Theory constSubstCorrect
Ancestors
  constSubst vyperTypeConstantFold vyperAST vyperTypeContractContext
  vyperState vyperValue vyperContext vyperTypeInvariants vyperInterpreter
  vyperMisc vyperTyping vyperTypeValues
  vyperPlaceFrames vyperStatePreservation
  vyperImmutablesPreservation vyperScopePreservation vyperCallOutcomeFrame
  vyperCreateFrame vyperCallFrame vyperMachineFrame
  vyperTypeContract vyperTypeContractStaticMaps vyperTypeSystem finite_map alist list

Definition const_local_refs_def:
  const_local_refs (TopLevelName ty ns) =
    (case ns of (NONE,id) => [(ty,id)] | _ => []) /\
  const_local_refs (StructLit ty ns fs) = const_local_fields fs /\
  const_local_refs (Subscript ty a b) = const_local_refs a ++ const_local_refs b /\
  const_local_refs (Attribute ty a id) = const_local_refs a /\
  const_local_refs (Builtin ty bi es) = const_local_exprs es /\
  const_local_refs (TypeBuiltin ty bi t es) = const_local_exprs es /\
  const_local_refs e = [] /\
  const_local_exprs [] = [] /\
  const_local_exprs (e::es) = const_local_refs e ++ const_local_exprs es /\
  const_local_fields [] = [] /\
  const_local_fields ((id,e)::fs) = const_local_refs e ++ const_local_fields fs
Termination
  WF_REL_TAC `measure (\x. case x of
      INL e => expr_size e
    | INR (INL es) => list_size expr_size es
    | INR (INR fs) => list_size (pair_size (list_size char_size) expr_size) fs)` >>
  simp[expr_size_def, list_size_def, basicSizeTheory.pair_size_def]
End

Definition const_acc_agrees_def:
  const_acc_agrees mods imms E A <=>
    ALL_DISTINCT (MAP FST E) /\ set (MAP FST E) = FDOM A /\
    (!id r. ALOOKUP E id = SOME r ==>
      constant_expr mods r /\ const_local_refs r = [] /\
      ?tv v. FLOOKUP A id = SOME (tv,v) /\
        evaluate_type (type_env_all_modules mods) (expr_type r) = SOME tv /\
        constant_value mods imms r = SOME v)
End

Theorem const_local_exprs_map:
  const_local_exprs es = FLAT (MAP const_local_refs es)
Proof
  Induct_on `es` >> simp[const_local_refs_def]
QED

Theorem const_local_fields_map:
  const_local_fields fs = const_local_exprs (MAP SND fs)
Proof
  Induct_on `fs` >> simp[const_local_refs_def] >> Cases_on `h` >>
  simp[const_local_refs_def]
QED

Theorem fold_const_builtin_constant:
  constant_builtin bi /\ EVERY (constant_expr mods) es ==>
  constant_expr mods (fold_const_builtin ty bi es)
Proof
  strip_tac >> Cases_on `bi` >>
  gvs[fold_const_builtin_def, constant_expr_def, SF ETA_ss] >>
  Cases_on `es` >> gvs[constant_expr_def, SF ETA_ss] >>
  Cases_on `t` >> gvs[constant_expr_def, SF ETA_ss] >>
  Cases_on `h` >> gvs[constant_expr_def, SF ETA_ss] >>
  rename1 `Literal aty l` >> Cases_on `l` >>
  gvs[constant_expr_def, SF ETA_ss]
QED

Theorem fold_const_expr_constant:
  (!e. constant_expr mods e ==> constant_expr mods (fold_const_expr e)) /\
  (!es. EVERY (constant_expr mods) es ==>
    EVERY (constant_expr mods) (fold_const_exprs es)) /\
  (!fs. EVERY (constant_expr mods) (MAP SND fs) ==>
    EVERY (constant_expr mods) (MAP SND (fold_const_fields fs)))
Proof
  ho_match_mp_tac const_local_refs_ind >>
  simp[constant_expr_def, fold_const_expr_def, SF ETA_ss] >>
  rpt strip_tac >> irule fold_const_builtin_constant >> simp[]
QED

Theorem fold_const_builtin_value:
  constant_value mods imms (fold_const_builtin ty bi es) =
  constant_value mods imms (Builtin ty bi es)
Proof
  Cases_on `bi` >> simp[fold_const_builtin_def] >>
  Cases_on `es` >> simp[] >> Cases_on `t` >> simp[] >>
  Cases_on `h` >> simp[] >> rename1 `Literal aty l` >>
  Cases_on `l` >> simp[constant_value_def, constant_builtin_def,
    builtin_args_length_ok_def, vyperValueOperationTheory.evaluate_literal_def, evaluate_builtin_def,
    expr_type_def]
QED

Theorem fold_const_expr_value_aux[local]:
  (!e. constant_expr mods e ==>
    constant_value mods imms (fold_const_expr e) = constant_value mods imms e) /\
  (!es. EVERY (constant_expr mods) es ==>
    MAP expr_type (fold_const_exprs es) = MAP expr_type es /\
    constant_values mods imms (fold_const_exprs es) = constant_values mods imms es /\
    LENGTH (fold_const_exprs es) = LENGTH es) /\
  (!fs. EVERY (constant_expr mods) (MAP SND fs) ==>
    MAP FST (fold_const_fields fs) = MAP FST fs /\
    constant_values mods imms (MAP SND (fold_const_fields fs)) =
      constant_values mods imms (MAP SND fs))
Proof
  ho_match_mp_tac const_local_refs_ind >>
  simp[constant_expr_def, fold_const_expr_def, constant_value_def,
       fold_const_builtin_value, SF ETA_ss] >>
  rpt strip_tac >> gvs[]
QED

Theorem fold_const_expr_value:
  constant_expr mods e ==>
  constant_value mods imms (fold_const_expr e) = constant_value mods imms e
Proof
  metis_tac[fold_const_expr_value_aux]
QED

Theorem fold_const_builtin_local_closed:
  const_local_exprs es = [] ==>
  const_local_refs (fold_const_builtin ty bi es) = []
Proof
  strip_tac >> Cases_on `bi` >>
  gvs[fold_const_builtin_def, const_local_refs_def] >>
  Cases_on `es` >> gvs[const_local_refs_def] >>
  Cases_on `t` >> gvs[const_local_refs_def] >>
  Cases_on `h` >> gvs[const_local_refs_def] >>
  rename1 `Literal aty l` >> Cases_on `l` >> gvs[const_local_refs_def]
QED

Theorem fold_const_expr_local_closed:
  (!e. const_local_refs e = [] ==>
    const_local_refs (fold_const_expr e) = []) /\
  (!es. const_local_exprs es = [] ==>
    const_local_exprs (fold_const_exprs es) = []) /\
  (!fs. const_local_fields fs = [] ==>
    const_local_fields (fold_const_fields fs) = [])
Proof
  ho_match_mp_tac const_local_refs_ind >>
  simp[const_local_refs_def, fold_const_expr_def] >>
  rpt strip_tac >> irule fold_const_builtin_local_closed >> simp[]
QED

Theorem subst_consts_expr_type_constant:
  constant_expr mods e /\
  (!ty id r. MEM (ty,id) (const_local_refs e) /\ ALOOKUP E id = SOME r ==>
    expr_type r = ty) ==>
  expr_type (subst_consts_expr E e) = expr_type e
Proof
  Cases_on `e` >> simp[subst_consts_expr_def, constant_expr_def, expr_type_def] >>
  rename1 `TopLevelName ty ns` >> PairCases_on `ns` >> Cases_on `ns0` >>
  simp[subst_consts_expr_def, expr_type_def, const_local_refs_def] >>
  rpt strip_tac >> Cases_on `ALOOKUP E ns1` >> gvs[expr_type_def]
QED

Definition const_replacements_ok_def:
  const_replacements_ok mods imms E refs <=>
    !ty id r. MEM (ty,id) refs /\ ALOOKUP E id = SOME r ==>
      expr_type r = ty /\ constant_expr mods r /\
      constant_value mods imms r = constant_value mods imms (TopLevelName ty (NONE,id))
End

Theorem const_replacements_ok_append[simp]:
  const_replacements_ok mods imms E (a ++ b) <=>
  const_replacements_ok mods imms E a /\ const_replacements_ok mods imms E b
Proof
  simp[const_replacements_ok_def] >> metis_tac[]
QED

Theorem const_subst_constant_value:
  (!e. !E. constant_expr mods e /\
      const_replacements_ok mods imms E (const_local_refs e) ==>
    expr_type (subst_consts_expr E e) = expr_type e /\
    constant_expr mods (subst_consts_expr E e) /\
    constant_value mods imms (subst_consts_expr E e) = constant_value mods imms e) /\
  (!es. !E. EVERY (constant_expr mods) es /\
      const_replacements_ok mods imms E (const_local_exprs es) ==>
    MAP expr_type (subst_consts_exprs E es) = MAP expr_type es /\
    EVERY (constant_expr mods) (subst_consts_exprs E es) /\
    constant_values mods imms (subst_consts_exprs E es) = constant_values mods imms es /\
    LENGTH (subst_consts_exprs E es) = LENGTH es) /\
  (!fs. !E. EVERY (constant_expr mods) (MAP SND fs) /\
      const_replacements_ok mods imms E (const_local_fields fs) ==>
    MAP FST (subst_consts_fields E fs) = MAP FST fs /\
    EVERY (constant_expr mods) (MAP SND (subst_consts_fields E fs)) /\
    constant_values mods imms (MAP SND (subst_consts_fields E fs)) =
      constant_values mods imms (MAP SND fs))
Proof
  ho_match_mp_tac const_local_refs_ind >>
  simp[const_local_refs_def, constant_expr_def, subst_consts_expr_def,
       constant_value_def, expr_type_def] >>
  rpt strip_tac >> gvs[SF ETA_ss] >>
  rename1 `TopLevelName ty ns` >> PairCases_on `ns` >> Cases_on `ns0` >>
  gvs[subst_consts_expr_def, const_local_refs_def, const_replacements_ok_def,
      expr_type_def] >>
  Cases_on `ALOOKUP E ns1` >> gvs[expr_type_def]
QED

Theorem const_subst_expr_value:
  constant_expr mods e /\ const_replacements_ok mods imms E (const_local_refs e) ==>
  constant_value mods imms (subst_consts_expr E e) = constant_value mods imms e
Proof
  metis_tac[const_subst_constant_value]
QED

Theorem const_subst_expr_annotation:
  constant_expr mods e /\ const_replacements_ok mods imms E (const_local_refs e) ==>
  expr_type (subst_consts_expr E e) = expr_type e
Proof
  metis_tac[const_subst_constant_value]
QED

Theorem const_subst_expr_constant:
  constant_expr mods e /\ const_replacements_ok mods imms E (const_local_refs e) ==>
  constant_expr mods (subst_consts_expr E e)
Proof
  metis_tac[const_subst_constant_value]
QED

Theorem constant_value_local_closed:
  (!e. !imms imms'. constant_expr mods e /\ const_local_refs e = [] /\
    (!src. IS_SOME src ==> get_source_immutables src imms = get_source_immutables src imms') ==>
    constant_value mods imms e = constant_value mods imms' e) /\
  (!es. !imms imms'. EVERY (constant_expr mods) es /\ const_local_exprs es = [] /\
    (!src. IS_SOME src ==> get_source_immutables src imms = get_source_immutables src imms') ==>
    constant_values mods imms es = constant_values mods imms' es) /\
  (!fs. !imms imms'. EVERY (constant_expr mods) (MAP SND fs) /\ const_local_fields fs = [] /\
    (!src. IS_SOME src ==> get_source_immutables src imms = get_source_immutables src imms') ==>
    constant_values mods imms (MAP SND fs) = constant_values mods imms' (MAP SND fs))
Proof
  ho_match_mp_tac const_local_refs_ind >>
  simp[const_local_refs_def, constant_expr_def, constant_value_def] >>
  rpt strip_tac >> gvs[SF ETA_ss] >>
  rpt (first_x_assum (qspecl_then [`imms`,`imms'`] assume_tac)) >>
  gvs[] >>
  rename1 `TopLevelName ty ns` >> PairCases_on `ns` >> Cases_on `ns0` >>
  gvs[const_local_refs_def, constant_value_def]
QED

Theorem constant_value_closed_stable:
  constant_expr mods e /\ const_local_refs e = [] /\
  (!src. IS_SOME src ==> get_source_immutables src imms = get_source_immutables src imms') ==>
  constant_value mods imms e = constant_value mods imms' e
Proof
  metis_tac[constant_value_local_closed]
QED


Definition const_decl_names_def:
  const_decl_names [] = [] /\
  const_decl_names (VariableDecl vis (Constant e) id ty slot :: ts) =
    id :: const_decl_names ts /\
  const_decl_names (_ :: ts) = const_decl_names ts
End

Theorem checked_const_decl_typed:
  check_contract mode layouts addr mods = SOME artifact /\
  ALOOKUP mods src = SOME ts /\
  MEM (VariableDecl vis (Constant e) id ty slot) ts ==>
  assignable_type (type_env_all_modules mods) ty /\
  well_typed_expr (artifact_env artifact mods src) e /\
  expr_type e = ty /\ constant_expr mods e
Proof
  rpt strip_tac >> drule check_contract_toplevel_decl_MEM_checked >>
  disch_then drule >> disch_then drule >> simp[check_toplevel_decl_def]
QED

Theorem constant_value_local_refs_present:
  (!e. !imms v ty id.
    constant_value mods imms e = SOME v /\ MEM (ty,id) (const_local_refs e) ==>
    IS_SOME (FLOOKUP (get_source_immutables NONE imms) id)) /\
  (!es. !imms vs ty id.
    constant_values mods imms es = SOME vs /\ MEM (ty,id) (const_local_exprs es) ==>
    IS_SOME (FLOOKUP (get_source_immutables NONE imms) id)) /\
  (!fs. !imms vs ty id.
    constant_values mods imms (MAP SND fs) = SOME vs /\
    MEM (ty,id) (const_local_fields fs) ==>
    IS_SOME (FLOOKUP (get_source_immutables NONE imms) id))
Proof
  ho_match_mp_tac const_local_refs_ind >>
  simp[const_local_refs_def, constant_value_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
  >- (PairCases_on `ns` >> Cases_on `ns0` >>
      gvs[const_local_refs_def, constant_value_def, AllCaseEqs()]) >>
  metis_tac[]
QED

Theorem const_decl_names_MEM:
  !ts id. MEM id (const_decl_names ts) <=>
    ?vis e ty slot. MEM (VariableDecl vis (Constant e) id ty slot) ts
Proof
  Induct >> simp[const_decl_names_def] >> Cases_on `h` >>
  simp[const_decl_names_def] >> rename1 `VariableDecl vis mut` >>
  Cases_on `mut` >> simp[const_decl_names_def, EXISTS_OR_THM]
QED

Theorem const_decl_names_distinct:
  !ts src. ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts)) ==>
    ALL_DISTINCT (const_decl_names ts)
Proof
  Induct >> simp[const_decl_names_def] >> rpt gen_tac >> Cases_on `h` >>
  simp[toplevel_vtype_keys_toplevel_def, const_decl_names_def] >>
  rpt strip_tac
  >~ [`const_decl_names (VariableDecl vis mut id ty slot :: ts)`]
  >- (Cases_on `mut` >> gvs[const_decl_names_def, const_decl_names_MEM] >>
      metis_tac[vyperTypeConstantCellsTheory.module_toplevel_vtype_key_MEM_Variable_any]) >>
  metis_tac[]
QED

Theorem checked_const_decl_names_distinct:
  check_contract mode layouts addr mods = SOME artifact /\
  ALOOKUP mods src = SOME ts ==> ALL_DISTINCT (const_decl_names ts)
Proof
  strip_tac >>
  `contract_namespaces_ok F mods` by metis_tac[check_contract_runtime_namespaces] >>
  metis_tac[const_decl_names_distinct,
    contract_namespaces_ok_module_toplevel_vtype_keys, ALOOKUP_MEM]
QED

Theorem constants_fold_module_prefix_refs:
  !pre A B vis e id ty slot rest ety n.
  constants_fold_module mods imms NONE
    (pre ++ VariableDecl vis (Constant e) id ty slot :: rest) A = SOME B /\
  MEM (ety,n) (const_local_refs e) ==>
  IS_SOME (FLOOKUP (get_source_immutables NONE imms) n) \/
  n IN FDOM A \/ MEM n (const_decl_names pre)
Proof
  Induct >- (
    simp[constants_fold_module_def] >> rpt strip_tac >> gvs[AllCaseEqs()] >>
    drule (cj 1 constant_value_local_refs_present) >> disch_then drule >>
    simp[merge_constant_imms_def, vyperTypeInitialStateTheory.get_source_immutables_set_same,
         FLOOKUP_FUNION, AllCaseEqs(), FLOOKUP_DEF, const_decl_names_def] >>
    metis_tac[]) >>
  rpt gen_tac >> Cases_on `h` >>
  simp[constants_fold_module_def, const_decl_names_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
  >~ [`constants_fold_module _ _ _ (VariableDecl vis' mut name' ty' slot' :: _) _`]
  >- (Cases_on `mut` >>
      gvs[constants_fold_module_def, const_decl_names_def, AllCaseEqs()] >>
      first_x_assum drule_all >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem constants_fold_append:
  !pre imms rest out.
  constants_fold mods imms (pre ++ rest) = SOME out ==>
  ?mid. constants_fold mods imms pre = SOME mid /\
        constants_fold mods mid rest = SOME out
Proof
  Induct >> simp[constants_fold_def] >> Cases_on `h` >>
  simp[constants_fold_def] >> rpt strip_tac >> gvs[AllCaseEqs()] >>
  first_x_assum drule >> strip_tac >>
  qexists `mid` >> simp[]
QED

Theorem constants_order_main_last:
  !mods tops. ALL_DISTINCT (MAP FST mods) /\ ALOOKUP mods NONE = SOME tops ==>
  ?imports. constants_order mods = imports ++ [(NONE,tops)] /\
    EVERY (IS_SOME o FST) imports
Proof
  Induct >> simp[vyperInterpreterTheory.constants_order_def] >>
  Cases_on `h` >> Cases_on `q` >>
  simp[vyperInterpreterTheory.constants_order_def] >> rpt strip_tac >> gvs[]
  >- (rw[EVERY_MEM] >> PairCases_on `e` >> Cases_on `e0` >> simp[] >>
      `MEM (NONE,e1) mods` by
        metis_tac[vyperInterpreterTheory.PERM_constants_order, sortingTheory.PERM_MEM_EQ] >>
      gvs[MEM_MAP, pairTheory.EXISTS_PROD]) >>
  first_x_assum drule_all >> strip_tac >> qexists `(SOME x,r)::imports` >> simp[]
QED

Theorem constants_fold_imports_preserve_local:
  !imports imms out. EVERY (IS_SOME o FST) imports /\
    constants_fold mods imms imports = SOME out ==>
    get_source_immutables NONE out = get_source_immutables NONE imms
Proof
  Induct >> simp[constants_fold_def] >> Cases_on `h` >>
  simp[constants_fold_def] >> rpt strip_tac >> gvs[AllCaseEqs()] >>
  first_x_assum drule_all >>
  simp[merge_constant_imms_def,
       vyperTypeInitialStateTheory.get_source_immutables_set_other] >>
  Cases_on `q` >> gvs[vyperTypeInitialStateTheory.get_source_immutables_set_other]
QED

Theorem constant_expr_local_refs_declared:
  (!e. constant_expr mods e ==>
    !ty id. MEM (ty,id) (const_local_refs e) ==> declared_constant mods NONE id) /\
  (!es. EVERY (constant_expr mods) es ==>
    !ty id. MEM (ty,id) (const_local_exprs es) ==> declared_constant mods NONE id) /\
  (!fs. EVERY (constant_expr mods) (MAP SND fs) ==>
    !ty id. MEM (ty,id) (const_local_fields fs) ==> declared_constant mods NONE id)
Proof
  ho_match_mp_tac const_local_refs_ind >>
  simp[const_local_refs_def, constant_expr_def] >> rpt strip_tac >> gvs[]
  >- (PairCases_on `ns` >> Cases_on `ns0` >> gvs[const_local_refs_def, constant_expr_def]) >>
  metis_tac[]
QED

Theorem checked_const_initializer_prefix_names:
  check_contract mode layouts addr mods = SOME artifact /\
  ALOOKUP mods NONE = SOME tops /\
  tops = pre ++ VariableDecl vis (Constant e) id ty slot :: rest /\
  MEM (ety,n) (const_local_refs e) ==>
  MEM n (const_decl_names pre)
Proof
  rpt strip_tac >>
  `constant_expr mods e` by (irule (cj 4 checked_const_decl_typed) >> metis_tac[MEM_APPEND, MEM]) >>
  `declared_constant mods NONE n` by metis_tac[constant_expr_local_refs_declared] >>
  `contract_namespaces_ok F mods` by metis_tac[check_contract_runtime_namespaces] >>
  `?imports. constants_order mods = imports ++ [(NONE,tops)] /\
     EVERY (IS_SOME o FST) imports` by
    (irule constants_order_main_last >> gvs[contract_namespaces_ok_def]) >>
  `contract_constants_ok mods` by
    (qpat_x_assum `check_contract _ _ _ _ = _` mp_tac >>
     Cases_on `mode` >> simp[check_contract_def]) >>
  gvs[contract_constants_ok_def] >>
  Cases_on `initial_immutables (type_env_all_modules mods) mods` >> gvs[] >>
  rename1 `initial_immutables _ _ = SOME imms` >>
  qpat_x_assum `IS_SOME (constants_fold _ _ _)` mp_tac >>
  simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  drule constants_fold_append >> strip_tac >>
  drule_all constants_fold_imports_preserve_local >> strip_tac >>
  qpat_x_assum `constants_fold _ _ [(NONE,_)] = _` mp_tac >>
  simp[constants_fold_def] >> strip_tac >> gvs[AllCaseEqs()] >>
  qpat_x_assum `constants_fold_module _ _ _ _ _ = _` mp_tac >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> strip_tac >>
  drule_all constants_fold_module_prefix_refs >>
  gvs[declared_constant_def] >>
  `FLOOKUP (get_source_immutables NONE imms) n = NONE` by
    (irule vyperTypeConstantCellsTheory.checked_initial_immutables_constant_absent >>
     metis_tac[]) >> simp[]
QED

Theorem checked_constant_refs_well_typed:
  check_contract mode layouts addr mods = SOME artifact /\
  ALOOKUP cx.sources cx.txn.target = SOME mods ==>
  (!e. constant_expr mods e /\
    well_typed_expr (artifact_env artifact mods current_src) e ==>
    !ty id. MEM (ty,id) (const_local_refs e) ==>
      well_typed_expr (artifact_env artifact mods current_src) (TopLevelName ty (NONE,id))) /\
  (!es. EVERY (constant_expr mods) es /\
    well_typed_exprs (artifact_env artifact mods current_src) es ==>
    !ty id. MEM (ty,id) (const_local_exprs es) ==>
      well_typed_expr (artifact_env artifact mods current_src) (TopLevelName ty (NONE,id))) /\
  (!fs. EVERY (constant_expr mods) (MAP SND fs) /\
    well_typed_named_exprs (artifact_env artifact mods current_src) fs ==>
    !ty id. MEM (ty,id) (const_local_fields fs) ==>
      well_typed_expr (artifact_env artifact mods current_src) (TopLevelName ty (NONE,id)))
Proof
  strip_tac >> ho_match_mp_tac const_local_refs_ind >>
  simp[const_local_refs_def, constant_expr_def] >> rpt strip_tac
  >- (PairCases_on `ns` >> Cases_on `ns0` >> gvs[const_local_refs_def])
  >- (qpat_x_assum `well_typed_expr _ (StructLit _ _ _)` mp_tac >>
      simp[Once well_typed_expr_def] >> strip_tac >> metis_tac[])
  >- (drule_all constant_subscript_base_well_typed >> metis_tac[])
  >- (qpat_x_assum `well_typed_expr _ (Subscript _ _ _)` mp_tac >>
      simp[Once well_typed_expr_def] >> strip_tac >> metis_tac[])
  >- (qpat_x_assum `well_typed_expr _ (Attribute _ _ _)` mp_tac >>
      simp[Once well_typed_expr_def] >> strip_tac >> metis_tac[])
  >- (qpat_x_assum `well_typed_expr _ (Builtin _ _ _)` mp_tac >>
      simp[Once well_typed_expr_def] >> strip_tac >> metis_tac[])
  >- (qpat_x_assum `well_typed_expr _ (TypeBuiltin _ _ _ _)` mp_tac >>
      simp[Once well_typed_expr_def] >> strip_tac >> metis_tac[])
  >- (qpat_x_assum `well_typed_exprs _ (_::_)` mp_tac >>
      simp[Once well_typed_expr_def] >> strip_tac >> metis_tac[])
  >- (qpat_x_assum `well_typed_exprs _ (_::_)` mp_tac >>
      simp[Once well_typed_expr_def] >> strip_tac >> metis_tac[]) >>
  qpat_x_assum `well_typed_named_exprs _ (_::_)` mp_tac >>
  simp[Once well_typed_expr_def] >> strip_tac >> metis_tac[]
QED

Theorem checked_constant_reference_annotation:
  check_contract mode layouts addr mods = SOME artifact /\
  ALOOKUP mods src = SOME ts /\
  MEM (VariableDecl vis (Constant init) id ty slot) ts /\
  constant_expr mods e /\ well_typed_expr (artifact_env artifact mods current_src) e /\
  MEM (ann,id) (const_local_refs e) /\ src = NONE ==> ann = ty
Proof
  strip_tac >>
  `ALOOKUP (constant_context mods).sources (constant_context mods).txn.target = SOME mods` by
    simp[constant_context_def] >>
  `well_typed_expr (artifact_env artifact mods current_src) (TopLevelName ann (NONE,id))` by
    metis_tac[checked_constant_refs_well_typed] >>
  `MEM (src,ts) mods` by metis_tac[ALOOKUP_MEM] >>
  gvs[] >>
  drule_all (vyperTypeConstantCellsTheory.checked_constant_declared_type |>
    Q.INST [`cx` |-> `constant_context mods`]) >> simp[]
QED

Theorem checked_const_initializer_prefix:
  check_contract mode layouts addr mods = SOME artifact /\
  ALOOKUP mods NONE = SOME tops /\
  tops = pre ++ VariableDecl vis (Constant e) id ty slot :: rest ==>
  constant_expr mods e /\ expr_type e = ty /\
  well_typed_expr (artifact_env artifact mods NONE) e /\
  (!ety n. MEM (ety,n) (const_local_refs e) ==>
    MEM n (const_decl_names pre) /\
    ?v init slot'. MEM (VariableDecl v (Constant init) n ety slot') pre)
Proof
  strip_tac >>
  `MEM (VariableDecl vis (Constant e) id ty slot) tops` by simp[] >>
  drule_all checked_const_decl_typed >> strip_tac >> simp[] >>
  rpt strip_tac >>
  `MEM n (const_decl_names pre)` by metis_tac[checked_const_initializer_prefix_names] >>
  simp[] >> fs[const_decl_names_MEM] >>
  `ty' = ety` by
    (sym_tac >> irule checked_constant_reference_annotation >>
     metis_tac[MEM_APPEND, MEM]) >> gvs[] >> metis_tac[]
QED

Theorem const_subst_local_refs_closed:
  (!e. !E. constant_expr mods e /\
    (!ty id. MEM (ty,id) (const_local_refs e) ==>
      ?r. ALOOKUP E id = SOME r /\ const_local_refs r = []) ==>
    const_local_refs (subst_consts_expr E e) = []) /\
  (!es. !E. EVERY (constant_expr mods) es /\
    (!ty id. MEM (ty,id) (const_local_exprs es) ==>
      ?r. ALOOKUP E id = SOME r /\ const_local_refs r = []) ==>
    const_local_exprs (subst_consts_exprs E es) = []) /\
  (!fs. !E. EVERY (constant_expr mods) (MAP SND fs) /\
    (!ty id. MEM (ty,id) (const_local_fields fs) ==>
      ?r. ALOOKUP E id = SOME r /\ const_local_refs r = []) ==>
    const_local_fields (subst_consts_fields E fs) = [])
Proof
  ho_match_mp_tac const_local_refs_ind >>
  simp[const_local_refs_def, constant_expr_def, subst_consts_expr_def] >>
  rpt strip_tac >> gvs[]
  >- (PairCases_on `ns` >> Cases_on `ns0` >>
      gvs[const_local_refs_def, subst_consts_expr_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem merge_constant_imms_imports:
  IS_SOME src ==>
  get_source_immutables src (merge_constant_imms NONE A imms) =
  get_source_immutables src imms
Proof
  Cases_on `src` >>
  simp[merge_constant_imms_def,
       vyperTypeInitialStateTheory.get_source_immutables_set_other]
QED

Theorem const_acc_agrees_stable:
  const_acc_agrees mods imms E A /\
  (!src. IS_SOME src ==> get_source_immutables src imms = get_source_immutables src imms') ==>
  const_acc_agrees mods imms' E A
Proof
  rw[const_acc_agrees_def] >> first_x_assum drule >> strip_tac >>
  metis_tac[constant_value_closed_stable]
QED

Theorem const_acc_agrees_empty:
  const_acc_agrees mods imms [] FEMPTY
Proof
  simp[const_acc_agrees_def]
QED

Theorem const_acc_agrees_snoc:
  const_acc_agrees mods imms E A /\ ~MEM id (MAP FST E) /\
  constant_expr mods r /\ const_local_refs r = [] /\
  evaluate_type (type_env_all_modules mods) (expr_type r) = SOME tv /\
  constant_value mods imms' r = SOME v /\
  (!src. IS_SOME src ==> get_source_immutables src imms = get_source_immutables src imms') ==>
  const_acc_agrees mods imms' (E ++ [(id,r)]) (A |+ (id,(tv,v)))
Proof
  strip_tac >> drule_all const_acc_agrees_stable >>
  simp[const_acc_agrees_def, MAP_APPEND, ALL_DISTINCT_APPEND, FDOM_FUPDATE,
       pred_setTheory.EXTENSION] >> strip_tac >>
  rpt conj_tac >- metis_tac[] >- metis_tac[] >>
  rpt gen_tac >> simp[ALOOKUP_APPEND] >>
  Cases_on `ALOOKUP E id'` >> simp[] >> strip_tac
  >- (gvs[] >> simp[FLOOKUP_UPDATE]) >>
  `id' <> id` by metis_tac[ALOOKUP_MEM, MEM_MAP, pairTheory.FST] >>
  simp[FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem checked_constant_name_fold:
  check_contract mode layouts addr mods = SOME artifact /\
  ALOOKUP mods NONE = SOME tops /\
  MEM (VariableDecl vis (Constant init) id ty slot) tops /\
  FLOOKUP A id = SOME (tv,v) ==>
  constant_value mods (merge_constant_imms NONE A imms)
    (TopLevelName ann (NONE,id)) = SOME v
Proof
  strip_tac >>
  `contract_namespaces_ok F mods` by metis_tac[check_contract_runtime_namespaces] >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops))` by
    metis_tac[contract_namespaces_ok_module_toplevel_vtype_keys, ALOOKUP_MEM] >>
  `find_var_decl_by_name id tops = NONE` by
    metis_tac[find_var_decl_by_name_NONE_Constant] >>
  simp[constant_value_def, merge_constant_imms_def,
       vyperTypeInitialStateTheory.get_source_immutables_set_same, FLOOKUP_FUNION]
QED

(* Metadata connecting expanded syntax to its checked source declarations. *)
Definition const_prefix_syntax_def:
  const_prefix_syntax E pre <=>
    MAP FST E = const_decl_names pre /\
    (!id r. ALOOKUP E id = SOME r ==>
      ?vis init ty slot. MEM (VariableDecl vis (Constant init) id ty slot) pre /\
        expr_type r = ty)
End

Theorem checked_const_prefix_replacements:
  check_contract mode layouts addr mods = SOME artifact /\
  ALOOKUP mods NONE = SOME tops /\
  tops = pre ++ VariableDecl vis (Constant e) id ty slot :: rest /\
  const_prefix_syntax E pre /\
  const_acc_agrees mods (merge_constant_imms NONE A imms) E A ==>
  const_replacements_ok mods (merge_constant_imms NONE A imms) E (const_local_refs e) /\
  (!ann n. MEM (ann,n) (const_local_refs e) ==>
    ?r. ALOOKUP E n = SOME r /\ const_local_refs r = [])
Proof
  strip_tac >> drule_all checked_const_initializer_prefix >> strip_tac >>
  gvs[const_replacements_ok_def, const_prefix_syntax_def, const_acc_agrees_def] >>
  conj_tac >> rpt gen_tac >> strip_tac
  >- (`?vis' init ty' slot'. MEM (VariableDecl vis' (Constant init) id' ty' slot') pre /\
          expr_type r = ty'` by metis_tac[] >>
      `MEM (VariableDecl vis' (Constant init) id' ty' slot')
        (pre ++ VariableDecl vis (Constant e) id (expr_type e) slot :: rest)` by simp[] >>
      `ty = ty'` by
        (irule checked_constant_reference_annotation >> goal_assum (drule_at Any) >>
         goal_assum (drule_at Any) >> metis_tac[]) >>
      `?tv v. FLOOKUP A id' = SOME (tv,v) /\
         constant_value mods (merge_constant_imms NONE A imms) r = SOME v` by metis_tac[] >>
      `constant_value mods (merge_constant_imms NONE A imms)
        (TopLevelName ty (NONE,id')) = SOME v` by
        (irule checked_constant_name_fold >> rpt conj_tac >> metis_tac[]) >>
      metis_tac[]) >>
  `MEM n (MAP FST E)` by metis_tac[] >>
  `?r. ALOOKUP E n = SOME r` by metis_tac[ALOOKUP_NONE, optionTheory.option_CASES] >>
  metis_tac[]
QED

Theorem const_decl_names_append:
  !pre rest. const_decl_names (pre ++ rest) = const_decl_names pre ++ const_decl_names rest
Proof
  Induct >> simp[const_decl_names_def] >> Cases_on `h` >>
  simp[const_decl_names_def] >> rename1 `VariableDecl vis mut` >>
  Cases_on `mut` >> simp[const_decl_names_def]
QED

Theorem const_prefix_syntax_snoc:
  const_prefix_syntax E pre /\ expr_type r = ty ==>
  const_prefix_syntax (E ++ [(id,r)]) (pre ++ [VariableDecl vis (Constant init) id ty slot])
Proof
  rw[const_prefix_syntax_def, MAP_APPEND, const_decl_names_append, const_decl_names_def] >>
  gvs[ALOOKUP_APPEND, AllCaseEqs()] >> metis_tac[MEM_APPEND, MEM]
QED

Theorem checked_const_acc_step:
  check_contract mode layouts addr mods = SOME artifact /\
  ALOOKUP mods NONE = SOME tops /\
  tops = pre ++ VariableDecl vis (Constant e) id ty slot :: rest /\
  const_prefix_syntax E pre /\
  const_acc_agrees mods (merge_constant_imms NONE A imms) E A /\
  evaluate_type (type_env_all_modules mods) ty = SOME tv /\
  constant_value mods (merge_constant_imms NONE A imms) e = SOME v ==>
  const_acc_agrees mods (merge_constant_imms NONE (A |+ (id,(tv,v))) imms)
    (E ++ [(id,fold_const_expr (subst_consts_expr E e))]) (A |+ (id,(tv,v))) /\
  const_prefix_syntax (E ++ [(id,fold_const_expr (subst_consts_expr E e))])
    (pre ++ [VariableDecl vis (Constant e) id ty slot])
Proof
  strip_tac >> drule_all checked_const_initializer_prefix >> strip_tac >>
  drule_all checked_const_prefix_replacements >> strip_tac >>
  `expr_type (subst_consts_expr E e) = ty /\
   constant_expr mods (subst_consts_expr E e) /\
   constant_value mods (merge_constant_imms NONE A imms) (subst_consts_expr E e) = SOME v` by
    metis_tac[const_subst_constant_value] >>
  `const_local_refs (subst_consts_expr E e) = []` by
    metis_tac[const_subst_local_refs_closed] >>
  `expr_type (fold_const_expr (subst_consts_expr E e)) = ty /\
   constant_expr mods (fold_const_expr (subst_consts_expr E e)) /\
   const_local_refs (fold_const_expr (subst_consts_expr E e)) = [] /\
   constant_value mods (merge_constant_imms NONE A imms)
     (fold_const_expr (subst_consts_expr E e)) = SOME v` by
    metis_tac[fold_const_expr_type, fold_const_expr_constant,
      fold_const_expr_local_closed, fold_const_expr_value] >>
  `~MEM id (MAP FST E)` by
    (drule_all checked_const_decl_names_distinct >>
     gvs[const_prefix_syntax_def, const_decl_names_append, const_decl_names_def,
         ALL_DISTINCT_APPEND]) >>
  `!src. IS_SOME src ==>
    get_source_immutables src (merge_constant_imms NONE A imms) =
    get_source_immutables src (merge_constant_imms NONE (A |+ (id,(tv,v))) imms)` by
    simp[merge_constant_imms_imports] >>
  `constant_value mods (merge_constant_imms NONE (A |+ (id,(tv,v))) imms)
    (fold_const_expr (subst_consts_expr E e)) = SOME v` by metis_tac[constant_value_closed_stable] >>
  conj_tac >- (irule const_acc_agrees_snoc >> metis_tac[]) >>
  irule const_prefix_syntax_snoc >> simp[]
QED

Theorem const_prefix_syntax_skip:
  const_prefix_syntax E pre /\ const_decl_names [t] = [] ==>
  const_prefix_syntax E (pre ++ [t])
Proof
  simp[const_prefix_syntax_def, const_decl_names_append] >>
  metis_tac[MEM_APPEND]
QED

Theorem constants_fold_module_subst_acc:
  !ts pre E A B.
    check_contract mode layouts addr mods = SOME artifact /\
    ALOOKUP mods NONE = SOME tops /\ tops = pre ++ ts /\
    const_prefix_syntax E pre /\
    const_acc_agrees mods (merge_constant_imms NONE A imms) E A /\
    constants_fold_module mods imms NONE ts A = SOME B ==>
    const_acc_agrees mods (merge_constant_imms NONE B imms) (module_consts_env ts E) B /\
    const_prefix_syntax (module_consts_env ts E) tops
Proof
  Induct >- simp[constants_fold_module_def, module_consts_env_def] >>
  rpt gen_tac >> Cases_on `h` >>
  simp[constants_fold_module_def, module_consts_env_def] >>
  strip_tac
  >~ [`module_consts_env (VariableDecl vis mut id ty slot :: ts) E`]
  >- (Cases_on `mut` >>
      gvs[constants_fold_module_def, module_consts_env_def, AllCaseEqs()]
      >~ [`constant_value mods (merge_constant_imms NONE A imms) e = SOME v`]
      >- (`const_acc_agrees mods (merge_constant_imms NONE (A |+ (id,(tv,v))) imms)
             (E ++ [(id,fold_const_expr (subst_consts_expr E e))]) (A |+ (id,(tv,v))) /\
           const_prefix_syntax (E ++ [(id,fold_const_expr (subst_consts_expr E e))])
             (pre ++ [VariableDecl vis (Constant e) id ty slot])` by
            (irule checked_const_acc_step >>
             conj_tac >- metis_tac[] >>
             conj_tac >- (qexistsl [`ts`,`pre ++ VariableDecl vis (Constant e) id ty slot :: ts`] >> simp[]) >>
             simp[]) >>
          first_x_assum irule >> metis_tac[]) >>
      first_x_assum irule >> reverse conj_tac >- metis_tac[] >>
      gvs[const_prefix_syntax_def, const_decl_names_append, const_decl_names_def] >>
      metis_tac[MEM_APPEND]) >>
  gvs[] >> first_x_assum irule >> reverse conj_tac >- metis_tac[] >>
  gvs[const_prefix_syntax_def, const_decl_names_append, const_decl_names_def] >>
      metis_tac[MEM_APPEND]
QED

Theorem checked_module_consts_env_agrees:
  check_contract mode layouts addr mods = SOME artifact /\
  ALOOKUP mods NONE = SOME tops /\
  constants_fold_module mods imms NONE tops FEMPTY = SOME A ==>
  const_acc_agrees mods (merge_constant_imms NONE A imms) (module_consts_env tops []) A /\
  const_prefix_syntax (module_consts_env tops []) tops
Proof
  strip_tac >>
  irule constants_fold_module_subst_acc >>
  conj_tac >- metis_tac[] >> simp[] >>
  conj_tac >- simp[const_prefix_syntax_def, const_decl_names_def] >>
  qexists `FEMPTY` >> simp[const_acc_agrees_empty]
QED

Theorem checked_module_consts_env_replacement:
  check_contract mode layouts addr mods = SOME artifact /\
  ALOOKUP mods NONE = SOME tops /\
  constants_fold_module mods imms NONE tops FEMPTY = SOME A /\
  ALOOKUP (module_consts_env tops []) id = SOME r ==>
  ?vis init ty slot tv v.
    MEM (VariableDecl vis (Constant init) id ty slot) tops /\
    expr_type r = ty /\ FLOOKUP A id = SOME (tv,v) /\
    constant_expr mods r /\ const_local_refs r = [] /\
    evaluate_type (type_env_all_modules mods) ty = SOME tv /\
    constant_value mods (merge_constant_imms NONE A imms) r = SOME v
Proof
  strip_tac >> drule_all checked_module_consts_env_agrees >>
  simp[const_acc_agrees_def, const_prefix_syntax_def] >> metis_tac[]
QED

Theorem checked_module_consts_env_runtime:
  check_contract mode layouts addr mods = SOME artifact /\
  ALOOKUP mods NONE = SOME tops /\
  constants_fold_module mods imms NONE tops FEMPTY = SOME A /\
  ALOOKUP (module_consts_env tops []) id = SOME r /\
  (!src. IS_SOME src ==> get_source_immutables src imms' = get_source_immutables src imms) /\
  (!tv v. FLOOKUP A id = SOME (tv,v) ==>
    FLOOKUP (get_source_immutables NONE imms') id = SOME (tv,v)) ==>
  constant_expr mods r /\ const_local_refs r = [] /\
  constant_value mods imms' r = constant_value mods imms' (TopLevelName (expr_type r) (NONE,id))
Proof
  strip_tac >> drule_all checked_module_consts_env_replacement >> strip_tac >> simp[] >>
  `constant_value mods imms' r = SOME v` by
    (qsuff_tac `constant_value mods (merge_constant_imms NONE A imms) r = constant_value mods imms' r`
     >- simp[] >> irule constant_value_closed_stable >> simp[merge_constant_imms_imports]) >>
  `contract_namespaces_ok F mods` by metis_tac[check_contract_runtime_namespaces] >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops))` by
    metis_tac[contract_namespaces_ok_module_toplevel_vtype_keys, ALOOKUP_MEM] >>
  `find_var_decl_by_name id tops = NONE` by metis_tac[find_var_decl_by_name_NONE_Constant] >>
  simp[constant_value_def] >> qexists `(tv,v)` >> simp[]
QED

Theorem checked_const_initializer_read_fold:
  check_contract F cx.layouts cx.txn.target mods = SOME artifact /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  ALOOKUP mods src = SOME full /\
  MEM (VariableDecl vis (Constant e) id ty slot) full /\
  deployment_constant_cells_typed (type_env_all_modules mods) cx.txn.target mods am /\
  constant_fmap_declared_typed (type_env_all_modules mods) full acc /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  (do pv <- eval_expr cx e; read_result cx pv od)
    (initial_state (merge_constants cx.txn.target src acc am) [FEMPTY]) = (INL v,st') ==>
  constant_value mods
    (merge_constant_imms src acc (constant_machine_immutables am cx.txn.target)) e = SOME v /\
  constant_fmap_declared_typed (type_env_all_modules mods) full (acc |+ (id,(tv,v)))
Proof
  strip_tac >> drule_all checked_const_decl_typed >> strip_tac >>
  `contract_namespaces_ok F mods` by metis_tac[check_contract_runtime_namespaces] >>
  `deployment_constant_cells_typed (type_env_all_modules mods) cx.txn.target mods
    (merge_constants cx.txn.target src acc am)` by
    metis_tac[vyperTypeConstantCellsTheory.merge_constants_preserves_constant_cells_typed] >>
  `constant_machine_immutables (merge_constants cx.txn.target src acc am) cx.txn.target =
    merge_constant_imms src acc (constant_machine_immutables am cx.txn.target)` by
    (simp[constant_machine_immutables_def, merge_constants_immutables,
          vyperInterpreterTheory.merge_constants_def, merge_constant_imms_def,
          vyperStateTheory.empty_immutables_def]) >>
  drule_all constant_eval_expr_read_fold_agreement >> strip_tac >>
  drule_all constant_eval_expr_read_typed >> strip_tac >>
  conj_tac >- gvs[] >>
  drule get_tenv_sources >> disch_then SUBST_ALL_TAC >>
  irule vyperTypeConstantCellsTheory.constant_fmap_declared_typed_update >>
  gvs[vyperTypeExprSoundnessTheory.value_runtime_typed_def, artifact_env_def] >>
  metis_tac[]
QED

Theorem constants_env_fold_agreement_acc:
  !ts acc A.
    check_contract F cx.layouts cx.txn.target mods = SOME artifact /\
    ALOOKUP cx.sources cx.txn.target = SOME mods /\
    ALOOKUP mods src = SOME full /\ EVERY (\t. MEM t full) ts /\
    deployment_constant_cells_typed (type_env_all_modules mods) cx.txn.target mods am /\
    constant_fmap_declared_typed (type_env_all_modules mods) full acc /\
    constants_env cx am cx.txn.target src ts acc = SOME A ==>
    constants_fold_module mods (constant_machine_immutables am cx.txn.target) src ts acc = SOME A /\
    constant_fmap_declared_typed (type_env_all_modules mods) full A
Proof
  Induct >- simp[vyperInterpreterTheory.constants_env_def, constants_fold_module_def] >>
  rpt gen_tac >> Cases_on `h` >>
  simp[vyperInterpreterTheory.constants_env_def, constants_fold_module_def] >>
  strip_tac
  >~ [`constants_fold_module _ _ _ (VariableDecl vis mut id ty slot :: ts) acc`]
  >- (Cases_on `mut` >>
      gvs[vyperInterpreterTheory.constants_env_def, constants_fold_module_def, AllCaseEqs()]
      >~ [`FST _ = INL v`]
      >- (`?st'. (do pv <- eval_expr cx e; read_result cx pv od)
             (initial_state (merge_constants cx.txn.target src acc am) [FEMPTY]) = (INL v,st')` by
            metis_tac[pairTheory.PAIR] >>
          drule_all checked_const_initializer_read_fold >> strip_tac >>
          first_x_assum (qspec_then `acc |+ (id,(tv,v))` mp_tac) >> simp[] >> strip_tac >>
          drule get_tenv_sources >> strip_tac >> gvs[] >> metis_tac[]) >>
      metis_tac[]) >>
  first_x_assum drule_all >> simp[]
QED

Theorem checked_constants_env_fold:
  check_contract F cx.layouts cx.txn.target mods = SOME artifact /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  ALOOKUP mods NONE = SOME tops /\
  deployment_constant_cells_typed (type_env_all_modules mods) cx.txn.target mods am /\
  constants_env cx am cx.txn.target NONE tops FEMPTY = SOME A ==>
  constants_fold_module mods (constant_machine_immutables am cx.txn.target)
    NONE tops FEMPTY = SOME A
Proof
  strip_tac >> irule (cj 1 constants_env_fold_agreement_acc) >>
  simp[vyperTypeConstantCellsTheory.constant_fmap_declared_typed_empty, EVERY_MEM] >>
  metis_tac[]
QED

Theorem checked_constants_env_subst_agrees:
  check_contract F cx.layouts cx.txn.target mods = SOME artifact /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  ALOOKUP mods NONE = SOME tops /\
  deployment_constant_cells_typed (type_env_all_modules mods) cx.txn.target mods am /\
  constants_env cx am cx.txn.target NONE tops FEMPTY = SOME A ==>
  const_acc_agrees mods
    (merge_constant_imms NONE A (constant_machine_immutables am cx.txn.target))
    (module_consts_env tops []) A /\
  const_prefix_syntax (module_consts_env tops []) tops
Proof
  strip_tac >> drule_all checked_constants_env_fold >> strip_tac >>
  drule_all checked_module_consts_env_agrees >> simp[]
QED

(* The typing premise is the evaluator's ordinary expression interface; the
   collector supplies the value, not a new runtime typing assumption. *)
Theorem checked_module_consts_env_runtime_read:
  check_contract F cx.layouts cx.txn.target mods = SOME artifact /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  ALOOKUP mods NONE = SOME tops /\
  constants_fold_module mods imms NONE tops FEMPTY = SOME A /\
  ALOOKUP (module_consts_env tops []) id = SOME r /\
  (!src. IS_SOME src ==>
    get_source_immutables src (constant_machine_immutables am cx.txn.target) =
    get_source_immutables src imms) /\
  (!tv v. FLOOKUP A id = SOME (tv,v) ==>
    FLOOKUP (get_source_immutables NONE
      (constant_machine_immutables am cx.txn.target)) id = SOME (tv,v)) /\
  deployment_constant_cells_typed (type_env_all_modules mods) cx.txn.target mods am /\
  well_typed_expr (artifact_env artifact mods current_src) r ==>
  ?v pv.
    constant_value mods (constant_machine_immutables am cx.txn.target)
      (TopLevelName (expr_type r) (NONE,id)) = SOME v /\
    eval_expr cx r (initial_state am sc) = (INL pv,initial_state am sc) /\
    read_result cx pv (initial_state am sc) = (INL v,initial_state am sc) /\
    value_runtime_typed (artifact_env artifact mods current_src) (expr_type r) v
Proof
  strip_tac >>
  drule_all checked_module_consts_env_runtime >> strip_tac >>
  drule_all checked_module_consts_env_replacement >> strip_tac >>
  `constant_value mods (constant_machine_immutables am cx.txn.target) r = SOME v` by
    (qsuff_tac `constant_value mods (merge_constant_imms NONE A imms) r =
       constant_value mods (constant_machine_immutables am cx.txn.target) r`
     >- simp[] >> irule constant_value_closed_stable >>
     simp[merge_constant_imms_imports]) >>
  drule (cj 1 constant_value_eval_expr) >>
  disch_then (qspecl_then [`cx`,`am`] mp_tac) >> simp[] >>
  disch_then (qspecl_then [`sc`,`current_src`] mp_tac) >> simp[] >>
  metis_tac[]
QED


(* Constant roots cannot occur in the checked immutable-write namespace. *)
Theorem checked_constant_not_assignable:
  contract_namespaces_ok F mods /\ declared_constant mods src id ==>
  FLOOKUP (build_contract_type_artifact F mods).cta_bare_global_assignable
    (src,id) = NONE
Proof
  rpt strip_tac >>
  Cases_on `FLOOKUP (build_contract_type_artifact F mods).cta_bare_global_assignable (src,id)` >> simp[] >>
  drule_all build_contract_type_artifact_bare_global_assignable_sound >>
  strip_tac >> gvs[declared_constant_def] >>
  `ALL_DISTINCT (MAP FST mods)` by gvs[contract_namespaces_ok_def] >>
  `ALOOKUP mods src = SOME tls` by metis_tac[ALOOKUP_ALL_DISTINCT_MEM] >>
  gvs[] >>
  drule_all contract_namespaces_ok_module_toplevel_vtype_keys >>
  metis_tac[vyperTypeConstantCellsTheory.module_immutable_constant_names_distinct]
QED

(* Mutation typing is inherited by the syntactic place root. *)
Definition base_target_root_def:
  base_target_root (AttributeTarget t id) = base_target_root t /\
  base_target_root (SubscriptTarget t e) = base_target_root t /\
  base_target_root t = t
End

Theorem type_place_target_root:
  !bt env. IS_SOME (type_place_target env bt) ==>
    IS_SOME (type_place_target env (base_target_root bt))
Proof
  recInduct base_target_root_ind >>
  simp[base_target_root_def, optionTheory.IS_SOME_EXISTS,
    vyperTypeEnvTheory.type_place_target_AttributeTarget,
    vyperTypeEnvTheory.type_place_target_SubscriptTarget] >>
  metis_tac[]
QED

Theorem checked_constant_bare_global:
  contract_namespaces_ok F mods /\ declared_constant mods src id ==>
  IS_SOME (FLOOKUP (build_contract_type_artifact F mods).cta_bare_globals (src,id))
Proof
  strip_tac >> gvs[declared_constant_def] >>
  `ALL_DISTINCT (MAP FST mods)` by gvs[contract_namespaces_ok_def] >>
  `ALOOKUP mods src = SOME tls` by metis_tac[ALOOKUP_ALL_DISTINCT_MEM] >>
  metis_tac[build_contract_type_artifact_bare_globals_complete,
    optionTheory.IS_SOME_EXISTS]
QED

Theorem constant_root_not_typable:
  FLOOKUP env.bare_global_assignable (src,id) = NONE /\
  IS_SOME (FLOOKUP env.bare_globals (src,id)) ==>
  type_place_target env (TopLevelNameTarget (src,id)) = NONE
Proof
  Cases_on `type_place_target env (TopLevelNameTarget (src,id))` >>
  gvs[vyperTypeEnvTheory.type_place_target_TopLevelNameTarget]
QED

Theorem typed_mutation_root_excludes_constant:
  IS_SOME (type_place_target env bt) /\
  FLOOKUP env.bare_global_assignable (src,id) = NONE /\
  IS_SOME (FLOOKUP env.bare_globals (src,id)) ==>
  base_target_root bt <> TopLevelNameTarget (src,id)
Proof
  metis_tac[type_place_target_root, constant_root_not_typable,
    optionTheory.NOT_IS_SOME_EQ_NONE]
QED

Theorem push_function_target:
  push_function fn sc cx st = (INL cx',st') ==> cx'.txn.target = cx.txn.target
Proof
  simp[vyperInterpreterTheory.push_function_def, vyperStateTheory.return_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem extend_storage_place_not_immutable:
  extend_storage_place cx tr slot tv sb st <>
    (INL (ImmutablePlace src id path),st')
Proof
  Cases_on `tv` >> Cases_on `sb` >>
  simp[vyperStateTheory.extend_storage_place_def,
    vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
    vyperStateTheory.return_def, vyperStateTheory.raise_def,
    vyperStateTheory.lift_option_type_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
  >- (rename1 `ValueSubscript v` >> Cases_on `v` >>
      gvs[vyperStateTheory.extend_storage_place_def, vyperStateTheory.raise_def])
  >- (rename1 `ValueSubscript v` >> Cases_on `v` >>
      gvs[vyperStateTheory.extend_storage_place_def, vyperStateTheory.bind_def,
        vyperStateTheory.ignore_bind_def, vyperStateTheory.return_def,
        vyperStateTheory.raise_def, AllCaseEqs()])
  >- (rename1 `ValueSubscript v` >> Cases_on `v` >>
      gvs[vyperStateTheory.extend_storage_place_def, vyperStateTheory.bind_def,
        vyperStateTheory.return_def, vyperStateTheory.raise_def, AllCaseEqs()] >>
      pairarg_tac >> gvs[vyperStateTheory.return_def])
  >- (rename1 `ValueSubscript v` >> Cases_on `v` >>
      gvs[vyperStateTheory.extend_storage_place_def, vyperStateTheory.raise_def])
  >- (pairarg_tac >> gvs[vyperStateTheory.return_def]) >>
  rename1 `ValueSubscript v` >> Cases_on `v` >>
  gvs[vyperStateTheory.extend_storage_place_def,
    vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
    vyperStateTheory.return_def, vyperStateTheory.raise_def, AllCaseEqs()]
QED

Theorem extend_place_immutable_root:
  extend_place cx pv sb st = (INL (PlaceR (ImmutablePlace src id path)),st') ==>
  ?p. pv = PlaceR (ImmutablePlace src id p)
Proof
  Cases_on `pv` >>
  simp[vyperStateTheory.extend_place_def, vyperStateTheory.raise_def]
  >- (Cases_on `p` >>
      gvs[vyperStateTheory.extend_place_def, vyperStateTheory.bind_def,
        vyperStateTheory.ignore_bind_def, vyperStateTheory.return_def,
        vyperStateTheory.extend_memory_place_def, AllCaseEqs()] >>
      metis_tac[extend_storage_place_not_immutable]) >>
  Cases_on `sb` >>
  gvs[vyperStateTheory.extend_place_def, vyperStateTheory.bind_def,
    vyperStateTheory.return_def, vyperStateTheory.raise_def, AllCaseEqs()] >>
  Cases_on `v` >>
  gvs[vyperStateTheory.bind_def, vyperStateTheory.lift_option_type_def,
    vyperStateTheory.return_def, vyperStateTheory.raise_def, AllCaseEqs()]
QED

Theorem lookup_global_immutable_root:
  lookup_global cx src0 id0 st = (INL (PlaceR (ImmutablePlace src id path)),st') ==>
  src0 = src /\ id0 = id
Proof
  simp[vyperStateTheory.lookup_global_def, vyperStateTheory.bind_def,
    vyperStateTheory.lift_option_type_def, vyperStateTheory.return_def,
    vyperStateTheory.raise_def, vyperMiscTheory.option_CASE_rator,
    vyperMiscTheory.prod_CASE_rator, vyperStateTheory.var_decl_info_CASE_rator,
    AllCaseEqs()] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem eval_base_place_immutable_root:
  !bt cx st src id path st'.
    eval_base_place cx bt st = (INL (PlaceR (ImmutablePlace src id path)),st') ==>
    base_target_root bt = TopLevelNameTarget (src,id)
Proof
  recInduct base_target_root_ind >> rpt strip_tac >>
  gvs[base_target_root_def, Once vyperInterpreterTheory.evaluate_def,
    vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
    vyperStateTheory.get_scopes_def, vyperStateTheory.type_check_def,
    vyperStateTheory.assert_def, vyperStateTheory.return_def,
    vyperStateTheory.raise_def, AllCaseEqs()]
  >- (drule extend_place_immutable_root >> strip_tac >> gvs[] >>
      first_x_assum drule >> simp[])
  >- (drule extend_place_immutable_root >> strip_tac >> gvs[] >>
      first_x_assum drule >> simp[]) >>
  rename1 `TopLevelNameTarget root` >> PairCases_on `root` >>
  gvs[Once vyperInterpreterTheory.evaluate_def] >>
  drule lookup_global_immutable_root >> simp[]
QED

Theorem eval_target_place_immutable_root:
  eval_target_place cx bt st = (INL (ImmutablePlace src id path),st') ==>
  base_target_root bt = TopLevelNameTarget (src,id)
Proof
  simp[Once vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
    AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  Cases_on `pv` >>
  gvs[vyperStateTheory.get_place_def, vyperStateTheory.return_def,
    vyperStateTheory.raise_def] >>
  metis_tac[eval_base_place_immutable_root]
QED

Theorem typed_base_atarget:
  atarget_accepts env (BaseTarget bt) ty ==>
  IS_SOME (type_place_target env bt)
Proof
  Cases_on `type_place_target env bt` >> simp[atarget_accepts_def]
QED

Theorem typed_tuple_atarget_member:
  atarget_accepts env (TupleTarget tgts) ty /\ MEM tgt tgts ==>
  ?t. well_typed_atarget env tgt t
Proof
  simp[atarget_accepts_def, well_typed_atarget_def] >> rpt strip_tac >>
  drule listTheory.LIST_REL_MEM_IMP >> metis_tac[]
QED

Theorem typed_atarget_base:
  well_typed_atarget env (BaseTarget bt) ty ==>
  IS_SOME (type_place_target env bt)
Proof
  simp[well_typed_atarget_def, well_typed_target_def]
QED

Theorem typed_atarget_tuple_member:
  well_typed_atarget env (TupleTarget tgts) ty /\ MEM tgt tgts ==>
  ?t. well_typed_atarget env tgt t
Proof
  simp[well_typed_atarget_def] >> rpt strip_tac >>
  drule listTheory.LIST_REL_MEM_IMP >> metis_tac[]
QED

Theorem checked_signature_callable_mode:
  check_contract F cx.layouts cx.txn.target mods = SOME art /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  FLOOKUP art.cta_fn_sigs (src,fn) = SOME sig /\
  get_module_code cx src = SOME ts ==>
  lookup_callable_function mode fn ts = lookup_callable_function F fn ts
Proof
  strip_tac >>
  `ALOOKUP mods src = SOME ts` by gvs[vyperContextTheory.get_module_code_def] >>
  drule check_contract_artifact_fields >> strip_tac >>
  `FLOOKUP (build_contract_type_artifact F mods).cta_fn_sigs (src,fn) = SOME sig` by
    gvs[FLOOKUP_DRESTRICT_SOME] >>
  drule_all build_contract_type_artifact_fn_sigs_sound >> strip_tac >>
  gvs[] >>
  Cases_on `lookup_function NONE fn Internal ts` >>
  gvs[vyperInterpreterTheory.lookup_callable_function_def]
QED

(* A typed internal call selects a live signature from the actual checked
   artifact.  No runtime stack or global evaluator soundness is needed. *)
Theorem checked_callable_body_typing:
  check_contract F cx.layouts cx.txn.target mods = SOME art /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  FLOOKUP art.cta_fn_sigs (src,fn) = SOME sig /\
  get_module_code cx src = SOME ts /\
  lookup_callable_function mode fn ts = SOME (mut,nr,args,dflts,ret,ss) ==>
  IS_SOME (type_stmts (function_entry_env art mods src Internal args) ret ss) /\
  well_typed_exprs (defaults_env (function_entry_env art mods src Internal args)) dflts
Proof
  strip_tac >>
  drule_all checked_signature_callable_mode >>
  disch_then (qspec_then `mode` assume_tac) >> gvs[] >>
  `ALOOKUP mods src = SOME ts` by gvs[vyperContextTheory.get_module_code_def] >>
  `function_live cx.layouts cx.txn.target mods
     (live_functions cx.layouts cx.txn.target mods) (src,fn)` by
    (drule check_contract_artifact_fields >>
     strip_tac >> gvs[FLOOKUP_DRESTRICT_SOME]) >>
  drule lookup_callable_function_F_SOME_MEM >> strip_tac >>
  `check_function_body cx.layouts cx.txn.target mods art src Internal mut nr args dflts ret ss` by
    (irule vyperTypeContractContextTheory.check_contract_function_body_MEM >>
     conj_tac
     >- (qexists `F` >> simp[check_function_body_in_mode_def]) >>
     qexistsl [`fn`, `raw`, `ts`] >> simp[]) >>
  gvs[check_function_body_def]
QED

Theorem checked_typed_intcall_body:
  check_contract F cx.layouts cx.txn.target mods = SOME art /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  well_typed_expr env (Call ty (IntCall (src,fn)) es drv) /\
  env.fn_sigs = art.cta_fn_sigs /\
  get_module_code cx src = SOME ts /\
  lookup_callable_function mode fn ts = SOME (mut,nr,args,dflts,ret,ss) ==>
  IS_SOME (type_stmts (function_entry_env art mods src Internal args) ret ss) /\
  well_typed_exprs (defaults_env (function_entry_env art mods src Internal args)) dflts
Proof
  simp[well_typed_expr_def] >> strip_tac >>
  `FLOOKUP art.cta_fn_sigs (src,fn) = SOME sig` by metis_tac[] >>
  drule_all checked_callable_body_typing >> simp[]
QED

Theorem checked_artifact_mutation_root:
  check_contract F layouts addr mods = SOME art /\
  declared_constant mods src id /\
  env.bare_global_assignable = art.cta_bare_global_assignable /\
  env.bare_globals = art.cta_bare_globals /\
  IS_SOME (type_place_target env bt) ==>
  base_target_root bt <> TopLevelNameTarget (src,id)
Proof
  strip_tac >> drule check_contract_artifact_fields >> strip_tac >>
  irule typed_mutation_root_excludes_constant >>
  metis_tac[checked_constant_not_assignable, checked_constant_bare_global]
QED

Theorem checked_artifact_intcall_body:
  check_contract F cx.layouts cx.txn.target mods = SOME art /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  well_typed_expr (artifact_env art mods current_src)
    (Call ty (IntCall (src,fn)) es drv) /\
  get_module_code cx src = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,ss) ==>
  IS_SOME (type_stmts (function_entry_env art mods src Internal args) ret ss) /\
  well_typed_exprs (defaults_env (function_entry_env art mods src Internal args)) dflts
Proof
  strip_tac >>
  `(artifact_env art mods current_src).fn_sigs = art.cta_fn_sigs` by
    simp[artifact_env_def] >>
  drule_all checked_typed_intcall_body >> simp[]
QED

Theorem function_entry_constant_maps:
  (function_entry_env art mods src Internal args).bare_globals = art.cta_bare_globals /\
  (function_entry_env art mods src Internal args).bare_global_assignable =
    art.cta_bare_global_assignable /\
  (function_entry_env art mods src Internal args).fn_sigs = art.cta_fn_sigs /\
  (defaults_env (function_entry_env art mods src Internal args)).bare_globals = art.cta_bare_globals /\
  (defaults_env (function_entry_env art mods src Internal args)).bare_global_assignable =
    art.cta_bare_global_assignable /\
  (defaults_env (function_entry_env art mods src Internal args)).fn_sigs = art.cta_fn_sigs
Proof
  simp[function_entry_env_def, defaults_env_def, artifact_env_def,
    vyperTypeContractContextTheory.FOLDL_extend_local_args_static]
QED

Theorem typed_assign_target:
  IS_SOME (type_stmt env ret (Assign tgt e)) ==>
  atarget_accepts env tgt (expr_type e)
Proof
  simp[type_stmt_def] >> metis_tac[]
QED

Theorem typed_augassign_target:
  IS_SOME (type_stmt env ret (AugAssign ty bt bop e)) ==>
  IS_SOME (type_place_target env bt)
Proof
  simp[type_stmt_def, well_typed_target_def] >> metis_tac[optionTheory.IS_SOME_EXISTS]
QED

Theorem typed_append_target:
  IS_SOME (type_stmt env ret (Append bt e)) ==>
  IS_SOME (type_place_target env bt)
Proof
  Cases_on `type_place_target env bt` >> simp[type_stmt_def]
QED

Theorem typed_pop_target:
  well_typed_expr env (Pop ty bt) ==> IS_SOME (type_place_target env bt)
Proof
  simp[well_typed_expr_def] >> metis_tac[optionTheory.IS_SOME_EXISTS]
QED

(* A cell frame observes exactly one address/source/name, including absence.
   It is independent of the constant-footprint observation relation below. *)
Definition protected_cell_frame_def:
  protected_cell_frame addr src id (st:evaluation_state) (st':evaluation_state) <=>
    OPTION_BIND (ALOOKUP st'.immutables addr)
      (\imms. FLOOKUP (get_source_immutables src imms) id) =
    OPTION_BIND (ALOOKUP st.immutables addr)
      (\imms. FLOOKUP (get_source_immutables src imms) id)
End

Theorem protected_cell_frame_refl[simp]:
  protected_cell_frame addr src id st st
Proof
  simp[protected_cell_frame_def]
QED

Theorem protected_cell_frame_eq:
  st'.immutables = st.immutables ==> protected_cell_frame addr src id st st'
Proof
  simp[protected_cell_frame_def]
QED

Theorem protected_cell_frame_trans:
  protected_cell_frame addr src id s t /\ protected_cell_frame addr src id t u ==>
  protected_cell_frame addr src id s u
Proof
  simp[protected_cell_frame_def]
QED

Theorem set_immutable_other_cell_frame:
  (addr <> cx.txn.target \/ src <> written_src \/ id <> written_id) /\
  set_immutable cx written_src written_id tv v st = (res,st') ==>
  protected_cell_frame addr src id st st'
Proof
  rw[set_immutable_def, get_address_immutables_def, set_address_immutables_def,
     bind_def, lift_option_type_def, return_def, raise_def,
     vyperMiscTheory.option_CASE_rator, AllCaseEqs()] >>
  gvs[protected_cell_frame_def, ALOOKUP_ADELKEY,
      get_source_immutables_def, set_source_immutables_def, FLOOKUP_UPDATE,
      AllCaseEqs()] >>
  rw[ALOOKUP_ADELKEY] >> gvs[ALOOKUP_ADELKEY, FLOOKUP_UPDATE] >>
  Cases_on `written_src = src` >> gvs[FLOOKUP_UPDATE]
QED

Definition place_excludes_cell_def:
  place_excludes_cell cx addr src id p <=>
    !written_src written_id path.
      p = ImmutablePlace written_src written_id path ==>
      addr <> cx.txn.target \/ src <> written_src \/ id <> written_id
End

Theorem write_place_protected_cell:
  place_excludes_cell cx addr src id p /\
  write_place cx p v st = (res,st') ==>
  protected_cell_frame addr src id st st'
Proof
  Cases_on `p`
  >- metis_tac[write_storage_place_immutables, protected_cell_frame_eq]
  >- metis_tac[write_memory_place_immutables, protected_cell_frame_eq] >>
  simp[place_excludes_cell_def, write_place_def, bind_def, ignore_bind_def,
       lift_option_type_def, lift_sum_def, vyperMiscTheory.option_CASE_rator,
       vyperMiscTheory.sum_CASE_rator, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> imp_res_tac get_immutables_state >> gvs[] >>
  metis_tac[set_immutable_other_cell_frame]
QED

Theorem append_place_protected_cell:
  !cx addr src id p v st res st'.
  place_excludes_cell cx addr src id p /\
  append_place cx p v st = (res,st') ==>
  protected_cell_frame addr src id st st'
Proof
  rpt gen_tac >> Cases_on `p`
  >- (strip_tac >> irule protected_cell_frame_eq >>
      metis_tac[append_storage_place_scopes_immutables]) >>
  qmatch_goalsub_abbrev_tac `append_place cx pp v st` >>
  `append_place cx pp v = do
      tv <- place_type_value cx pp; old <- read_place cx pp;
      updated <- lift_sum (append_element tv old v); write_place cx pp updated od`
    by simp[Abbr `pp`, append_place_def] >>
  pop_assum SUBST1_TAC >>
  namedCases_on `place_type_value cx pp st` ["tv_result middle"] >>
  `middle = st` by metis_tac[place_type_value_state] >>
  qpat_x_assum `middle = st` SUBST_ALL_TAC >>
  namedCases_on `tv_result` ["tv", "err"] >>
  simp[bind_def] >>
  namedCases_on `read_place cx pp st` ["old_result middle"] >>
  `middle = st` by metis_tac[read_place_state] >>
  qpat_x_assum `middle = st` SUBST_ALL_TAC >>
  namedCases_on `old_result` ["old", "err"] >> simp[bind_def] >>
  Cases_on `append_element tv old v` >>
  simp[lift_sum_def, bind_def, return_def, raise_def] >>
  metis_tac[write_place_protected_cell, protected_cell_frame_refl]
QED

Theorem pop_place_protected_cell:
  !cx addr src id p st res st'.
  place_excludes_cell cx addr src id p /\
  pop_place cx p st = (res,st') ==>
  protected_cell_frame addr src id st st'
Proof
  rpt gen_tac >> Cases_on `p`
  >- (strip_tac >> irule protected_cell_frame_eq >>
      metis_tac[pop_storage_place_scopes_immutables])
  >- (rename1 `MemoryPlace nm path` >> strip_tac >>
      Cases_on `find_containing_scope nm st.scopes` >>
      gvs[pop_place_def, bind_def, get_scopes_def, lift_option_type_def,
          return_def, raise_def] >> PairCases_on `x` >>
      gvs[bind_def, ignore_bind_def, lift_sum_def, type_check_def, assert_def,
          check_def, set_scopes_def, return_def, raise_def, AllCaseEqs()] >>
      fs[GSYM lift_sum_def, GSYM lift_option_type_def] >>
      imp_res_tac lift_sum_state >> imp_res_tac lift_option_type_state >>
      gvs[] >> pairarg_tac >>
      gvs[bind_def, ignore_bind_def, set_scopes_def, return_def] >>
      irule protected_cell_frame_eq >> simp[]) >>
  simp[place_excludes_cell_def, pop_place_def, bind_def, ignore_bind_def,
       lift_option_type_def, lift_sum_def, vyperMiscTheory.option_CASE_rator,
       vyperMiscTheory.sum_CASE_rator, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> imp_res_tac get_immutables_state >> gvs[] >>
  metis_tac[set_immutable_other_cell_frame]
QED

Theorem typed_target_place_excludes_constant:
  IS_SOME (type_place_target env bt) /\
  FLOOKUP env.bare_global_assignable (src,id) = NONE /\
  IS_SOME (FLOOKUP env.bare_globals (src,id)) /\
  eval_target_place cx bt st = (INL p,st') ==>
  place_excludes_cell cx addr src id p
Proof
  rw[place_excludes_cell_def] >>
  drule eval_target_place_immutable_root >> strip_tac >>
  metis_tac[typed_mutation_root_excludes_constant]
QED

Theorem protected_cell_frame_state:
  (!st res st'. f st = (res,st') ==> st' = st) ==>
  state_rel_frame (protected_cell_frame addr src id) f
Proof
  simp[state_rel_frame_result] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[]
QED

Theorem protected_cell_frame_eq_op:
  (!st res st'. f st = (res,st') ==> st'.immutables = st.immutables) ==>
  state_rel_frame (protected_cell_frame addr src id) f
Proof
  simp[state_rel_frame_result] >> metis_tac[protected_cell_frame_eq]
QED

Theorem frame_lift_option_type_success[local]:
  lift_option_type opt msg st = (INL v,st') <=> opt = SOME v /\ st' = st
Proof
  Cases_on `opt` >> simp[lift_option_type_def, return_def, raise_def] >>
  metis_tac[]
QED

Theorem protected_cell_frame_bind:
  state_rel_frame (protected_cell_frame addr src id) f /\
  (!s v t. f s = (INL v,t) ==>
    state_rel_frame (protected_cell_frame addr src id) (g v)) ==>
  state_rel_frame (protected_cell_frame addr src id) (vyperState$bind f g)
Proof
  strip_tac >> irule state_rel_frame_bind_guarded >> simp[] >>
  metis_tac[protected_cell_frame_trans]
QED

Theorem protected_cell_frame_finally[local]:
  state_rel_frame (protected_cell_frame addr src id) f /\
  state_rel_frame (protected_cell_frame addr src id) g ==>
  state_rel_frame (protected_cell_frame addr src id) (finally f g)
Proof
  simp[state_rel_frame_result, finally_def, ignore_bind_def, bind_def,
    return_def, raise_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >> metis_tac[protected_cell_frame_trans]
QED

Theorem protected_cell_frame_reads:
  state_rel_frame (protected_cell_frame addr src id) (read_result cx pv) /\
  state_rel_frame (protected_cell_frame addr src id) (read_results cx results) /\
  state_rel_frame (protected_cell_frame addr src id) (select_result cx ann pv sb) /\
  state_rel_frame (protected_cell_frame addr src id) (conditional_result cx pv) /\
  state_rel_frame (protected_cell_frame addr src id) (lookup_global cx source nm) /\
  state_rel_frame (protected_cell_frame addr src id) (lookup_flag_mem cx nsid mid) /\
  state_rel_frame (protected_cell_frame addr src id) (read_storage_slot cx b slot ty) /\
  state_rel_frame (protected_cell_frame addr src id) (result_array_length cx pv) /\
  state_rel_frame (protected_cell_frame addr src id) (lift_sum z) /\
  state_rel_frame (protected_cell_frame addr src id) (get_immutables cx source) /\
  state_rel_frame (protected_cell_frame addr src id) (get_place pv) /\
  state_rel_frame (protected_cell_frame addr src id) (read_place cx p) /\
  state_rel_frame (protected_cell_frame addr src id) (place_type_value cx p) /\
  state_rel_frame (protected_cell_frame addr src id) (extend_place cx pv sb) /\
  state_rel_frame (protected_cell_frame addr src id) (resolve_array_element cx b slot ty subs)
Proof
  rpt conj_tac >> irule protected_cell_frame_state >> rpt strip_tac >>
  FIRST [drule_all read_result_state, drule_all read_results_state,
    drule_all select_result_state, drule_all conditional_result_state,
    drule_all lookup_global_state, drule_all lookup_flag_mem_state,
    drule_all read_storage_slot_state, drule_all result_array_length_state,
    drule_all lift_sum_state, drule_all get_immutables_state,
    drule_all get_place_state, drule_all read_place_state,
    drule_all place_type_value_state, drule_all extend_place_state,
    drule_all resolve_array_element_state] >> simp[]
QED

Theorem protected_cell_frame_primitives:
  state_rel_frame (protected_cell_frame addr src id) get_scopes /\
  state_rel_frame (protected_cell_frame addr src id) (set_scopes scs) /\
  state_rel_frame (protected_cell_frame addr src id) push_scope /\
  state_rel_frame (protected_cell_frame addr src id) pop_scope /\
  state_rel_frame (protected_cell_frame addr src id) (push_scope_with_var nm ty v) /\
  state_rel_frame (protected_cell_frame addr src id) (new_variable nm ty v) /\
  state_rel_frame (protected_cell_frame addr src id) (append_logs ls) /\
  state_rel_frame (protected_cell_frame addr src id) (push_log lg) /\
  state_rel_frame (protected_cell_frame addr src id) get_pending_deletions /\
  state_rel_frame (protected_cell_frame addr src id) (update_pending_deletions fp) /\
  state_rel_frame (protected_cell_frame addr src id) (transfer_value sender target amount) /\
  state_rel_frame (protected_cell_frame addr src id) (acquire_nonreentrant_lock target lock view) /\
  state_rel_frame (protected_cell_frame addr src id) (release_nonreentrant_lock target lock) /\
  state_rel_frame (protected_cell_frame addr src id) (push_function fn sc cx) /\
  state_rel_frame (protected_cell_frame addr src id) (pop_function scs) /\
  state_rel_frame (protected_cell_frame addr src id) (write_storage_slot cx b slot ty v) /\
  state_rel_frame (protected_cell_frame addr src id) (set_global cx source nm v)
Proof
  rpt conj_tac >> irule protected_cell_frame_eq_op >>
  simp[get_scopes_def, set_scopes_def, push_scope_def, pop_scope_def,
    push_scope_with_var_def, append_logs_def, push_log_def,
    get_pending_deletions_def, update_pending_deletions_def,
    push_function_def, pop_function_def, return_def, raise_def,
    bind_def, ignore_bind_def, type_check_def, assert_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[new_variable_immutables, transfer_value_immutables,
    acquire_nonreentrant_lock_immutables,
    release_nonreentrant_lock_immutables, write_storage_slot_immutables,
    set_global_immutables]
QED

(* The call oracle and concrete EVM creation adapters update accounts,
   transient storage, logs and request/outcome queues, not immutable cells. *)
Theorem protected_cell_frame_locals:
  (!s t. t.scopes = s.scopes /\ t.immutables = s.immutables ==>
    protected_cell_frame addr src id s t)
Proof
  metis_tac[protected_cell_frame_eq]
QED

Theorem protected_cell_frame_call_primitives:
  state_rel_frame (protected_cell_frame addr src id) (vyperState$return v) /\
  state_rel_frame (protected_cell_frame addr src id) (vyperState$raise e) /\
  state_rel_frame (protected_cell_frame addr src id) get_accounts /\
  state_rel_frame (protected_cell_frame addr src id) get_transient_storage /\
  state_rel_frame (protected_cell_frame addr src id) (update_accounts upd) /\
  state_rel_frame (protected_cell_frame addr src id) (update_transient upd_t) /\
  state_rel_frame (protected_cell_frame addr src id) (adopt_call_outcome rq co) /\
  state_rel_frame (protected_cell_frame addr src id)
    (take_call_outcome target calldata value_opt)
Proof
  conj_tac >- metis_tac[state_rel_frame_locals_primitives, protected_cell_frame_locals] >>
  conj_tac >- metis_tac[state_rel_frame_locals_primitives, protected_cell_frame_locals] >>
  conj_tac >- metis_tac[state_rel_frame_locals_primitives, protected_cell_frame_locals] >>
  conj_tac >- metis_tac[state_rel_frame_locals_primitives, protected_cell_frame_locals] >>
  conj_tac >- metis_tac[state_rel_frame_locals_primitives, protected_cell_frame_locals] >>
  conj_tac >- metis_tac[state_rel_frame_locals_primitives, protected_cell_frame_locals] >>
  conj_tac >- metis_tac[state_rel_frame_locals_primitives, protected_cell_frame_locals] >>
  irule state_rel_frame_locals_take >> metis_tac[protected_cell_frame_locals]
QED

Theorem protected_cell_frame_pure_guards[local]:
  state_rel_frame (protected_cell_frame addr src id) (type_check b msg) /\
  state_rel_frame (protected_cell_frame addr src id) (check b msg) /\
  state_rel_frame (protected_cell_frame addr src id) (lift_option_type opt msg) /\
  state_rel_frame (protected_cell_frame addr src id) (lift_option opt msg)
Proof
  rpt conj_tac >> irule protected_cell_frame_eq_op >>
  simp[type_check_def, check_def, lift_option_type_def, lift_option_def] >>
  rpt strip_tac >>
  gvs[vyperStateTheory.assert_def, return_def, raise_def, AllCaseEqs()] >>
  Cases_on `opt` >> gvs[return_def, raise_def]
QED

Theorem protected_cell_frame_raw_call[local]:
  state_rel_frame (protected_cell_frame addr src id)
    (eval_raw_call cx flags target calldata amount gas)
Proof
  irule protected_cell_frame_eq_op >>
  metis_tac[eval_raw_call_preserves_non_accounts]
QED

Theorem protected_cell_frame_send[local]:
  state_rel_frame (protected_cell_frame addr src id) (eval_send cx has_gas vs)
Proof
  irule protected_cell_frame_eq_op >>
  metis_tac[eval_send_preserves_non_accounts]
QED

Theorem protected_cell_frame_next_gas_reading:
  state_rel_frame (protected_cell_frame addr src id) next_gas_reading
Proof
  simp[state_rel_frame_result] >> rpt strip_tac >>
  irule protected_cell_frame_eq >>
  drule next_gas_reading_state >> rw[] >> simp[]
QED

Theorem protected_cell_frame_create:
  state_rel_frame (protected_cell_frame addr src id)
    (eval_create cx kind has_salt rof arg_tys vs blueprint_size)
Proof
  irule protected_cell_frame_eq_op >>
  metis_tac[eval_create_preserves_scopes_immutables]
QED

Theorem protected_cell_frame_extcall_tail:
  state_rel_frame (protected_cell_frame addr src id) k ==>
  state_rel_frame (protected_cell_frame addr src id)
    (do check success msg;
        update_accounts (K accounts); update_transient (K transient);
        append_logs logs; k od)
Proof
  simp[state_rel_frame_result, concrete_extcall_tail] >>
  Cases_on `success` >> simp[] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule >>
  simp[protected_cell_frame_def]
QED

Theorem protected_cell_frame_mutations:
  place_excludes_cell cx addr src id p ==>
  state_rel_frame (protected_cell_frame addr src id) (write_place cx p v) /\
  state_rel_frame (protected_cell_frame addr src id) (append_place cx p v) /\
  state_rel_frame (protected_cell_frame addr src id) (pop_place cx p)
Proof
  simp[state_rel_frame_result] >>
  metis_tac[write_place_protected_cell, append_place_protected_cell,
    pop_place_protected_cell]
QED

(* A constant footprint records typed roots, rather than evaluator behavior. *)
Definition const_cells_agree_def:
  const_cells_agree roots (st:evaluation_state) <=>
    !addr src id tv root.
      MEM (addr,src,id,tv,root) roots ==>
      ?imms. ALOOKUP st.immutables addr = SOME imms /\
        FLOOKUP (get_source_immutables src imms) id = SOME (tv,root)
End

Definition const_result_at_def:
  const_result_at roots cx ty pv v <=>
    (?tv. evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v) /\
    (pv = Value v \/
     ?src id path tv root etv.
       pv = PlaceR (ImmutablePlace src id path) /\
       MEM (cx.txn.target,src,id,tv,root) roots /\
       subscripts_type tv path = SOME etv /\
       evaluate_type (get_tenv cx) ty = SOME etv /\
       evaluate_subscripts tv root path = INL v)
End

Definition const_results_related_def:
  const_results_related roots cx ty p q <=>
    p = q \/ ?v. const_result_at roots cx ty p v /\ const_result_at roots cx ty q v
End

Definition const_computations_related_def:
  const_computations_related R f g st <=>
    ?a b st'. f st = (a,st') /\ g st = (b,st') /\
      (case (a,b) of
       | (INL x,INL y) => R x y
       | (INR x,INR y) => x = y
       | _ => F)
End

Definition const_result_lists_related_def:
  const_result_lists_related roots cx tys ps qs <=>
    LIST_REL (\(ty,p) (ty',q).
      ty = ty' /\ const_results_related roots cx ty p q)
      (ZIP (tys,ps)) (ZIP (tys,qs)) /\
    LENGTH ps = LENGTH tys /\ LENGTH qs = LENGTH tys
End

Definition const_select_output_def:
  const_select_output (Value v) sb w = Value w /\
  const_select_output (PlaceR (ImmutablePlace src id path)) sb w =
    PlaceR (ImmutablePlace src id (path ++ [sb])) /\
  const_select_output pv sb w = Value w
End

Theorem constant_result_selection_outcome:
  constant_result_shape pv /\
  eval_result_typed (env,cx,st) pv (Type ty) /\
  read_result cx pv st = (INL v,st) /\
  env.type_defs = get_tenv cx /\ evaluate_type env.type_defs ty = SOME tv ==>
  select_result cx ty pv sb st =
    case evaluate_subscripts tv v [sb] of
    | INL w => (INL (const_select_output pv sb w),st)
    | INR err => (INR (Error err),st)
Proof
  rw[constant_result_shape_def]
  >- (Cases_on `evaluate_subscripts tv v [sb]` >>
      gvs[select_result_def, read_result_def, return_def, bind_def,
          lift_option_type_def, lift_sum_def, raise_def,
          const_select_output_def]) >>
  gvs[eval_result_typed_def, runtime_place_typed_def] >>
  `read_place cx (ImmutablePlace src id path) st = (INL v,st)` by
    gvs[read_result_def] >>
  simp[select_result_def, extend_place_def, bind_def, ignore_bind_def,
       lift_sum_def, return_def, extend_memory_place_def,
       const_select_output_def] >>
  Cases_on `evaluate_subscripts tv v [sb]` >> simp[return_def, raise_def]
QED

Theorem const_result_at_observe:
  const_result_at roots cx ty pv v /\ const_cells_agree roots st ==>
  constant_result_shape pv /\
  read_result cx pv st = (INL v,st) /\
  (!env. env.type_defs = get_tenv cx ==>
    eval_result_typed (env,cx,st) pv (Type ty))
Proof
  rw[const_result_at_def, constant_result_shape_def]
  >- simp[read_result_def, return_def]
  >- simp[eval_result_typed_def]
  >- (gvs[const_cells_agree_def] >>
      first_x_assum drule >> strip_tac >>
      simp[read_result_def, read_place_def, get_immutables_def,
           get_address_immutables_def, bind_def, lift_option_type_def,
           lift_sum_def, return_def]) >>
  gvs[eval_result_typed_def, runtime_place_typed_def] >>
  conj_tac >- metis_tac[evaluate_type_well_formed_type_value] >>
  gvs[const_cells_agree_def] >> first_x_assum drule >> strip_tac >>
  simp[place_type_value_def, get_immutables_def, get_address_immutables_def,
       bind_def, lift_option_type_def, return_def]
QED

Theorem constant_result_length_outcome:
  constant_result_shape pv /\ read_result cx pv st = (INL v,st) ==>
  result_array_length cx pv st = result_array_length cx (Value v) st
Proof
  rw[constant_result_shape_def] >>
  gvs[result_array_length_def, read_result_def, bind_def, return_def]
QED

Theorem const_results_related_read:
  const_results_related roots cx ty p q /\ const_cells_agree roots st ==>
  read_result cx p st = read_result cx q st
Proof
  rw[const_results_related_def] >> metis_tac[const_result_at_observe]
QED

Theorem const_result_at_conditional:
  const_result_at roots cx ty pv v /\ const_cells_agree roots st ==>
  conditional_result cx pv st = (INL (Value v),st)
Proof
  strip_tac >> drule_all const_result_at_observe >> strip_tac >>
  gvs[constant_result_shape_def]
  >- gvs[conditional_result_def, read_result_def, return_def] >>
  `?tv. place_type_value cx (ImmutablePlace src id path) st = (INL tv,st)` by
    (qpat_x_assum `!env. _` (qspec_then `ARB with type_defs := get_tenv cx` mp_tac) >>
     simp[eval_result_typed_def, runtime_place_typed_def] >> metis_tac[]) >>
  gvs[conditional_result_def, read_result_def, bind_def, return_def]
QED

Theorem const_results_related_conditional:
  const_results_related roots cx ty p q /\ const_cells_agree roots st ==>
  conditional_result cx p st = conditional_result cx q st
Proof
  rw[const_results_related_def] >> metis_tac[const_result_at_conditional]
QED

Theorem const_result_lists_related_read:
  const_result_lists_related roots cx tys ps qs /\ const_cells_agree roots st ==>
  read_results cx ps st = read_results cx qs st
Proof
  qid_spec_tac `qs` >> qid_spec_tac `ps` >> Induct_on `tys` >>
  Cases_on `ps` >> Cases_on `qs` >>
  simp[const_result_lists_related_def, read_results_def] >>
  rpt strip_tac >>
  `read_result cx h st = read_result cx h' st` by
    metis_tac[const_results_related_read] >>
  simp[bind_def] >>
  Cases_on `read_result cx h' st` >> Cases_on `q` >> simp[] >>
  `r = st` by metis_tac[read_result_state] >> gvs[] >>
  `read_results cx t r = read_results cx t' r` by
    (first_x_assum irule >> simp[const_result_lists_related_def]) >> simp[]
QED

Theorem const_results_related_length:
  const_results_related roots cx ty p q /\ const_cells_agree roots st ==>
  result_array_length cx p st = result_array_length cx q st
Proof
  rw[const_results_related_def] >>
  imp_res_tac const_result_at_observe >>
  metis_tac[constant_result_length_outcome]
QED

Theorem const_result_at_select:
  const_result_at roots cx ty pv v /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  subscript_type tv sb = SOME etv /\
  evaluate_type (get_tenv cx) result_ty = SOME etv /\
  evaluate_subscripts tv v [sb] = INL w ==>
  const_result_at roots cx result_ty (const_select_output pv sb w) w
Proof
  rw[const_result_at_def, const_select_output_def] >> gvs[] >>
  rename1 `subscript_type base_tv sb = SOME etv` >>
  `value_has_type etv w` by
    (irule vyperPlaceStatePreservationTheory.evaluate_subscripts_type >>
     qexistsl [`v`,`[sb]`,`base_tv`] >> simp[subscripts_type_def] >>
     metis_tac[evaluate_type_well_formed_type_value]) >>
  simp[const_select_output_def] >>
  goal_assum (drule_at Any) >>
  simp[vyperPlaceStatePreservationTheory.subscripts_type_append, subscripts_type_def] >>
  drule_all vyperPlaceResultTypingTheory.evaluate_subscripts_append >>
  disch_then (qspec_then `[sb]` mp_tac) >> simp[]
QED

Theorem const_results_related_select:
  const_results_related roots cx ty p q /\ const_cells_agree roots st /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  subscript_type tv sb = SOME etv /\
  evaluate_type (get_tenv cx) result_ty = SOME etv ==>
  (?err. select_result cx ty p sb st = (INR err,st) /\
         select_result cx ty q sb st = (INR err,st)) \/
  (?p' q'. select_result cx ty p sb st = (INL p',st) /\
           select_result cx ty q sb st = (INL q',st) /\
           const_results_related roots cx result_ty p' q') \/ p = q
Proof
  rw[const_results_related_def] >>
  imp_res_tac const_result_at_observe >>
  `select_result cx ty p sb st =
    case evaluate_subscripts tv v [sb] of
    | INL w => (INL (const_select_output p sb w),st)
    | INR err => (INR (Error err),st)` by
    (irule constant_result_selection_outcome >>
     simp[] >> qexists `ARB with type_defs := get_tenv cx` >> simp[]) >>
  `select_result cx ty q sb st =
    case evaluate_subscripts tv v [sb] of
    | INL w => (INL (const_select_output q sb w),st)
    | INR err => (INR (Error err),st)` by
    (irule constant_result_selection_outcome >>
     simp[] >> qexists `ARB with type_defs := get_tenv cx` >> simp[]) >>
  Cases_on `evaluate_subscripts tv v [sb]` >> gvs[] >>
  disj1_tac >>
  simp[const_results_related_def] >>
  metis_tac[const_result_at_select]
QED

Theorem const_results_related_select_total:
  const_results_related roots cx ty p q /\ const_cells_agree roots st /\
  (!v tv w. evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
    evaluate_subscripts tv v [sb] = INL w ==>
    ?etv. subscript_type tv sb = SOME etv /\
      evaluate_type (get_tenv cx) result_ty = SOME etv) ==>
  const_computations_related (const_results_related roots cx result_ty)
    (select_result cx ty p sb) (select_result cx ty q sb) st
Proof
  rw[const_results_related_def]
  >- (Cases_on `select_result cx ty p sb st` >> Cases_on `q` >>
      simp[const_computations_related_def, const_results_related_def]) >>
  imp_res_tac const_result_at_observe >>
  `?tv. evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v` by
    gvs[const_result_at_def] >>
  `select_result cx ty p sb st =
    case evaluate_subscripts tv v [sb] of
    | INL w => (INL (const_select_output p sb w),st)
    | INR err => (INR (Error err),st)` by
    (irule constant_result_selection_outcome >>
     simp[] >> qexists `ARB with type_defs := get_tenv cx` >> simp[]) >>
  `select_result cx ty q sb st =
    case evaluate_subscripts tv v [sb] of
    | INL w => (INL (const_select_output q sb w),st)
    | INR err => (INR (Error err),st)` by
    (irule constant_result_selection_outcome >>
     simp[] >> qexists `ARB with type_defs := get_tenv cx` >> simp[]) >>
  Cases_on `evaluate_subscripts tv v [sb]` >>
  gvs[const_computations_related_def] >>
  simp[const_results_related_def] >>
  metis_tac[const_result_at_select]
QED

Theorem const_results_related_subscript:
  const_results_related roots cx ct p q /\ const_cells_agree roots st /\
  subscript_type_ok ct ie ty /\
  vyperTypeExprResult$subscript_index_matches ct ie idx ==>
  const_computations_related (const_results_related roots cx ty)
    (select_result cx ct p (ValueSubscript idx))
    (select_result cx ct q (ValueSubscript idx)) st
Proof
  strip_tac >> irule const_results_related_select_total >> simp[] >>
  rpt strip_tac >>
  drule_all (constant_subscript_selected_typed
    |> Q.INST [`env` |-> `ARB with type_defs := get_tenv cx`] |> SRULE []) >> simp[] >>
  metis_tac[]
QED

Theorem const_results_related_attribute:
  const_results_related roots cx ct p q /\ const_cells_agree roots st /\
  attribute_type (get_tenv cx) ct id = SOME ty ==>
  const_computations_related (const_results_related roots cx ty)
    (select_result cx ct p (AttrSubscript id))
    (select_result cx ct q (AttrSubscript id)) st
Proof
  strip_tac >> irule const_results_related_select_total >> simp[] >>
  rpt strip_tac >>
  drule_all (constant_attribute_selected_typed
    |> Q.INST [`env` |-> `ARB with type_defs := get_tenv cx`] |> SRULE []) >> simp[] >>
  metis_tac[]
QED

Theorem const_cells_agree_append:
  const_cells_agree (xs ++ ys) st <=>
  const_cells_agree xs st /\ const_cells_agree ys st
Proof
  simp[const_cells_agree_def, MEM_APPEND] >> metis_tac[]
QED

Theorem const_result_at_mono:
  const_result_at xs cx ty pv v /\
  (!root. MEM root xs ==> MEM root ys) ==>
  const_result_at ys cx ty pv v
Proof
  rw[const_result_at_def] >> metis_tac[]
QED

Theorem const_result_at_intro:
  constant_result_shape pv /\
  eval_result_typed (env,cx,st) pv (Type ty) /\
  env.type_defs = get_tenv cx /\ read_result cx pv st = (INL v,st) /\
  (?vt. evaluate_type (get_tenv cx) ty = SOME vt /\ value_has_type vt v) ==>
  ?roots. const_cells_agree roots st /\ const_result_at roots cx ty pv v
Proof
  rw[constant_result_shape_def]
  >- (qexists `[]` >>
      gvs[read_result_def, return_def, eval_result_typed_def,
          const_cells_agree_def, const_result_at_def]) >>
  drule constant_immutable_read_inv >> strip_tac >>
  gvs[eval_result_typed_def, runtime_place_typed_def] >>
  qexists `[(cx.txn.target,src,id,tv,root)]` >>
  simp[const_cells_agree_def, const_result_at_def] >>
  gvs[place_type_value_def, get_immutables_def, get_address_immutables_def,
      bind_def, lift_option_type_def, return_def] >>
  Cases_on `subscripts_type tv path` >> gvs[raise_def, return_def]
QED

Theorem const_results_related_intro:
  constant_result_shape p /\ constant_result_shape q /\
  eval_result_typed (env,cx,st) p (Type ty) /\
  eval_result_typed (env,cx,st) q (Type ty) /\
  env.type_defs = get_tenv cx /\
  read_result cx p st = (INL v,st) /\ read_result cx q st = (INL v,st) /\
  (?tv. evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v) ==>
  ?roots. const_cells_agree roots st /\ const_results_related roots cx ty p q
Proof
  strip_tac >>
  `?xs. const_cells_agree xs st /\ const_result_at xs cx ty p v` by
    (irule const_result_at_intro >> metis_tac[]) >>
  `?ys. const_cells_agree ys st /\ const_result_at ys cx ty q v` by
    (irule const_result_at_intro >> metis_tac[]) >>
  qexists `xs ++ ys` >> simp[const_cells_agree_append, const_results_related_def] >>
  disj2_tac >> qexists `v` >> conj_tac >>
  irule const_result_at_mono >> simp[MEM_APPEND] >> metis_tac[]
QED

Theorem checked_module_consts_env_result_footprint:
  check_contract F cx.layouts cx.txn.target mods = SOME artifact /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  ALOOKUP mods NONE = SOME tops /\
  constants_fold_module mods imms NONE tops FEMPTY = SOME A /\
  ALOOKUP (module_consts_env tops []) id = SOME r /\
  (!src. IS_SOME src ==>
    get_source_immutables src (constant_machine_immutables am cx.txn.target) =
    get_source_immutables src imms) /\
  (!tv v. FLOOKUP A id = SOME (tv,v) ==>
    FLOOKUP (get_source_immutables NONE
      (constant_machine_immutables am cx.txn.target)) id = SOME (tv,v)) /\
  deployment_constant_cells_typed (type_env_all_modules mods) cx.txn.target mods am /\
  well_typed_expr (artifact_env artifact mods current_src) r ==>
  ?v pv roots.
    eval_expr cx r (initial_state am sc) = (INL pv,initial_state am sc) /\
    read_result cx pv (initial_state am sc) = (INL v,initial_state am sc) /\
    const_cells_agree roots (initial_state am sc) /\
    const_results_related roots cx (expr_type r)
      (PlaceR (ImmutablePlace NONE id [])) pv
Proof
  strip_tac >>
  drule_all checked_module_consts_env_replacement >> strip_tac >>
  `constant_value mods (constant_machine_immutables am cx.txn.target) r = SOME v` by
    (qsuff_tac `constant_value mods (merge_constant_imms NONE A imms) r =
       constant_value mods (constant_machine_immutables am cx.txn.target) r`
     >- simp[] >> irule constant_value_closed_stable >>
     simp[merge_constant_imms_imports]) >>
  drule constant_value_eval_expr_observation >>
  disch_then (qspecl_then [`sc`,`cx`,`current_src`,`artifact`,`am`] mp_tac) >>
  simp[] >> strip_tac >>
  `get_tenv cx = type_env_all_modules mods` by metis_tac[get_tenv_sources] >>
  `?tv. evaluate_type (get_tenv cx) (expr_type r) = SOME tv /\ value_has_type tv v` by
    gvs[vyperTypeExprSoundnessTheory.value_runtime_typed_def, artifact_env_def, expr_type_def] >>
  `?ys. const_cells_agree ys (initial_state am sc) /\
    const_result_at ys cx ty pv v` by
    (irule const_result_at_intro >> gvs[] >>
     qexists `artifact_env artifact mods current_src` >>
     gvs[artifact_env_def]) >>
  `FLOOKUP (get_source_immutables NONE
    (constant_machine_immutables am cx.txn.target)) id = SOME (tv,v)` by metis_tac[] >>
  `const_cells_agree [(cx.txn.target,NONE,id,tv,v)] (initial_state am sc)` by
    (Cases_on `ALOOKUP am.immutables cx.txn.target` >>
     gvs[const_cells_agree_def, initial_state_def, constant_machine_immutables_def,
         get_source_immutables_def]) >>
  qexistsl [`v`,`pv`,`[(cx.txn.target,NONE,id,tv,v)] ++ ys`] >>
  simp[const_cells_agree_append, const_results_related_def] >>
  disj2_tac >> qexists `v` >> conj_tac
  >- (gvs[const_result_at_def, subscripts_type_def, evaluate_subscripts_def] >>
      metis_tac[]) >>
  irule const_result_at_mono >> qexists `ys` >> simp[MEM_APPEND] >> simp[]
QED

(* Mutation steps of the mutual frame consume recursive frames only for
   evaluation, and syntactic target typing only for the eventual write. *)
Theorem protected_cell_frame_typed_pop:
  well_typed_expr env (Pop ty bt) /\
  FLOOKUP env.bare_global_assignable (src,id) = NONE /\
  IS_SOME (FLOOKUP env.bare_globals (src,id)) /\
  state_rel_frame (protected_cell_frame addr src id) (eval_target_place cx bt) ==>
  state_rel_frame (protected_cell_frame addr src id) (eval_expr cx (Pop ty bt))
Proof
  strip_tac >> simp_tac bool_ss [Once evaluate_def] >>
  irule protected_cell_frame_bind >> simp[] >> rpt strip_tac >>
  irule (cj 3 protected_cell_frame_mutations) >>
  irule typed_target_place_excludes_constant >>
  metis_tac[typed_pop_target]
QED

Theorem protected_cell_frame_cells_agree:
  const_cells_agree roots st /\
  (!addr src id tv root. MEM (addr,src,id,tv,root) roots ==>
    protected_cell_frame addr src id st st') ==>
  const_cells_agree roots st'
Proof
  rw[const_cells_agree_def] >>
  `?imms. ALOOKUP st.immutables addr = SOME imms /\
    FLOOKUP (get_source_immutables src imms) id = SOME (tv,root)` by metis_tac[] >>
  `protected_cell_frame addr src id st st'` by metis_tac[] >>
  gvs[protected_cell_frame_def] >>
  Cases_on `ALOOKUP st'.immutables addr` >> gvs[]
QED

Theorem protected_cell_frame_typed_append:
  IS_SOME (type_stmt env ret (Append bt e)) /\
  FLOOKUP env.bare_global_assignable (src,id) = NONE /\
  IS_SOME (FLOOKUP env.bare_globals (src,id)) /\
  state_rel_frame (protected_cell_frame addr src id) (eval_target_place cx bt) /\
  state_rel_frame (protected_cell_frame addr src id) (eval_expr cx e) ==>
  state_rel_frame (protected_cell_frame addr src id) (eval_stmt cx (Append bt e))
Proof
  strip_tac >> simp_tac bool_ss [Once evaluate_def] >>
  irule protected_cell_frame_bind >> simp[] >> rpt strip_tac >>
  irule protected_cell_frame_bind >> simp[] >> rpt strip_tac >>
  irule protected_cell_frame_bind >>
  simp[protected_cell_frame_reads] >> rpt strip_tac >>
  irule (cj 2 protected_cell_frame_mutations) >>
  irule typed_target_place_excludes_constant >>
  metis_tac[typed_append_target]
QED

Theorem protected_cell_frame_typed_assign:
  IS_SOME (type_stmt env ret (Assign (BaseTarget bt) e)) /\
  FLOOKUP env.bare_global_assignable (src,id) = NONE /\
  IS_SOME (FLOOKUP env.bare_globals (src,id)) /\
  state_rel_frame (protected_cell_frame addr src id) (eval_target_place cx bt) /\
  state_rel_frame (protected_cell_frame addr src id) (eval_expr cx e) ==>
  state_rel_frame (protected_cell_frame addr src id)
    (eval_stmt cx (Assign (BaseTarget bt) e))
Proof
  strip_tac >> simp_tac bool_ss [Once evaluate_def] >>
  irule protected_cell_frame_bind >> simp[] >> rpt strip_tac >>
  irule protected_cell_frame_bind >> simp[] >> rpt strip_tac >>
  irule protected_cell_frame_bind >>
  simp[protected_cell_frame_reads] >> rpt strip_tac >>
  irule (cj 1 protected_cell_frame_mutations) >>
  irule typed_target_place_excludes_constant >>
  metis_tac[typed_assign_target, typed_base_atarget]
QED

(* Static inputs for the specialized evaluator frame.  No runtime invariant is
   hidden in these abbreviations. *)
Definition frame_maps_def:
  frame_maps env art <=>
    env.bare_globals = art.cta_bare_globals /\
    env.bare_global_assignable = art.cta_bare_global_assignable /\
    env.fn_sigs = art.cta_fn_sigs
End

Definition checked_frame_context_def:
  checked_frame_context cx mods art src id env <=>
    check_contract F cx.layouts cx.txn.target mods = SOME art /\
    ALOOKUP cx.sources cx.txn.target = SOME mods /\
    declared_constant mods src id /\ frame_maps env art
End

Theorem frame_maps_extend_local[simp]:
  frame_maps (extend_local env nm ty writable) art = frame_maps env art
Proof
  simp[frame_maps_def, extend_local_def]
QED

Theorem frame_maps_defaults_env[simp]:
  frame_maps (defaults_env env) art = frame_maps env art
Proof
  simp[frame_maps_def, defaults_env_def]
QED

Theorem frame_maps_function_entry[simp]:
  frame_maps (function_entry_env art mods current_src Internal args) art
Proof
  simp[frame_maps_def, function_entry_constant_maps]
QED

Theorem checked_frame_context_transport:
  checked_frame_context cx mods art src id env /\
  cx'.layouts = cx.layouts /\ cx'.txn.target = cx.txn.target /\
  cx'.sources = cx.sources /\ frame_maps env' art ==>
  checked_frame_context cx' mods art src id env'
Proof
  simp[checked_frame_context_def]
QED

Theorem checked_frame_context_stack[simp]:
  checked_frame_context (cx with stk := stack) mods art src id env =
  checked_frame_context cx mods art src id env
Proof
  simp[checked_frame_context_def]
QED

Theorem checked_frame_context_push_function:
  checked_frame_context cx mods art src id env /\
  push_function fn sc cx st = (INL cx',st') ==>
  checked_frame_context cx' mods art src id env
Proof
  simp[push_function_def, return_def, checked_frame_context_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem checked_frame_intcall_static:
  checked_frame_context cx mods art src id env /\
  well_typed_expr env (Call ty (IntCall (call_src,fn)) es drv) /\
  get_module_code cx call_src = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,ss) ==>
  checked_frame_context cx mods art src id
    (function_entry_env art mods call_src Internal args) /\
  IS_SOME (type_stmts (function_entry_env art mods call_src Internal args) ret ss) /\
  well_typed_exprs (defaults_env (function_entry_env art mods call_src Internal args)) dflts
Proof
  strip_tac >>
  `frame_maps env art` by gvs[checked_frame_context_def] >>
  `env.fn_sigs = art.cta_fn_sigs` by gvs[frame_maps_def] >>
  `check_contract F cx.layouts cx.txn.target mods = SOME art /\
   ALOOKUP cx.sources cx.txn.target = SOME mods` by
    gvs[checked_frame_context_def] >>
  drule_all checked_typed_intcall_body >> strip_tac >>
  simp[] >> irule checked_frame_context_transport >> simp[] >>
  qexistsl [`cx`, `env`] >> simp[]
QED

Theorem type_frame_maps_mutual:
  (!env ret s env'. type_stmt env ret s = SOME env' ==>
    !art. frame_maps env art ==> frame_maps env' art) /\
  (!env ret ss env'. type_stmts env ret ss = SOME env' ==>
    !art. frame_maps env art ==> frame_maps env' art)
Proof
  ho_match_mp_tac type_stmt_ind >>
  rw[type_stmt_def, AllCaseEqs()] >> gvs[]
QED

Theorem type_stmt_frame_maps:
  type_stmt env ret s = SOME env' /\ frame_maps env art ==>
  frame_maps env' art
Proof
  metis_tac[type_frame_maps_mutual]
QED

Theorem type_stmts_frame_maps:
  type_stmts env ret ss = SOME env' /\ frame_maps env art ==>
  frame_maps env' art
Proof
  metis_tac[type_frame_maps_mutual]
QED

Definition writable_atarget_def:
  writable_atarget env g <=> ?ty. atarget_accepts env g ty
End

Theorem writable_atarget_base:
  writable_atarget env (BaseTarget bt) ==> IS_SOME (type_place_target env bt)
Proof
  simp[writable_atarget_def] >> metis_tac[typed_base_atarget]
QED

Theorem well_typed_atarget_writable:
  !g ty. well_typed_atarget env g ty ==> writable_atarget env g
Proof
  Cases
  >- (rpt strip_tac >> simp[writable_atarget_def, atarget_accepts_def] >>
      qexists `ty` >> gvs[well_typed_atarget_def, well_typed_target_def,
        type_widens_to_def]) >>
  rpt strip_tac >> simp[writable_atarget_def, atarget_accepts_def] >>
  qexists `ty` >> simp[]
QED

Theorem writable_atarget_tuple:
  writable_atarget env (TupleTarget gs) ==> EVERY (writable_atarget env) gs
Proof
  simp[writable_atarget_def, EVERY_MEM] >>
  metis_tac[typed_tuple_atarget_member, well_typed_atarget_writable,
    writable_atarget_def]
QED

Theorem type_place_target_subscript_child:
  IS_SOME (type_place_target env (SubscriptTarget bt e)) ==>
  IS_SOME (type_place_target env bt) /\ well_typed_expr env e
Proof
  Cases_on `type_place_target env bt` >>
  simp[Once well_typed_expr_def] >>
  Cases_on `well_typed_expr env e` >> simp[]
QED

Theorem type_place_target_attribute_child:
  IS_SOME (type_place_target env (AttributeTarget bt fld)) ==>
  IS_SOME (type_place_target env bt)
Proof
  Cases_on `type_place_target env bt` >> simp[Once well_typed_expr_def]
QED

Theorem frame_well_typed_exprs_every:
  !es. well_typed_exprs env es <=> EVERY (well_typed_expr env) es
Proof
  Induct >> simp[well_typed_expr_def]
QED

Theorem frame_well_typed_exprs_slices:
  well_typed_exprs env es ==>
  well_typed_exprs env (TAKE n es) /\ well_typed_exprs env (DROP n es)
Proof
  simp[frame_well_typed_exprs_every] >>
  metis_tac[rich_listTheory.EVERY_TAKE, rich_listTheory.EVERY_DROP]
QED

Theorem frame_well_typed_exprs_member:
  well_typed_exprs env es /\ MEM e es ==> well_typed_expr env e
Proof
  simp[frame_well_typed_exprs_every, EVERY_MEM] >> metis_tac[]
QED

Theorem frame_well_typed_exprs_cons:
  well_typed_exprs env (e::es) <=>
  well_typed_expr env e /\ well_typed_exprs env es
Proof
  simp[well_typed_expr_def]
QED

Theorem checked_frame_context_extend_local[simp]:
  checked_frame_context cx mods art src id (extend_local env nm ty writable) =
  checked_frame_context cx mods art src id env
Proof
  simp[checked_frame_context_def]
QED

Theorem checked_frame_context_defaults_env[simp]:
  checked_frame_context cx mods art src id (defaults_env env) =
  checked_frame_context cx mods art src id env
Proof
  simp[checked_frame_context_def]
QED

Theorem checked_frame_context_type_stmt:
  checked_frame_context cx mods art src id env /\
  type_stmt env ret s = SOME env' ==>
  checked_frame_context cx mods art src id env'
Proof
  simp[checked_frame_context_def] >> metis_tac[type_stmt_frame_maps]
QED

Theorem checked_frame_context_type_stmts:
  checked_frame_context cx mods art src id env /\
  type_stmts env ret ss = SOME env' ==>
  checked_frame_context cx mods art src id env'
Proof
  simp[checked_frame_context_def] >> metis_tac[type_stmts_frame_maps]
QED

Theorem checked_frame_context_function_entry:
  checked_frame_context cx mods art src id env ==>
  checked_frame_context cx mods art src id
    (function_entry_env art mods current_src Internal args)
Proof
  simp[checked_frame_context_def]
QED

Theorem checked_frame_context_constant_root:
  checked_frame_context cx mods art src id env ==>
  FLOOKUP env.bare_global_assignable (src,id) = NONE /\
  IS_SOME (FLOOKUP env.bare_globals (src,id))
Proof
  simp[checked_frame_context_def, frame_maps_def] >> rpt strip_tac >>
  drule check_contract_artifact_fields >> strip_tac >> gvs[] >>
  metis_tac[checked_constant_not_assignable, checked_constant_bare_global]
QED

Theorem writable_atarget_member:
  EVERY (writable_atarget env) gs /\ MEM g gs ==> writable_atarget env g
Proof
  simp[EVERY_MEM] >> metis_tac[]
QED

Theorem writable_atarget_cons:
  EVERY (writable_atarget env) (g::gs) <=>
  writable_atarget env g /\ EVERY (writable_atarget env) gs
Proof
  simp[]
QED

Theorem frame_ordered_custom_error_typing:
  well_typed_custom_error env err /\
  order_custom_error_args params err = SOME es ==>
  well_typed_exprs env es
Proof
  simp[well_typed_custom_error_def, frame_well_typed_exprs_every] >>
  rpt strip_tac >> drule order_custom_error_args_perm >>
  metis_tac[sortingTheory.PERM_EVERY]
QED

Theorem protected_cell_frame_return[simp]:
  state_rel_frame (protected_cell_frame addr src id) (return v)
Proof
  simp[state_rel_frame_def, return_def]
QED

Theorem protected_cell_frame_raise[simp]:
  state_rel_frame (protected_cell_frame addr src id) (raise ex)
Proof
  simp[state_rel_frame_def, raise_def]
QED

Theorem protected_cell_frame_read_tail:
  (!v. state_rel_frame (protected_cell_frame addr src id) (k v)) ==>
  state_rel_frame (protected_cell_frame addr src id)
    (bind (read_result cx tv) k)
Proof
  strip_tac >> irule protected_cell_frame_bind >>
  simp[protected_cell_frame_reads]
QED

Theorem protected_cell_frame_string_raise:
  state_rel_frame (protected_cell_frame addr src id)
    (bind (read_result cx tv) (\v.
      bind (lift_option_type (dest_StringV v) "not StringV")
        (\s. raise (AssertException s))))
Proof
  irule protected_cell_frame_read_tail >> gen_tac >> simp_tac bool_ss [] >>
  irule protected_cell_frame_bind >>
  simp[state_rel_frame_locals_primitives, protected_cell_frame_locals,
    protected_cell_frame_call_primitives]
QED

Theorem protected_cell_frame_custom_error_tail:
  state_rel_frame (protected_cell_frame addr src id)
    (bind (lift_option (build_custom_error_data tenv nm tys vs)
      "custom error encoding") (\data. raise (Error (RevertData data))))
Proof
  irule protected_cell_frame_bind >>
  simp[state_rel_frame_locals_primitives, protected_cell_frame_locals,
    protected_cell_frame_call_primitives]
QED

Theorem protected_cell_frame_switch:
  state_rel_frame (protected_cell_frame addr src id) f /\
  state_rel_frame (protected_cell_frame addr src id) g ==>
  state_rel_frame (protected_cell_frame addr src id) (switch_BoolV cx tv f g)
Proof
  strip_tac >> rewrite_tac[switch_BoolV_def] >>
  irule protected_cell_frame_read_tail >> gen_tac >> simp_tac bool_ss [] >>
  rpt IF_CASES_TAC >> simp[state_rel_frame_def, raise_def]
QED

Theorem protected_cell_frame_at:
  f st = (res,st') ==>
  state_rel_frame (protected_cell_frame addr src id) f ==>
  protected_cell_frame addr src id st st'
Proof
  simp[state_rel_frame_result]
QED

Theorem frame_subscript_typing:
  (well_typed_expr env (Subscript ty e idx) \/
   ?vt. type_place_expr env (Subscript ty e idx) = SOME vt) ==>
  (well_typed_expr env e \/ ?vt. type_place_expr env e = SOME vt) /\
  well_typed_expr env idx
Proof
  simp[Once well_typed_expr_def] >>
  simp[Once well_typed_expr_def] >>
  rw[AllCaseEqs()] >> metis_tac[]
QED

Theorem frame_place_expr_other:
  type_place_expr env (IfExp ty a b c) = NONE /\
  type_place_expr env (StructLit ty nm fs) = NONE /\
  type_place_expr env (Attribute ty e fld) = NONE /\
  type_place_expr env (Builtin ty bt es) = NONE /\
  type_place_expr env (TypeBuiltin ty tbt aty es) = NONE /\
  type_place_expr env (Pop ty btgt) = NONE /\
  type_place_expr env (Call ty ct es d) = NONE
Proof
  simp[well_typed_expr_def]
QED

Theorem protected_cell_frame_blueprint[local]:
  state_rel_frame (protected_cell_frame addr src id) (check_create_blueprint has_salt vs)
Proof
  simp[state_rel_frame_result] >> rpt strip_tac >>
  drule check_create_blueprint_result_state >> strip_tac >> simp[]
QED

Theorem protected_cell_frame_ext_call[local]:
  state_rel_frame (protected_cell_frame addr src id)
    (eval_ext_call cx static skip sig opts vs)
Proof
  irule protected_cell_frame_eq_op >>
  metis_tac[eval_ext_call_preserves_non_accounts]
QED

Theorem checked_protected_cell_frame_mutual_aux:
  (!cx s st res st'. eval_stmt cx s st = (res,st') ==>
    !mods art src id env addr ret. checked_frame_context cx mods art src id env /\
      IS_SOME (type_stmt env ret s) ==> protected_cell_frame addr src id st st') /\
  (!cx ss st res st'. eval_stmts cx ss st = (res,st') ==>
    !mods art src id env addr ret. checked_frame_context cx mods art src id env /\
      IS_SOME (type_stmts env ret ss) ==> protected_cell_frame addr src id st st') /\
  (!cx it st res st'. eval_iterator cx it st = (res,st') ==>
    !mods art src id env addr ty. checked_frame_context cx mods art src id env /\
      well_typed_iterator env ty it ==> protected_cell_frame addr src id st st') /\
  (!cx tyv nm body vs st res st'. eval_for cx tyv nm body vs st = (res,st') ==>
    !mods art src id env addr ret. checked_frame_context cx mods art src id env /\
      IS_SOME (type_stmts env ret body) ==> protected_cell_frame addr src id st st') /\
  (!cx e st res st'. eval_expr cx e st = (res,st') ==>
    !mods art src id env addr. checked_frame_context cx mods art src id env /\
      (well_typed_expr env e \/ ?vt. type_place_expr env e = SOME vt) ==>
      protected_cell_frame addr src id st st') /\
  (!cx es st res st'. eval_exprs cx es st = (res,st') ==>
    !mods art src id env addr. checked_frame_context cx mods art src id env /\
      well_typed_exprs env es ==> protected_cell_frame addr src id st st') /\
  (!cx bt st res st'. eval_base_place cx bt st = (res,st') ==>
    !mods art src id env addr. checked_frame_context cx mods art src id env /\
      IS_SOME (type_place_target env bt) ==> protected_cell_frame addr src id st st') /\
  (!cx bt st res st'. eval_target_place cx bt st = (res,st') ==>
    !mods art src id env addr. checked_frame_context cx mods art src id env /\
      IS_SOME (type_place_target env bt) ==> protected_cell_frame addr src id st st') /\
  (!cx g v st res st'. assign_tuple_targets cx g v st = (res,st') ==>
    !mods art src id env addr. checked_frame_context cx mods art src id env /\
      writable_atarget env g ==> protected_cell_frame addr src id st st') /\
  (!cx gs vs st res st'. assign_tuple_target_list cx gs vs st = (res,st') ==>
    !mods art src id env addr. checked_frame_context cx mods art src id env /\
      EVERY (writable_atarget env) gs ==> protected_cell_frame addr src id st st') /\
  (!cx es st res st'. eval_expr_results cx es st = (res,st') ==>
    !mods art src id env addr. checked_frame_context cx mods art src id env /\
      well_typed_exprs env es ==> protected_cell_frame addr src id st st')
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >>
  simp_tac bool_ss [frame_place_expr_other, optionTheory.NOT_NONE_SOME] >>
  rpt strip_tac >>
  qpat_x_assum `_ = (res,st')` mp_tac >>
  simp_tac bool_ss [Once evaluate_def] >>
  simp[return_def, raise_def] >> rpt strip_tac >>
  drule protected_cell_frame_at >> disch_then irule >>
  qpat_x_assum `_ = (res,st')` kall_tac >>
  simp[protected_cell_frame_reads, protected_cell_frame_call_primitives]
  >~ [`type_stmt env ret (Return (SOME e))`]
  >- (`well_typed_expr env e` by
        gvs[type_stmt_def, AllCaseEqs()] >>
      `state_rel_frame (protected_cell_frame addr src id) (eval_expr cx e)` by
        (simp[state_rel_frame_result] >> metis_tac[]) >>
      irule protected_cell_frame_bind >> simp[] >> rpt strip_tac >>
      irule protected_cell_frame_bind >> simp[protected_cell_frame_reads,
        state_rel_frame_def, raise_def])
  >~ [`type_stmt env ret (Raise (RaiseReason e))`]
  >- (`well_typed_expr env e` by gvs[type_stmt_def, AllCaseEqs()] >>
      irule protected_cell_frame_bind >>
      reverse conj_tac >- (simp[state_rel_frame_result] >> metis_tac[]) >>
      simp[protected_cell_frame_string_raise])
  >~ [`type_stmt env ret (Raise (RaiseCustomError err))`]
  >- (`well_typed_custom_error env err` by gvs[type_stmt_def] >>
  Cases_on `err` >> rename1 `CustomError ns pos kwargs` >>
  simp_tac bool_ss [] >>
  Cases_on `get_module_code cx (FST ns)`
  >- simp[state_rel_frame_def, raise_def] >>
  rename1 `get_module_code cx (FST ns) = SOME tops` >>
  Cases_on `lookup_custom_error_args_in (SND ns) tops`
  >- simp[state_rel_frame_def, raise_def] >>
  rename1 `lookup_custom_error_args_in (SND ns) tops = SOME params` >>
  Cases_on `order_custom_error_args params (CustomError ns pos kwargs)`
  >- simp[state_rel_frame_def, raise_def] >>
  simp[] >>
  irule protected_cell_frame_bind >> reverse conj_tac
  >- (simp[state_rel_frame_result] >>
      metis_tac[frame_ordered_custom_error_typing]) >>
  simp[protected_cell_frame_custom_error_tail])
  >~ [`well_typed_expr env (Attribute ty e fld)`]
  >- (`well_typed_expr env e` by
        (qpat_x_assum `well_typed_expr env (Attribute ty e fld)` mp_tac >>
         simp[Once well_typed_expr_def] >> metis_tac[]) >>
      irule protected_cell_frame_bind >>
      simp[protected_cell_frame_reads] >>
      simp[state_rel_frame_result] >> metis_tac[])
  >~ [`well_typed_expr env (Call ty RawLog es d)`]
  >- (`well_typed_exprs env es` by
        (qpat_x_assum `well_typed_expr env (Call ty RawLog es d)` mp_tac >>
         simp[Once well_typed_expr_def] >> metis_tac[]) >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- (simp[state_rel_frame_result] >> metis_tac[]) >>
      rpt strip_tac >> simp_tac bool_ss [ignore_bind_def] >>
      rpt (irule protected_cell_frame_bind >>
        simp[state_rel_frame_locals_primitives, protected_cell_frame_locals,
          protected_cell_frame_primitives] >>
        rpt strip_tac >> simp_tac bool_ss []))
  >~ [`well_typed_expr env (Call ty RawRevert es d)`]
  >- (`well_typed_exprs env es` by
        (qpat_x_assum `well_typed_expr env (Call ty RawRevert es d)` mp_tac >>
         simp[Once well_typed_expr_def] >> metis_tac[]) >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- (simp[state_rel_frame_result] >> metis_tac[]) >>
      rpt strip_tac >> simp_tac bool_ss [ignore_bind_def] >>
      irule protected_cell_frame_bind >>
      simp[state_rel_frame_locals_primitives, protected_cell_frame_locals])
  >~ [`well_typed_expr env (Call ty SelfDestructTarget es d)`]
  >- (`well_typed_exprs env es` by
        (qpat_x_assum `well_typed_expr env (Call ty SelfDestructTarget es d)` mp_tac >>
         simp[Once well_typed_expr_def] >> metis_tac[]) >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- (simp[state_rel_frame_result] >> metis_tac[]) >>
      rpt strip_tac >> simp_tac bool_ss [ignore_bind_def] >>
      rpt (irule protected_cell_frame_bind >>
        simp[state_rel_frame_locals_primitives, protected_cell_frame_locals,
          protected_cell_frame_primitives, protected_cell_frame_call_primitives] >>
        rpt strip_tac >> simp_tac bool_ss []))
  >~ [`type_stmt env ret (Log ns es)`]
  >- (`well_typed_exprs env es` by
        (gvs[type_stmt_def, AllCaseEqs()] >>
         Cases_on `FLOOKUP env.event_fields ns` >> gvs[AllCaseEqs()] >>
         metis_tac[]) >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- (simp[state_rel_frame_result] >> metis_tac[]) >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      irule protected_cell_frame_bind >>
      simp[state_rel_frame_locals_primitives, protected_cell_frame_locals,
        protected_cell_frame_primitives])
  >~ [`type_stmt env ret (Assign (BaseTarget bt) e)`]
  >- (`well_typed_expr env e` by gvs[type_stmt_def, AllCaseEqs()] >>
      `IS_SOME (type_place_target env bt)` by
        metis_tac[typed_assign_target, typed_base_atarget] >>
      drule checked_frame_context_constant_root >> strip_tac >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- (simp[state_rel_frame_result] >> metis_tac[]) >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- (simp[state_rel_frame_result] >> metis_tac[]) >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      irule protected_cell_frame_read_tail >> gen_tac >> simp_tac bool_ss [] >>
      irule (cj 1 protected_cell_frame_mutations) >>
      irule typed_target_place_excludes_constant >> metis_tac[])
  >~ [`type_stmt env ret (Assert e (AssertCustomError err))`]
  >- (`well_typed_expr env e /\ well_typed_custom_error env err` by
    gvs[type_stmt_def, AllCaseEqs()] >>
  irule protected_cell_frame_bind >> reverse conj_tac
  >- (simp[state_rel_frame_result] >> metis_tac[]) >>
  rpt strip_tac >> simp_tac bool_ss [] >>
  irule protected_cell_frame_switch >> conj_tac
  >- simp[state_rel_frame_def, return_def] >>
  Cases_on `err` >> rename1 `CustomError ns pos kwargs` >>
  simp_tac bool_ss [] >>
  Cases_on `get_module_code cx (FST ns)`
  >- simp[state_rel_frame_def, raise_def] >>
  rename1 `get_module_code cx (FST ns) = SOME tops` >>
  Cases_on `lookup_custom_error_args_in (SND ns) tops`
  >- simp[state_rel_frame_def, raise_def] >>
  rename1 `lookup_custom_error_args_in (SND ns) tops = SOME params` >>
  Cases_on `order_custom_error_args params (CustomError ns pos kwargs)`
  >- simp[state_rel_frame_def, raise_def] >>
  simp[] >> irule protected_cell_frame_bind >> reverse conj_tac
  >- (simp[state_rel_frame_result] >>
      metis_tac[frame_ordered_custom_error_typing]) >>
  simp[protected_cell_frame_custom_error_tail])
  >~ [`well_typed_expr env (Builtin ty bt es)`]
  >- (`well_typed_exprs env es` by
    (qpat_x_assum `well_typed_expr env (Builtin ty bt es)` mp_tac >>
     simp[Once well_typed_expr_def] >> metis_tac[]) >>
  rewrite_tac[ignore_bind_def] >> irule protected_cell_frame_bind >>
  reverse conj_tac
  >- metis_tac[state_rel_frame_locals_primitives, protected_cell_frame_locals] >>
  rpt strip_tac >> simp_tac bool_ss [] >>
  irule protected_cell_frame_bind >> conj_tac
  >- (rpt strip_tac >> simp[state_rel_frame_def, return_def]) >>
  Cases_on `bt = Len`
  >- (simp[] >> irule protected_cell_frame_bind >> reverse conj_tac
      >- (`es <> []` by
            (Cases_on `es` >> gvs[type_check_def, assert_def,
              builtin_args_length_ok_def, return_def, raise_def]) >>
          `well_typed_expr env (HD es)` by
            (Cases_on `es` >> gvs[frame_well_typed_exprs_every]) >>
          simp[state_rel_frame_result] >> metis_tac[]) >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      irule protected_cell_frame_bind >>
      simp[protected_cell_frame_reads, protected_cell_frame_call_primitives]) >>
  Cases_on `bt = Env MsgGas`
  >- simp[protected_cell_frame_next_gas_reading] >>
  simp[] >> irule protected_cell_frame_bind >> reverse conj_tac
  >- (simp[state_rel_frame_result] >> metis_tac[]) >>
  rpt strip_tac >> simp_tac bool_ss [] >>
  simp[state_rel_frame_result, bind_def, AllCaseEqs()] >>
  rpt strip_tac >> imp_res_tac lift_sum_state >>
  imp_res_tac precompile_call_success_state >>
  gvs[protected_cell_frame_def, get_accounts_def, return_def])

  >~ [`well_typed_expr env (Call ty (CreateTarget kind has_salt rof kw_order) es drv)`]
  >- (`well_typed_exprs env es` by
        (qpat_x_assum `well_typed_expr env (Call _ _ _ _)` mp_tac >>
         simp[Once well_typed_expr_def] >> metis_tac[]) >>
      Cases_on `kind` >> gvs[]
      >- (irule protected_cell_frame_bind >> conj_tac
          >- simp[protected_cell_frame_create] >>
          simp[state_rel_frame_result] >> metis_tac[])
      >- (irule protected_cell_frame_bind >> conj_tac
          >- simp[protected_cell_frame_create] >>
          simp[state_rel_frame_result] >> metis_tac[])
      >- (drule frame_well_typed_exprs_slices >>
          disch_then (qspec_then `if has_salt then 4 else 3` strip_assume_tac) >>
          irule protected_cell_frame_bind >> reverse conj_tac
          >- (simp[state_rel_frame_result] >> metis_tac[]) >>
          rpt strip_tac >> simp_tac bool_ss [] >>
          irule protected_cell_frame_bind >> simp[protected_cell_frame_blueprint] >>
          rpt strip_tac >> simp_tac bool_ss [] >>
          qpat_x_assum `!a b c d e f. _ /\ _ ==> _` drule >>
          disch_then drule >> strip_tac >>
          irule protected_cell_frame_bind >> reverse conj_tac
          >- (simp[state_rel_frame_result] >> metis_tac[]) >>
          rpt strip_tac >> simp_tac bool_ss [] >>
          irule protected_cell_frame_bind >>
          simp[protected_cell_frame_reads, protected_cell_frame_create]) >>
      `well_typed_exprs env (DROP 2 es)` by
        (irule (cj 2 frame_well_typed_exprs_slices) >> simp[]) >>
      drule frame_well_typed_exprs_slices >>
      disch_then (qspec_then `LENGTH es - ((if has_salt then 1 else 0) + 2)` strip_assume_tac) >>
      `well_typed_exprs env (TAKE 2 es)` by
        (irule (cj 1 frame_well_typed_exprs_slices) >> simp[]) >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- (simp[state_rel_frame_result] >> metis_tac[]) >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      qpat_x_assum `!a b c. eval_exprs _ _ _ = _ ==> _` drule >> strip_tac >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- (simp[state_rel_frame_result] >> metis_tac[]) >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      irule protected_cell_frame_bind >> simp[protected_cell_frame_reads] >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      qpat_x_assum `!a b c d e f g h i. _ /\ _ /\ _ ==> _` drule >>
      disch_then drule >> disch_then drule >> strip_tac >>
      irule protected_cell_frame_bind >>
      simp[protected_cell_frame_create] >>
      simp[state_rel_frame_result] >> metis_tac[])
  >~ [`well_typed_expr env (Call ty (IntCall (call_src,call_fn)) es drv)`]
  >- (rule_assum_tac (SIMP_RULE bool_ss [frame_lift_option_type_success]) >>
      rewrite_tac[ignore_bind_def] >>
      irule protected_cell_frame_bind >>
      simp[protected_cell_frame_pure_guards] >> rpt strip_tac >>
      simp_tac bool_ss [] >>
      irule protected_cell_frame_bind >>
      simp[protected_cell_frame_pure_guards] >> rpt strip_tac >>
      simp_tac bool_ss [] >>
      qpat_x_assum `lift_option_type _ _ _ = (INL _,_)`
        (mp_tac o REWRITE_RULE [frame_lift_option_type_success]) >>
      strip_tac >> full_simp_tac bool_ss [] >>
      irule protected_cell_frame_bind >>
      simp[protected_cell_frame_pure_guards] >> rpt strip_tac >>
      simp_tac bool_ss [] >>
      qpat_x_assum `lift_option_type _ _ _ = (INL _,_)`
        (mp_tac o REWRITE_RULE [frame_lift_option_type_success]) >>
      strip_tac >> full_simp_tac bool_ss [] >>
      rename1 `lookup_callable_function _ _ _ = SOME tup` >>
      PairCases_on `tup` >> gvs[] >>
      drule_all checked_frame_intcall_static >> strip_tac >>
      `well_typed_exprs env es` by
        (qpat_x_assum `well_typed_expr env (Call _ _ _ _)` mp_tac >>
         simp[Once well_typed_expr_def] >> metis_tac[]) >>
      irule protected_cell_frame_bind >>
      simp[protected_cell_frame_pure_guards] >> rpt strip_tac >>
      simp_tac bool_ss [] >>
      qpat_x_assum `!a b c d. type_check _ _ _ = _ /\ type_check _ _ _ = _ ==> _`
        drule >> disch_then drule >> strip_tac >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- (simp[state_rel_frame_result] >> metis_tac[]) >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      irule protected_cell_frame_bind >> simp[protected_cell_frame_primitives] >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      qpat_x_assum `!a b c d e f g h i j k l.
        _ /\ _ /\ _ /\ _ /\ set_scopes _ _ = _ ==> _`
        drule >> disch_then drule >> disch_then drule >> disch_then drule >>
      strip_tac >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- (irule protected_cell_frame_finally >>
          simp[protected_cell_frame_primitives] >>
          irule protected_cell_frame_bind >>
          simp[protected_cell_frame_primitives] >> rpt strip_tac >>
          simp_tac bool_ss [] >>
          `well_typed_exprs (defaults_env (function_entry_env art mods call_src Internal tup2))
             (DROP (LENGTH tup3 - (LENGTH tup2 - LENGTH es)) tup3)` by
            (irule (cj 2 frame_well_typed_exprs_slices) >> simp[]) >>
          simp[state_rel_frame_result] >> rpt strip_tac >>
          first_x_assum irule >>
          conj_tac >- metis_tac[] >>
          conj_tac >- metis_tac[] >>
          qexistsl [`art`, `defaults_env (function_entry_env art mods call_src Internal tup2)`, `mods`] >>
          simp[checked_frame_context_def] >>
          qpat_x_assum `checked_frame_context cx mods art src id env` mp_tac >>
          simp[checked_frame_context_def]) >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      irule protected_cell_frame_bind >> simp[protected_cell_frame_reads] >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      irule protected_cell_frame_bind >> simp[protected_cell_frame_pure_guards] >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      qpat_x_assum `lift_option_type _ _ _ = (INL _,_)`
        (mp_tac o REWRITE_RULE [frame_lift_option_type_success]) >> strip_tac >>
      irule protected_cell_frame_bind >> simp[protected_cell_frame_pure_guards] >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      qpat_x_assum `lift_option_type _ _ _ = (INL _,_)`
        (mp_tac o REWRITE_RULE [frame_lift_option_type_success]) >> strip_tac >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- (Cases_on `tup1` >> simp[protected_cell_frame_return] >>
          Cases_on `cx.nonreentrant_slot` >>
          simp[protected_cell_frame_raise, protected_cell_frame_primitives]) >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      irule protected_cell_frame_bind >> simp[protected_cell_frame_primitives] >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      qpat_x_assum `!a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23. _ ==> _`
        (drule o REWRITE_RULE [ignore_bind_def]) >>
      ntac 7 (disch_then drule) >>
      qmatch_asmsub_rename_tac `(if tup1 then _ else _) _ = (INL lockres,_)` >>
      Cases_on `lockres` >>
      disch_then drule >> disch_then drule >> strip_tac >>
      qpat_x_assum `!st res st' mods art src id env addr.
        eval_expr_results _ _ _ = _ /\ _ ==> _` kall_tac >>
      qpat_x_assum `!a b st res st' mods art src id env addr.
        set_scopes _ _ = _ /\ _ ==> _` kall_tac >>
      irule protected_cell_frame_bind >> conj_tac
      >- (rpt strip_tac >> simp_tac bool_ss [] >>
          irule protected_cell_frame_bind >>
          simp[protected_cell_frame_pure_guards, protected_cell_frame_return]) >>
      irule protected_cell_frame_finally >> reverse conj_tac
      >- (irule protected_cell_frame_bind >> simp[protected_cell_frame_primitives] >>
          rpt strip_tac >> Cases_on `tup1 /\ tup0 <> View /\ tup0 <> Pure` >>
          simp[protected_cell_frame_return] >> Cases_on `cx.nonreentrant_slot` >>
          simp[protected_cell_frame_return, protected_cell_frame_primitives]) >>
      irule state_rel_frame_try >> conj_tac
      >- metis_tac[protected_cell_frame_trans] >>
      conj_tac
      >- (Cases >> simp[handle_function_def, protected_cell_frame_return,
                        protected_cell_frame_raise]) >>
      irule protected_cell_frame_bind >> conj_tac
      >- simp[protected_cell_frame_return] >>
      simp[state_rel_frame_result] >> rpt strip_tac >>
      first_x_assum irule >> conj_tac >- metis_tac[] >>
      qexistsl [`art`, `function_entry_env art mods call_src Internal tup2`, `mods`, `tup4`] >>
      simp[] >> irule checked_frame_context_push_function >>
      goal_assum drule >> simp[])
  >~ [`type_stmt env ret (Append bt e)`]
  >- (`well_typed_expr env e` by
        (qpat_x_assum `IS_SOME (type_stmt env ret (Append bt e))` mp_tac >>
         simp[type_stmt_def] >>
         namedCases_on `type_place_target env bt` ["", "vt"] >> simp[] >>
         Cases_on `vt` >> simp[] >>
         rename1 `Type tyv` >> Cases_on `tyv` >> simp[] >>
         rename1 `ArrayT elem sz` >> Cases_on `sz` >> simp[] >>
         metis_tac[]) >>
      `IS_SOME (type_place_target env bt)` by metis_tac[typed_append_target] >>
      drule checked_frame_context_constant_root >> strip_tac >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- (simp[state_rel_frame_result] >> metis_tac[]) >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- (simp[state_rel_frame_result] >> metis_tac[]) >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      irule protected_cell_frame_read_tail >> gen_tac >> simp_tac bool_ss [] >>
      irule (cj 2 protected_cell_frame_mutations) >>
      irule typed_target_place_excludes_constant >> metis_tac[])
  >~ [`well_typed_iterator env ty (Range e e')`]
  >- (`well_typed_expr env e /\ well_typed_expr env e'` by
        gvs[well_typed_iterator_def] >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- (simp[state_rel_frame_result] >> metis_tac[]) >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- simp[protected_cell_frame_reads] >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- (simp[state_rel_frame_result] >> metis_tac[]) >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      irule protected_cell_frame_read_tail >> gen_tac >> simp_tac bool_ss [] >>
      irule protected_cell_frame_bind >> simp[protected_cell_frame_reads])
  >~ [`type_stmt env ret (Assert e (AssertReason e'))`]
  >- (`well_typed_expr env e /\ well_typed_expr env e'` by
        gvs[type_stmt_def, AllCaseEqs()] >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- (simp[state_rel_frame_result] >> metis_tac[]) >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      irule protected_cell_frame_switch >> simp[] >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- (simp[state_rel_frame_result] >> metis_tac[]) >>
      simp[protected_cell_frame_string_raise])
  >~ [`well_typed_expr env (Subscript ty e e')`]
  >- (`state_rel_frame (protected_cell_frame addr src id) (eval_expr cx e)` by
        (simp[state_rel_frame_result] >>
         metis_tac[frame_subscript_typing]) >>
      `well_typed_expr env e'` by metis_tac[frame_subscript_typing] >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- (simp[state_rel_frame_result] >> metis_tac[]) >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- (simp[state_rel_frame_result] >> metis_tac[]) >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      irule protected_cell_frame_read_tail >> simp[protected_cell_frame_reads])
  >~ [`type_place_expr env (Subscript ty e e') = SOME vt`]
  >- (`state_rel_frame (protected_cell_frame addr src id) (eval_expr cx e)` by
        (simp[state_rel_frame_result] >> metis_tac[frame_subscript_typing]) >>
      `well_typed_expr env e'` by metis_tac[frame_subscript_typing] >>
      irule protected_cell_frame_bind >> reverse conj_tac >- simp[] >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- (simp[state_rel_frame_result] >> metis_tac[]) >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      irule protected_cell_frame_read_tail >> simp[protected_cell_frame_reads])
  >~ [`type_stmt env ret (Assign (TupleTarget gs) e)`]
  >- (`well_typed_expr env e` by gvs[type_stmt_def, AllCaseEqs()] >>
      `writable_atarget env (TupleTarget gs)` by
        metis_tac[typed_assign_target, writable_atarget_def] >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- (simp[state_rel_frame_result] >> metis_tac[]) >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- simp[protected_cell_frame_reads] >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      simp[state_rel_frame_result] >> metis_tac[])
  >~ [`type_stmts env ret (s::ss)`]
  >- (qpat_x_assum `IS_SOME (type_stmts env ret (s::ss))` mp_tac >>
      simp[Once type_stmt_def] >>
      namedCases_on `type_stmt env ret s` ["", "env'"] >> simp[] >> strip_tac >>
      `checked_frame_context cx mods art src id env'` by
        (irule checked_frame_context_type_stmt >> metis_tac[]) >>
      `IS_SOME (type_stmt env ret s)` by simp[] >>
      rewrite_tac[ignore_bind_def] >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- (simp[state_rel_frame_result] >> metis_tac[]) >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      simp[state_rel_frame_result] >> metis_tac[])
  >~ [`type_place_expr env (Name ty nm) = SOME vt`]
  >- (irule protected_cell_frame_eq_op >>
      simp[get_scopes_def, bind_def, ignore_bind_def, type_check_def,
        vyperStateTheory.assert_def, return_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[])
  >~ [`well_typed_expr env (StructLit ty nm fs)`]
  >- (`well_typed_exprs env (MAP SND fs)` by
        (`!ks. well_typed_named_exprs env ks ==>
           well_typed_exprs env (MAP SND ks)` by
           (Induct >> simp[well_typed_expr_def] >>
            Cases >> simp[well_typed_expr_def]) >>
         gvs[Once well_typed_expr_def] >> metis_tac[]) >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- (simp[state_rel_frame_result] >> metis_tac[]) >>
      simp[protected_cell_frame_call_primitives])
  >~ [`type_stmt env ret (AnnAssign nm typ e)`]
  >- (`well_typed_expr env e` by gvs[type_stmt_def, AllCaseEqs()] >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- (Cases_on `evaluate_type (get_tenv cx) typ` >>
          simp[lift_option_type_def, protected_cell_frame_return,
            protected_cell_frame_raise]) >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- (simp[state_rel_frame_result] >> metis_tac[]) >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      irule protected_cell_frame_read_tail >>
      simp[protected_cell_frame_primitives])
  >~ [`well_typed_expr env (Call ty (RawCallCalldataTarget flags) es d)`]
  >- (`well_typed_exprs env es` by gvs[Once well_typed_expr_def] >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- (simp[state_rel_frame_result] >> metis_tac[]) >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      rewrite_tac[ignore_bind_def] >>
      irule protected_cell_frame_bind >> simp[protected_cell_frame_pure_guards] >>
      rpt strip_tac >> irule protected_cell_frame_bind >>
      simp[protected_cell_frame_pure_guards] >> rpt strip_tac >>
      irule protected_cell_frame_bind >>
      simp[protected_cell_frame_pure_guards, protected_cell_frame_raw_call])
  >~ [`well_typed_expr env (Call ty (RawCallTarget flags) es d)`]
  >- (`well_typed_exprs env es` by gvs[Once well_typed_expr_def] >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- (simp[state_rel_frame_result] >> metis_tac[]) >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      rewrite_tac[ignore_bind_def] >>
      irule protected_cell_frame_bind >> simp[protected_cell_frame_pure_guards] >>
      rpt strip_tac >> irule protected_cell_frame_bind >>
      simp[protected_cell_frame_pure_guards] >> rpt strip_tac >>
      irule protected_cell_frame_bind >>
      simp[protected_cell_frame_pure_guards] >> rpt strip_tac >>
      irule protected_cell_frame_bind >>
      simp[protected_cell_frame_pure_guards, protected_cell_frame_raw_call])
  >~ [`well_typed_expr env (Call ty (Send has_gas) es d)`]
  >- (`well_typed_exprs env es` by gvs[Once well_typed_expr_def] >>
      rewrite_tac[ignore_bind_def] >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- simp[protected_cell_frame_pure_guards] >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- (simp[state_rel_frame_result] >> metis_tac[]) >>
      simp[protected_cell_frame_send])
  >~ [`well_typed_expr env (TypeBuiltin ty tb typ es)`]
  >- (`well_typed_exprs env es` by gvs[Once well_typed_expr_def] >>
      rewrite_tac[ignore_bind_def] >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- simp[protected_cell_frame_pure_guards] >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- (simp[state_rel_frame_result] >> metis_tac[]) >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      irule protected_cell_frame_bind >>
      simp[protected_cell_frame_reads])
  >~ [`well_typed_expr env (IfExp ty e e' e'')`]
  >- (`well_typed_expr env e /\ well_typed_expr env e' /\
        well_typed_expr env e''` by gvs[Once well_typed_expr_def] >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- (simp[state_rel_frame_result] >> metis_tac[]) >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- (irule protected_cell_frame_switch >>
          simp[state_rel_frame_result] >> metis_tac[]) >>
      simp[protected_cell_frame_reads])
  >~ [`type_stmt env ret (If e ss ss')`]
  >- (`well_typed_expr env e /\ IS_SOME (type_stmts env ret ss) /\
        IS_SOME (type_stmts env ret ss')` by
        gvs[type_stmt_def, AllCaseEqs()] >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- (simp[state_rel_frame_result] >> metis_tac[]) >>
      rpt strip_tac >> simp_tac bool_ss [] >> rewrite_tac[ignore_bind_def] >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- simp[protected_cell_frame_primitives] >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      irule protected_cell_frame_finally >>
      simp[protected_cell_frame_primitives] >>
      irule protected_cell_frame_switch >>
      simp[state_rel_frame_result] >> metis_tac[])
  >~ [`EVERY (writable_atarget env) (g::gs)`]
  >- (gvs[EVERY_DEF] >> rewrite_tac[ignore_bind_def] >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- (simp[state_rel_frame_result] >> metis_tac[]) >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      Cases_on `v'` >> simp[state_rel_frame_result] >> metis_tac[])
  >~ [`type_stmt env ret (AugAssign ty bt bop e)`]
  >- (`well_typed_expr env e` by gvs[type_stmt_def, AllCaseEqs()] >>
      `IS_SOME (type_place_target env bt)` by metis_tac[typed_augassign_target] >>
      drule checked_frame_context_constant_root >> strip_tac >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- (simp[state_rel_frame_result] >> metis_tac[]) >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- simp[protected_cell_frame_reads] >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- simp[protected_cell_frame_reads] >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- (simp[state_rel_frame_result] >> metis_tac[]) >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      irule protected_cell_frame_read_tail >> gen_tac >> simp_tac bool_ss [] >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- simp[protected_cell_frame_reads] >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      irule (cj 1 protected_cell_frame_mutations) >>
      irule typed_target_place_excludes_constant >> metis_tac[])
  >~ [`IS_SOME (type_stmt env ret (For nm typ it n body'))`]
  >- (qpat_x_assum `IS_SOME (type_stmt _ _ _)` mp_tac >>
      simp[Once type_stmt_def] >> strip_tac >>
      rewrite_tac[ignore_bind_def] >>
      irule protected_cell_frame_bind >> simp[protected_cell_frame_pure_guards] >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      qpat_x_assum `!a b c. lift_option_type _ _ _ = _ ==> _` drule >> strip_tac >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- (simp[state_rel_frame_result] >> metis_tac[]) >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      irule protected_cell_frame_bind >> simp[protected_cell_frame_pure_guards] >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      qpat_x_assum `!a b c d e f g h i. _ /\ _ /\ _ ==> _` drule >>
      disch_then drule >> disch_then drule >> strip_tac >>
      simp[state_rel_frame_result] >> rpt strip_tac >> first_x_assum irule >>
      conj_tac >- metis_tac[] >>
      qexistsl [`art`, `extend_local env nm typ F`, `mods`, `ret`] >> simp[])
  >~ [`eval_for cx tyv nm body' vs`]
  >- (rewrite_tac[ignore_bind_def] >>
      irule protected_cell_frame_bind >> simp[protected_cell_frame_primitives] >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      qpat_x_assum `!a b c. push_scope_with_var _ _ _ _ = _ ==> _` drule >> strip_tac >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- (irule protected_cell_frame_finally >> simp[protected_cell_frame_primitives] >>
          irule state_rel_frame_try >> conj_tac
          >- metis_tac[protected_cell_frame_trans] >>
          conj_tac
          >- (Cases >> simp[handle_loop_exception_def, protected_cell_frame_return,
                            protected_cell_frame_raise]) >>
          irule protected_cell_frame_bind >> simp[protected_cell_frame_return] >>
          simp[state_rel_frame_result] >> metis_tac[]) >>
      rpt strip_tac >> simp_tac bool_ss [] >> Cases_on `v'` >>
      simp[protected_cell_frame_return] >>
      qpat_x_assum `!a b c d e. _ /\ _ ==> _`
        (mp_tac o REWRITE_RULE [ignore_bind_def]) >>
      disch_then drule >> strip_tac >>
      simp[state_rel_frame_result] >> metis_tac[])
  >~ [`well_typed_expr env (Call ty (ExtCall static skip sig opts) es drv)`]
  >- (PairCases_on `sig` >> gvs[] >>
      `well_typed_exprs env es` by
        (qpat_x_assum `well_typed_expr env (Call _ _ _ _)` mp_tac >>
         simp[Once well_typed_expr_def] >> metis_tac[]) >>
      `well_typed_exprs env (DROP 1 es)` by
        (irule (cj 2 frame_well_typed_exprs_slices) >> simp[]) >>
      drule frame_well_typed_exprs_slices >>
      disch_then (qspec_then `LENGTH sig1` strip_assume_tac) >>
      `well_typed_exprs env (TAKE 1 es)` by
        (irule (cj 1 frame_well_typed_exprs_slices) >> simp[]) >>
      `well_typed_exprs env (DROP (1 + LENGTH sig1) es)` by
        (irule (cj 2 frame_well_typed_exprs_slices) >> simp[]) >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- (simp[state_rel_frame_result] >> metis_tac[]) >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      qpat_x_assum `!a b c. eval_exprs _ _ _ = _ ==> _` drule >> strip_tac >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- (simp[state_rel_frame_result] >> metis_tac[]) >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      qpat_x_assum `!a b c d e f. eval_exprs _ _ _ = _ /\ _ ==> _` drule >>
      disch_then drule >> strip_tac >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- (simp[state_rel_frame_result] >> rpt strip_tac >>
          gvs[arithmeticTheory.ADD_COMM] >> metis_tac[]) >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      irule protected_cell_frame_bind >>
      simp[protected_cell_frame_reads, protected_cell_frame_ext_call])
  >~ [`IS_SOME (type_place_target env (NameTarget name))`]
  >- (rewrite_tac[ignore_bind_def] >>
      irule protected_cell_frame_bind >> simp[protected_cell_frame_primitives] >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      irule protected_cell_frame_bind >>
      simp[protected_cell_frame_pure_guards, protected_cell_frame_return])
  >~ [`IS_SOME (type_place_target env (AttributeTarget bt fld))`]
  >- (`IS_SOME (type_place_target env bt)` by
        metis_tac[type_place_target_attribute_child] >>
      irule protected_cell_frame_bind >> conj_tac
      >- simp[protected_cell_frame_reads] >>
      simp[state_rel_frame_result] >> metis_tac[])
  >~ [`well_typed_expr env (Name ty name)`]
  >- (rewrite_tac[ignore_bind_def] >>
      irule protected_cell_frame_bind >> simp[protected_cell_frame_primitives] >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      irule protected_cell_frame_bind >>
      simp[protected_cell_frame_pure_guards, protected_cell_frame_return])
  >~ [`well_typed_expr env (Pop ty bt)`]
  >- (`IS_SOME (type_place_target env bt)` by metis_tac[typed_pop_target] >>
      drule checked_frame_context_constant_root >> strip_tac >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- (simp[state_rel_frame_result] >> metis_tac[]) >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      irule (cj 3 protected_cell_frame_mutations) >>
      irule typed_target_place_excludes_constant >> metis_tac[])
  >~ [`IS_SOME (type_stmt env ret (Expr e))`]
  >- (`well_typed_expr env e` by
        (qpat_x_assum `IS_SOME (type_stmt _ _ _)` mp_tac >>
         simp[Once type_stmt_def]) >>
      irule protected_cell_frame_bind >> conj_tac
      >- simp[protected_cell_frame_pure_guards] >>
      simp[state_rel_frame_result] >> metis_tac[])
  >~ [`IS_SOME (type_stmt env ret (Assert e AssertBare))`]
  >- (`well_typed_expr env e` by
        (qpat_x_assum `IS_SOME (type_stmt _ _ _)` mp_tac >>
         simp[Once type_stmt_def] >> metis_tac[]) >>
      irule protected_cell_frame_bind >> conj_tac
      >- (rpt strip_tac >> simp_tac bool_ss [] >> irule protected_cell_frame_switch >>
          simp[protected_cell_frame_return, protected_cell_frame_raise]) >>
      simp[state_rel_frame_result] >> metis_tac[])
  >~ [`IS_SOME (type_stmt env ret (Assert e AssertUnreachable))`]
  >- (`well_typed_expr env e` by
        (qpat_x_assum `IS_SOME (type_stmt _ _ _)` mp_tac >>
         simp[Once type_stmt_def] >> metis_tac[]) >>
      irule protected_cell_frame_bind >> conj_tac
      >- (rpt strip_tac >> simp_tac bool_ss [] >> irule protected_cell_frame_switch >>
          simp[protected_cell_frame_return, protected_cell_frame_raise]) >>
      simp[state_rel_frame_result] >> metis_tac[])
  >~ [`well_typed_iterator env ty (Array e)`]
  >- (`well_typed_expr env e` by gvs[well_typed_iterator_def] >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- (simp[state_rel_frame_result] >> metis_tac[]) >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      irule protected_cell_frame_read_tail >> gen_tac >> simp_tac bool_ss [] >>
      irule protected_cell_frame_bind >> simp[protected_cell_frame_pure_guards] >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      irule protected_cell_frame_bind >>
      simp[protected_cell_frame_pure_guards, protected_cell_frame_return])
  >~ [`IS_SOME (type_place_target env (SubscriptTarget bt e))`]
  >- (drule type_place_target_subscript_child >> strip_tac >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- (simp[state_rel_frame_result] >> metis_tac[]) >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      qpat_x_assum `!a b c. eval_base_place _ _ _ = _ ==> _` drule >> strip_tac >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- (simp[state_rel_frame_result] >> metis_tac[]) >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      irule protected_cell_frame_read_tail >> simp[protected_cell_frame_reads])
  >~ [`writable_atarget env (TupleTarget gs)`]
  >- (drule writable_atarget_tuple >> strip_tac >> Cases_on `v` >>
      simp[protected_cell_frame_raise] >> rename1 `ArrayV av` >>
      Cases_on `av` >> simp[protected_cell_frame_raise] >>
      gvs[] >> simp[state_rel_frame_result] >> metis_tac[])
  >~ [`well_typed_exprs env (e::es)`]
  >- (gvs[Once well_typed_expr_def] >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- (simp[state_rel_frame_result] >> metis_tac[]) >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- simp[protected_cell_frame_reads] >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      irule protected_cell_frame_bind >> simp[protected_cell_frame_return] >>
      simp[state_rel_frame_result] >> metis_tac[])
  >~ [`well_typed_exprs env (e::es)`]
  >- (gvs[Once well_typed_expr_def] >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- (simp[state_rel_frame_result] >> metis_tac[]) >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      irule protected_cell_frame_bind >> simp[protected_cell_frame_return] >>
      simp[state_rel_frame_result] >> metis_tac[])
  >~ [`writable_atarget env (BaseTarget bt)`]
  >- (drule writable_atarget_base >> strip_tac >>
      drule checked_frame_context_constant_root >> strip_tac >>
      irule protected_cell_frame_bind >> reverse conj_tac
      >- (simp[state_rel_frame_result] >> metis_tac[]) >>
      rpt strip_tac >> simp_tac bool_ss [] >>
      irule (cj 1 protected_cell_frame_mutations) >>
      irule typed_target_place_excludes_constant >> metis_tac[])
  >~ [`bind (eval_base_place cx bt) _`]
  >- (irule protected_cell_frame_bind >> conj_tac
      >- simp[protected_cell_frame_reads] >>
      simp[state_rel_frame_result] >> metis_tac[])
QED


Theorem checked_protected_cell_frame_mutual:
  (!cx s st res st'. eval_stmt cx s st = (res,st') ==>
    !mods art src id env addr ret. checked_frame_context cx mods art src id env /\
      IS_SOME (type_stmt env ret s) ==> protected_cell_frame addr src id st st') /\
  (!cx ss st res st'. eval_stmts cx ss st = (res,st') ==>
    !mods art src id env addr ret. checked_frame_context cx mods art src id env /\
      IS_SOME (type_stmts env ret ss) ==> protected_cell_frame addr src id st st') /\
  (!cx it st res st'. eval_iterator cx it st = (res,st') ==>
    !mods art src id env addr ty. checked_frame_context cx mods art src id env /\
      well_typed_iterator env ty it ==> protected_cell_frame addr src id st st') /\
  (!cx tyv nm body vs st res st'. eval_for cx tyv nm body vs st = (res,st') ==>
    !mods art src id env addr ret. checked_frame_context cx mods art src id env /\
      IS_SOME (type_stmts env ret body) ==> protected_cell_frame addr src id st st') /\
  (!cx e st res st'. eval_expr cx e st = (res,st') ==>
    !mods art src id env addr. checked_frame_context cx mods art src id env /\
      well_typed_expr env e ==> protected_cell_frame addr src id st st') /\
  (!cx es st res st'. eval_exprs cx es st = (res,st') ==>
    !mods art src id env addr. checked_frame_context cx mods art src id env /\
      well_typed_exprs env es ==> protected_cell_frame addr src id st st') /\
  (!cx bt st res st'. eval_base_place cx bt st = (res,st') ==>
    !mods art src id env addr. checked_frame_context cx mods art src id env /\
      IS_SOME (type_place_target env bt) ==> protected_cell_frame addr src id st st') /\
  (!cx bt st res st'. eval_target_place cx bt st = (res,st') ==>
    !mods art src id env addr. checked_frame_context cx mods art src id env /\
      IS_SOME (type_place_target env bt) ==> protected_cell_frame addr src id st st') /\
  (!cx g v st res st'. assign_tuple_targets cx g v st = (res,st') ==>
    !mods art src id env addr. checked_frame_context cx mods art src id env /\
      writable_atarget env g ==> protected_cell_frame addr src id st st') /\
  (!cx gs vs st res st'. assign_tuple_target_list cx gs vs st = (res,st') ==>
    !mods art src id env addr. checked_frame_context cx mods art src id env /\
      EVERY (writable_atarget env) gs ==> protected_cell_frame addr src id st st') /\
  (!cx es st res st'. eval_expr_results cx es st = (res,st') ==>
    !mods art src id env addr. checked_frame_context cx mods art src id env /\
      well_typed_exprs env es ==> protected_cell_frame addr src id st st')
Proof
  conj_tac >- ACCEPT_TAC (cj 1 checked_protected_cell_frame_mutual_aux) >>
  conj_tac >- ACCEPT_TAC (cj 2 checked_protected_cell_frame_mutual_aux) >>
  conj_tac >- ACCEPT_TAC (cj 3 checked_protected_cell_frame_mutual_aux) >>
  conj_tac >- ACCEPT_TAC (cj 4 checked_protected_cell_frame_mutual_aux) >>
  conj_tac >- metis_tac[cj 5 checked_protected_cell_frame_mutual_aux] >>
  conj_tac >- ACCEPT_TAC (cj 6 checked_protected_cell_frame_mutual_aux) >>
  conj_tac >- ACCEPT_TAC (cj 7 checked_protected_cell_frame_mutual_aux) >>
  conj_tac >- ACCEPT_TAC (cj 8 checked_protected_cell_frame_mutual_aux) >>
  conj_tac >- ACCEPT_TAC (cj 9 checked_protected_cell_frame_mutual_aux) >>
  conj_tac >- ACCEPT_TAC (cj 10 checked_protected_cell_frame_mutual_aux) >>
  ACCEPT_TAC (cj 11 checked_protected_cell_frame_mutual_aux)
QED

Theorem checked_eval_stmt_protected_cell_frame:
  checked_frame_context cx mods art src id env /\ IS_SOME (type_stmt env ret s) ==>
  state_rel_frame (protected_cell_frame addr src id) (eval_stmt cx s)
Proof
  simp[state_rel_frame_result] >> metis_tac[cj 1 checked_protected_cell_frame_mutual]
QED

Theorem checked_eval_stmts_protected_cell_frame:
  checked_frame_context cx mods art src id env /\ IS_SOME (type_stmts env ret ss) ==>
  state_rel_frame (protected_cell_frame addr src id) (eval_stmts cx ss)
Proof
  simp[state_rel_frame_result] >> metis_tac[cj 2 checked_protected_cell_frame_mutual]
QED

Theorem checked_eval_iterator_protected_cell_frame:
  checked_frame_context cx mods art src id env /\ well_typed_iterator env ty it ==>
  state_rel_frame (protected_cell_frame addr src id) (eval_iterator cx it)
Proof
  simp[state_rel_frame_result] >> metis_tac[cj 3 checked_protected_cell_frame_mutual]
QED

Theorem checked_eval_for_protected_cell_frame:
  checked_frame_context cx mods art src id env /\ IS_SOME (type_stmts env ret ss) ==>
  state_rel_frame (protected_cell_frame addr src id) (eval_for cx tyv nm ss vs)
Proof
  simp[state_rel_frame_result] >> metis_tac[cj 4 checked_protected_cell_frame_mutual]
QED

Theorem checked_eval_expr_protected_cell_frame:
  checked_frame_context cx mods art src id env /\ well_typed_expr env e ==>
  state_rel_frame (protected_cell_frame addr src id) (eval_expr cx e)
Proof
  simp[state_rel_frame_result] >> metis_tac[cj 5 checked_protected_cell_frame_mutual]
QED

Theorem checked_eval_exprs_protected_cell_frame:
  checked_frame_context cx mods art src id env /\ well_typed_exprs env es ==>
  state_rel_frame (protected_cell_frame addr src id) (eval_exprs cx es)
Proof
  simp[state_rel_frame_result] >> metis_tac[cj 6 checked_protected_cell_frame_mutual]
QED

Theorem checked_eval_base_place_protected_cell_frame:
  checked_frame_context cx mods art src id env /\ IS_SOME (type_place_target env bt) ==>
  state_rel_frame (protected_cell_frame addr src id) (eval_base_place cx bt)
Proof
  simp[state_rel_frame_result] >> metis_tac[cj 7 checked_protected_cell_frame_mutual]
QED

Theorem checked_eval_target_place_protected_cell_frame:
  checked_frame_context cx mods art src id env /\ IS_SOME (type_place_target env bt) ==>
  state_rel_frame (protected_cell_frame addr src id) (eval_target_place cx bt)
Proof
  simp[state_rel_frame_result] >> metis_tac[cj 8 checked_protected_cell_frame_mutual]
QED

Theorem checked_assign_tuple_targets_protected_cell_frame:
  checked_frame_context cx mods art src id env /\ writable_atarget env g ==>
  state_rel_frame (protected_cell_frame addr src id) (assign_tuple_targets cx g v)
Proof
  simp[state_rel_frame_result] >> metis_tac[cj 9 checked_protected_cell_frame_mutual]
QED

Theorem checked_assign_tuple_target_list_protected_cell_frame:
  checked_frame_context cx mods art src id env /\ EVERY (writable_atarget env) gs ==>
  state_rel_frame (protected_cell_frame addr src id) (assign_tuple_target_list cx gs vs)
Proof
  simp[state_rel_frame_result] >> metis_tac[cj 10 checked_protected_cell_frame_mutual]
QED

Theorem checked_eval_expr_results_protected_cell_frame:
  checked_frame_context cx mods art src id env /\ well_typed_exprs env es ==>
  state_rel_frame (protected_cell_frame addr src id) (eval_expr_results cx es)
Proof
  simp[state_rel_frame_result] >> metis_tac[cj 11 checked_protected_cell_frame_mutual]
QED

Theorem checked_eval_expr_const_cells_agree:
  eval_expr cx e st = (res,st') /\ const_cells_agree roots st /\
  well_typed_expr env e /\
  (!addr src id tv root. MEM (addr,src,id,tv,root) roots ==>
    checked_frame_context cx mods art src id env) ==>
  const_cells_agree roots st'
Proof
  strip_tac >> irule protected_cell_frame_cells_agree >> simp[] >>
  rpt strip_tac >> metis_tac[cj 5 checked_protected_cell_frame_mutual]
QED

Theorem checked_eval_expr_or_place_const_cells_agree:
  eval_expr cx e st = (res,st') /\ const_cells_agree roots st /\
  (well_typed_expr env e \/ ?vt. type_place_expr env e = SOME vt) /\
  (!addr src id tv root. MEM (addr,src,id,tv,root) roots ==>
    checked_frame_context cx mods art src id env) ==>
  const_cells_agree roots st'
Proof
  strip_tac >> irule protected_cell_frame_cells_agree >> simp[] >>
  rpt strip_tac >> metis_tac[cj 5 checked_protected_cell_frame_mutual_aux]
QED

Theorem checked_eval_stmts_const_cells_agree:
  eval_stmts cx ss st = (res,st') /\ const_cells_agree roots st /\
  IS_SOME (type_stmts env ret ss) /\
  (!addr src id tv root. MEM (addr,src,id,tv,root) roots ==>
    checked_frame_context cx mods art src id env) ==>
  const_cells_agree roots st'
Proof
  strip_tac >> irule protected_cell_frame_cells_agree >> simp[] >>
  rpt strip_tac >> metis_tac[cj 2 checked_protected_cell_frame_mutual]
QED

(* Selection validates immutable paths, so replay requires agreement on
   their typed root, not just equality of the raw place result. *)
Theorem constant_result_selection_replay:
  const_result_at roots cx ty pv v /\
  const_cells_agree roots st0 /\ const_cells_agree roots st /\
  select_result cx ty pv sb st0 = (res,st0) ==>
  select_result cx ty pv sb st = (res,st)
Proof
  strip_tac >>
  `?tv. evaluate_type (get_tenv cx) ty = SOME tv` by
    gvs[const_result_at_def] >>
  `!s. const_cells_agree roots s ==>
    select_result cx ty pv sb s =
      case evaluate_subscripts tv v [sb] of
      | INL w => (INL (const_select_output pv sb w),s)
      | INR err => (INR (Error err),s)` by
    (rpt strip_tac >> irule constant_result_selection_outcome >>
     rpt conj_tac
     >- metis_tac[const_result_at_observe]
     >- metis_tac[const_result_at_observe] >>
     qexists `ARB with type_defs := get_tenv cx` >> simp[] >>
     drule_all const_result_at_observe >>
     strip_tac >> first_x_assum irule >> simp[]) >>
  Cases_on `evaluate_subscripts tv v [sb]` >> gvs[]
QED

Theorem constant_result_length_replay:
  constant_result_shape pv /\
  read_result cx pv st0 = (INL v,st0) /\
  read_result cx pv st = (INL v,st) /\
  result_array_length cx pv st0 = (res,st0) ==>
  result_array_length cx pv st = (res,st)
Proof
  strip_tac >>
  `result_array_length cx pv st0 = result_array_length cx (Value v) st0` by
    metis_tac[constant_result_length_outcome] >>
  `result_array_length cx pv st = result_array_length cx (Value v) st` by
    metis_tac[constant_result_length_outcome] >>
  Cases_on `v` >>
  gvs[result_array_length_def, read_result_def, bind_def, return_def,
      raise_def, AllCaseEqs()] >>
  Cases_on `a` >> gvs[return_def]
QED

(* Every root in a replay footprint denotes a checked module constant. *)
Definition constant_roots_provenance_def:
  constant_roots_provenance mods addr roots <=>
    !a src id tv v. MEM (a,src,id,tv,v) roots ==>
      a = addr /\ declared_constant mods src id
End

Theorem constant_roots_provenance_append:
  constant_roots_provenance mods addr (xs ++ ys) <=>
  constant_roots_provenance mods addr xs /\
  constant_roots_provenance mods addr ys
Proof
  simp[constant_roots_provenance_def, MEM_APPEND] >> metis_tac[]
QED

Theorem constant_expr_replay_aux[local]:
  (!mods imms e v cx am sc artifact current_src.
    constant_value mods imms e = SOME v /\
    check_contract F cx.layouts cx.txn.target mods = SOME artifact /\
    ALOOKUP cx.sources cx.txn.target = SOME mods /\
    constant_machine_immutables am cx.txn.target = imms /\
    deployment_constant_cells_typed (type_env_all_modules mods)
      cx.txn.target mods am /\
    well_typed_expr (artifact_env artifact mods current_src) e /\
    constant_expr mods e /\ no_sha256_expr e ==>
    ?pv roots.
      const_cells_agree roots (initial_state am sc) /\
      constant_roots_provenance mods cx.txn.target roots /\
      const_result_at roots cx (expr_type e) pv v /\
      (!st. const_cells_agree roots st ==>
        eval_expr cx e st = (INL pv,st))) /\
  (!mods imms es vs cx am sc artifact current_src.
    constant_values mods imms es = SOME vs /\
    check_contract F cx.layouts cx.txn.target mods = SOME artifact /\
    ALOOKUP cx.sources cx.txn.target = SOME mods /\
    constant_machine_immutables am cx.txn.target = imms /\
    deployment_constant_cells_typed (type_env_all_modules mods)
      cx.txn.target mods am /\
    well_typed_exprs (artifact_env artifact mods current_src) es /\
    EVERY (constant_expr mods) es /\ EVERY no_sha256_expr es ==>
    ?roots.
      const_cells_agree roots (initial_state am sc) /\
      constant_roots_provenance mods cx.txn.target roots /\
      (!st. const_cells_agree roots st ==>
        eval_exprs cx es st = (INL vs,st)) /\
      LIST_REL (\e v. ?pv. const_result_at roots cx (expr_type e) pv v /\
        (!st. const_cells_agree roots st ==> eval_expr cx e st = (INL pv,st))) es vs)
Proof
  ho_match_mp_tac constant_value_ind >>
  rpt conj_tac >> rpt gen_tac >> rpt strip_tac >>
  rule_assum_tac (PURE_REWRITE_RULE [no_sha256_expr_def,
    no_sha256_collections, EVERY_DEF]) >> rpt strip_tac
  >~ [`TopLevelName`] >- suspend "name"
  >~ [`Literal`] >- suspend "literal"
  >~ [`StructLit`] >- suspend "struct"
  >~ [`Subscript`] >- suspend "subscript"
  >~ [`Attribute`] >- suspend "attribute"
  >~ [`Builtin`] >- suspend "builtin"
  >~ [`TypeBuiltin`] >- suspend "type_builtin"
  >~ [`constant_values _ _ []`] >- (
    qexists `[]` >> gvs[constant_value_def, const_cells_agree_def,
      constant_roots_provenance_def, Once evaluate_def, return_def])
  >~ [`constant_values _ _ (e::es)`] >- suspend "cons" >>
  gvs[constant_value_def]
QED

Resume constant_expr_replay_aux[literal]:
  drule_all constant_value_eval_expr_observation >>
  disch_then (qspec_then `sc` strip_assume_tac) >>
  `get_tenv cx = type_env_all_modules mods` by metis_tac[get_tenv_sources] >>
  gvs[constant_value_def] >>
  qexistsl [`Value (evaluate_literal l)`,`[]`] >>
  simp[const_cells_agree_def, constant_roots_provenance_def,
       const_result_at_def, Once evaluate_def, return_def] >>
  gvs[vyperTypeExprSoundnessTheory.value_runtime_typed_def, artifact_env_def, get_tenv_sources]
QED

Resume constant_expr_replay_aux[name]:
  gvs[constant_expr_def, declared_constant_def] >>
  `mods' = ty` by
    (drule_all vyperTypeConstantCellsTheory.checked_constant_declared_type >>
     simp[]) >>
  gvs[constant_value_def, AllCaseEqs()] >>
  PairCases_on `z` >> gvs[] >>
  `evaluate_type (type_env_all_modules mods) mods' = SOME z0 /\
   value_has_type z0 z1` by
    (gvs[vyperTypeConstantCellsTheory.deployment_constant_cells_typed_def,
         constant_machine_immutables_def] >>
     metis_tac[]) >>
  `?ais. ALOOKUP am.immutables cx.txn.target = SOME ais /\
    FLOOKUP (get_source_immutables src ais) id = SOME (z0,z1)` by
    (Cases_on `ALOOKUP am.immutables cx.txn.target` >>
     gvs[constant_machine_immutables_def, get_source_immutables_def]) >>
  `get_tenv cx = type_env_all_modules mods` by metis_tac[get_tenv_sources] >>
  qexistsl [`PlaceR (ImmutablePlace src id [])`,
    `[(cx.txn.target,src,id,z0,z1)]`] >>
  simp[const_cells_agree_def, initial_state_def,
       constant_roots_provenance_def, declared_constant_def,
       const_result_at_def, expr_type_def, subscripts_type_def,
       evaluate_subscripts_def, get_tenv_sources] >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  simp[Once evaluate_def, lookup_global_def, get_module_code_def,
       get_immutables_def, get_address_immutables_def,
       bind_def, return_def, lift_option_type_def] >>
  metis_tac[]
QED
Resume constant_expr_replay_aux[struct]:
  drule_all constant_value_eval_expr_observation >>
  disch_then (qspec_then `sc` strip_assume_tac) >>
  `well_typed_exprs (artifact_env artifact mods current_src) (MAP SND kes)` by
    (irule vyperTypeEvalSoundnessTheory.well_typed_named_exprs_MAP_SND_stmt >>
     gvs[well_typed_expr_def]) >>
  gvs[constant_value_def, constant_expr_def, AllCaseEqs()] >>
  `EVERY (constant_expr mods) (MAP SND kes)` by fs[EVERY_MEM] >>
  `EVERY no_sha256_expr (MAP SND kes)` by
    gvs[EVERY_MAP, combinTheory.o_DEF] >>
  first_x_assum (qspecl_then [`cx`,`am`,`sc`,`artifact`,`current_src`] mp_tac) >>
  simp[EVERY_MAP, combinTheory.o_DEF] >> strip_tac >>
  qexistsl [`Value (StructV (ZIP (MAP FST kes,vs)))`,`roots`] >>
  simp[const_result_at_def, expr_type_def] >>
  conj_tac
  >- (`get_tenv cx = type_env_all_modules mods` by metis_tac[get_tenv_sources] >>
      gvs[vyperTypeExprSoundnessTheory.value_runtime_typed_def, artifact_env_def,
          expr_type_def]) >>
  PairCases_on `v5` >>
  simp[Once evaluate_def, bind_def, return_def]
QED
Resume constant_expr_replay_aux[subscript]:
  `well_typed_expr (artifact_env artifact mods current_src) e` by
    (fs[constant_expr_def] >>
     drule_all constant_subscript_base_well_typed >> simp[]) >>
  `subscript_type_ok (expr_type e) e' v6` by
    metis_tac[constant_subscript_type_ok] >>
  gvs[constant_value_def, constant_expr_def, AllCaseEqs()] >>
  `well_typed_expr (artifact_env artifact mods current_src) e'` by
    gvs[Once well_typed_expr_def] >>
  first_x_assum (qspecl_then [`cx`,`am`,`sc`,`artifact`,`current_src`] mp_tac) >>
  simp[] >> strip_tac >>
  first_x_assum (qspecl_then [`cx`,`am`,`sc`,`artifact`,`current_src`] mp_tac) >>
  simp[] >> strip_tac >>
  `get_tenv cx = type_env_all_modules mods` by metis_tac[get_tenv_sources] >>
  `value_has_type arr_tv v1` by gvs[const_result_at_def] >>
  `vyperTypeExprResult$subscript_index_matches (expr_type e) e' v2` by
    metis_tac[constant_subscript_index_matches] >>
  `evaluate_type (artifact_env artifact mods current_src).type_defs
     (expr_type e) = SOME arr_tv` by simp[artifact_env_def] >>
  drule_all constant_subscript_selected_typed >> strip_tac >>
  `const_result_at (roots' ++ roots) cx v6
    (const_select_output pv' (ValueSubscript v2) v) v` by
    (irule const_result_at_select >>
     qexistsl [`etv`,`arr_tv`,`expr_type e`,`v1`] >>
     conj_tac >- gvs[artifact_env_def] >>
     simp[] >> irule const_result_at_mono >> qexists `roots'` >> simp[MEM_APPEND]) >>
  qexistsl [`const_select_output pv' (ValueSubscript v2) v`,`roots' ++ roots`] >>
  simp[const_cells_agree_append, constant_roots_provenance_append, expr_type_def] >>
  rpt strip_tac >>
  `read_result cx pv st = (INL v2,st)` by metis_tac[const_result_at_observe] >>
  `select_result cx (expr_type e) pv' (ValueSubscript v2) st =
    (INL (const_select_output pv' (ValueSubscript v2) v),st)` by
    (`select_result cx (expr_type e) pv' (ValueSubscript v2) st =
       case evaluate_subscripts arr_tv v1 [ValueSubscript v2] of
       | INL w => (INL (const_select_output pv' (ValueSubscript v2) w),st)
       | INR err => (INR (Error err),st)` suffices_by simp[] >>
     irule constant_result_selection_outcome >>
     conj_tac >- metis_tac[const_result_at_observe] >>
     conj_tac >- metis_tac[const_result_at_observe] >>
     qexists `artifact_env artifact mods current_src` >>
     simp[artifact_env_def] >>
     drule_all const_result_at_observe >> strip_tac >>
     first_x_assum irule >> simp[artifact_env_def]) >>
  simp[Once evaluate_def, bind_def]
QED
Resume constant_expr_replay_aux[attribute]:
  gvs[constant_value_def, constant_expr_def, AllCaseEqs()] >>
  `well_typed_expr (artifact_env artifact mods current_src) e` by
    gvs[Once well_typed_expr_def] >>
  first_x_assum (qspecl_then [`cx`,`am`,`sc`,`artifact`,`current_src`] mp_tac) >>
  simp[] >> strip_tac >>
  `get_tenv cx = type_env_all_modules mods` by metis_tac[get_tenv_sources] >>
  gvs[Once well_typed_expr_def] >>
  `attribute_type (artifact_env artifact mods current_src).type_defs
     (expr_type e) id = SOME v7` by gvs[attribute_type_ok_def] >>
  `?tv. evaluate_type (artifact_env artifact mods current_src).type_defs
      (expr_type e) = SOME tv /\ value_has_type tv v'` by
    gvs[const_result_at_def, artifact_env_def] >>
  `evaluate_subscripts tv v' [AttrSubscript id] = INL v` by
    (Cases_on `v'` >> gvs[vyperValueOperationTheory.evaluate_attribute_def,
                          evaluate_subscripts_def, AllCaseEqs()]) >>
  drule_all constant_attribute_selected_typed >> strip_tac >>
  `const_result_at roots cx v7 (const_select_output pv (AttrSubscript id) v) v` by
    (irule const_result_at_select >>
     qexistsl [`etv`,`tv`,`expr_type e`,`v'`] >> gvs[artifact_env_def]) >>
  qexistsl [`const_select_output pv (AttrSubscript id) v`,`roots`] >>
  simp[expr_type_def] >> rpt strip_tac >>
  `select_result cx (expr_type e) pv (AttrSubscript id) st =
    (INL (const_select_output pv (AttrSubscript id) v),st)` by
    (`select_result cx (expr_type e) pv (AttrSubscript id) st =
       case evaluate_subscripts tv v' [AttrSubscript id] of
       | INL w => (INL (const_select_output pv (AttrSubscript id) w),st)
       | INR err => (INR (Error err),st)` suffices_by simp[] >>
     irule constant_result_selection_outcome >>
     conj_tac >- metis_tac[const_result_at_observe] >>
     conj_tac >- metis_tac[const_result_at_observe] >>
     qexists `artifact_env artifact mods current_src` >> simp[artifact_env_def] >>
     qpat_x_assum `const_result_at roots cx v7 _ _` kall_tac >>
     drule_all const_result_at_observe >> strip_tac >>
     first_x_assum irule >> simp[artifact_env_def]) >>
  simp[Once evaluate_def, bind_def]
QED
Resume constant_expr_replay_aux[builtin]:
  drule_all constant_value_eval_expr_observation >>
  disch_then (qspec_then `sc` strip_assume_tac) >>
  `well_typed_exprs (artifact_env artifact mods current_src) es` by
    gvs[Once well_typed_expr_def] >>
  gvs[constant_value_def, constant_expr_def, AllCaseEqs()] >>
  `EVERY (constant_expr mods) es` by fs[EVERY_MEM] >>
  first_x_assum (qspecl_then [`cx`,`am`,`sc`,`artifact`,`current_src`] mp_tac) >>
  simp[] >> strip_tac >>
  `get_tenv cx = type_env_all_modules mods` by metis_tac[get_tenv_sources]
  >- (gvs[] >> qexistsl [`Value (IntV (&n))`,`roots`] >>
      simp[const_result_at_def, expr_type_def] >> conj_tac
      >- gvs[vyperTypeExprSoundnessTheory.value_runtime_typed_def, artifact_env_def, expr_type_def] >>
      rpt strip_tac >>
      `result_array_length cx pv' st = (INL n,st)` by
        metis_tac[constant_result_length, const_result_at_observe] >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, return_def,
           type_check_def, assert_def]) >>
  qexistsl [`Value v`,`roots`] >> simp[const_result_at_def, expr_type_def] >>
  conj_tac
  >- gvs[vyperTypeExprSoundnessTheory.value_runtime_typed_def, artifact_env_def, expr_type_def] >>
  `!acc. evaluate_builtin cx acc ty bt (MAP expr_type es) vs = INL v` by
    metis_tac[evaluate_builtin_constant_context] >>
  `bt <> Env MsgGas` by
    (strip_tac >> gvs[evaluate_builtin_def, AllCaseEqs()]) >>
  `~precompile_builtin bt` by
    (Cases_on `bt` >> gvs[constant_builtin_def]) >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def, assert_def,
       lift_sum_def, get_accounts_def, return_def,
       precompile_call_success_def]
QED
Resume constant_expr_replay_aux[type_builtin]:
  drule_all constant_value_eval_expr_observation >>
  disch_then (qspec_then `sc` strip_assume_tac) >>
  `well_typed_exprs (artifact_env artifact mods current_src) es` by
    gvs[Once well_typed_expr_def] >>
  gvs[constant_value_def, constant_expr_def, AllCaseEqs()] >>
  `EVERY (constant_expr mods) es` by fs[EVERY_MEM] >>
  first_x_assum (qspecl_then [`cx`,`am`,`sc`,`artifact`,`current_src`] mp_tac) >>
  simp[] >> strip_tac >>
  `get_tenv cx = type_env_all_modules mods` by metis_tac[get_tenv_sources] >>
  qexistsl [`Value v`,`roots`] >> simp[const_result_at_def, expr_type_def] >>
  conj_tac
  >- gvs[vyperTypeExprSoundnessTheory.value_runtime_typed_def, artifact_env_def, expr_type_def] >>
  `evaluate_type_builtin cx tb typ (MAP expr_type es) vs = INL v` by
    metis_tac[evaluate_type_builtin_constant_context] >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def, assert_def,
       lift_sum_def, return_def]
QED
Resume constant_expr_replay_aux[cons]:
  gvs[constant_value_def, well_typed_expr_def, AllCaseEqs()] >>
  first_x_assum (qspecl_then [`cx`,`am`,`sc`,`artifact`,`current_src`] mp_tac) >>
  simp[] >> strip_tac >>
  first_x_assum (qspecl_then [`cx`,`am`,`sc`,`artifact`,`current_src`] mp_tac) >>
  simp[] >> strip_tac >>
  qexists `roots ++ roots'` >>
  simp[const_cells_agree_append, constant_roots_provenance_append] >>
  conj_tac
  >- (rpt strip_tac >>
      `read_result cx pv st = (INL v,st)` by metis_tac[const_result_at_observe] >>
      simp[Once evaluate_def, bind_def, return_def]) >>
  conj_tac
  >- (qexists `pv` >> simp[] >> irule const_result_at_mono >>
      qexists `roots` >> simp[MEM_APPEND]) >>
  qpat_x_assum `LIST_REL _ es vs'` mp_tac >>
  simp[LIST_REL_EL_EQN] >> rpt strip_tac >>
  first_x_assum (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
  qexists `pv'` >> simp[] >> irule const_result_at_mono >>
  qexists `roots'` >> simp[MEM_APPEND]
QED
Finalise constant_expr_replay_aux

Theorem constant_expr_replay_footprint:
  constant_value mods imms e = SOME v /\
  check_contract F cx.layouts cx.txn.target mods = SOME artifact /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  constant_machine_immutables am cx.txn.target = imms /\
  deployment_constant_cells_typed (type_env_all_modules mods)
    cx.txn.target mods am /\
  well_typed_expr (artifact_env artifact mods current_src) e /\
  constant_expr mods e /\ no_sha256_expr e ==>
  ?pv roots.
    const_cells_agree roots (initial_state am sc) /\
    constant_roots_provenance mods cx.txn.target roots /\
    const_result_at roots cx (expr_type e) pv v /\
    eval_expr cx e (initial_state am sc) = (INL pv,initial_state am sc) /\
    eval_result_typed (artifact_env artifact mods current_src,cx,initial_state am sc)
      pv (Type (expr_type e)) /\
    read_result cx pv (initial_state am sc) = (INL v,initial_state am sc) /\
    value_runtime_typed (artifact_env artifact mods current_src) (expr_type e) v /\
    constant_result_shape pv /\
    (!st. const_cells_agree roots st ==>
      eval_expr cx e st = (INL pv,st) /\ read_result cx pv st = (INL v,st))
Proof
  strip_tac >> drule_all (cj 1 constant_expr_replay_aux) >>
  disch_then (qspec_then `sc` strip_assume_tac) >>
  qexistsl [`pv`,`roots`] >> simp[] >>
  drule_all const_result_at_observe >> strip_tac >> simp[] >>
  conj_tac
  >- (first_x_assum irule >> drule get_tenv_sources >> simp[artifact_env_def]) >>
  conj_tac
  >- (gvs[const_result_at_def, vyperTypeExprSoundnessTheory.value_runtime_typed_def,
          artifact_env_def] >> metis_tac[get_tenv_sources]) >>
  metis_tac[const_result_at_observe]
QED

(* Static typing of the declaration-order replacement environment. *)
Theorem const_subst_literal_forms[local]:
  (int_literal_value e = SOME n ==>
    int_literal_value (subst_consts_expr E e) = SOME n) /\
  (nonneg_int_literal e ==> nonneg_int_literal (subst_consts_expr E e))
Proof
  Cases_on `e` >> simp[int_literal_value_def, nonneg_int_literal_def,
    subst_consts_expr_def] >> Cases_on `l` >> simp[subst_consts_expr_def]
QED

Theorem const_subst_subscript_form[local]:
  expr_type (subst_consts_expr E ix) = expr_type ix /\
  subscript_type_ok ty ix rt ==>
  subscript_type_ok ty (subst_consts_expr E ix) rt
Proof
  Cases_on `ty` >> simp[subscript_type_ok_def] >>
  Cases_on `ix` >> simp[subscript_type_ok_def, subst_consts_expr_def] >>
  Cases_on `l` >> simp[subst_consts_expr_def]
QED

Theorem const_subst_builtin_operands[local]:
  MAP expr_type (subst_consts_exprs E es) = MAP expr_type es /\
  well_typed_builtin_app ty bt (MAP expr_type es) /\
  builtin_operands_ok bt es ==>
  builtin_operands_ok bt (subst_consts_exprs E es)
Proof
  strip_tac >>
  Cases_on `bt = Bop Exp \/ bt = Bop ShL \/ bt = Bop ShR`
  >- (gvs[well_typed_builtin_app_def] >>
      Cases_on `es` >> gvs[] >> Cases_on `t` >> gvs[] >>
      gvs[builtin_operands_ok_def, subst_consts_expr_def, shift_amount_ok_def] >>
      metis_tac[const_subst_literal_forms, optionTheory.IS_SOME_EXISTS]) >>
  gvs[builtin_operands_ok_def]
QED

Theorem const_place_expr_annotation:
  !env e vt. type_place_expr env e = SOME vt ==>
    vtype_annotation_ok vt (expr_type e)
Proof
  metis_tac[type_place_expr_vtype_annotation]
QED

Theorem const_subscript_domain_type_ok:
  (well_typed_expr env (Subscript ty a b) \/
   IS_SOME (type_place_expr env (Subscript ty a b))) /\
  (~?kt vt. type_place_expr env a = SOME (HashMapT kt vt)) ==>
  subscript_type_ok (expr_type a) b ty
Proof
  disch_then (CONJUNCTS_THEN2 mp_tac assume_tac) >>
  simp[Once well_typed_expr_def, optionTheory.IS_SOME_EXISTS] >>
  simp[Once well_typed_expr_def] >> strip_tac >> gvs[AllCaseEqs()] >>
  drule const_place_expr_annotation >> strip_tac >>
  rename1 `vtype_annotation_ok base_vt (expr_type a)` >>
  Cases_on `base_vt` >> gvs[vtype_annotation_ok_def, subscript_vtype_def] >>
  Cases_on `expr_type a` >>
  gvs[subscript_vtype_def, subscript_type_ok_def, vtype_annotation_ok_def] >>
  metis_tac[]
QED

Theorem const_subscript_hashmap_base:
  type_place_expr env (Subscript ty a b) = SOME (HashMapT kt vt) ==>
  ?kt0 vt0. type_place_expr env a = SOME (HashMapT kt0 vt0)
Proof
  simp[Once well_typed_expr_def, AllCaseEqs()] >> rpt strip_tac >>
  rename1 `subscript_vtype base_vt _ = SOME _` >>
  Cases_on `base_vt` >> gvs[subscript_vtype_def] >>
  Cases_on `t` >> gvs[subscript_vtype_def] >> metis_tac[]
QED

Theorem const_subscript_type_ok[local]:
  well_typed_expr env (Subscript ty e1 e2) /\
  well_typed_expr env e1 ==>
  subscript_type_ok (expr_type e1) e2 ty
Proof
  strip_tac >> irule const_subscript_domain_type_ok >>
  metis_tac[vyperTypeExprResultTheory.well_typed_expr_not_hashmap_place]
QED

Theorem fold_const_literal_forms[local]:
  (int_literal_value e = SOME n ==>
    int_literal_value (fold_const_expr e) = SOME n) /\
  (nonneg_int_literal e ==> nonneg_int_literal (fold_const_expr e))
Proof
  Cases_on `e` >> simp[int_literal_value_def, nonneg_int_literal_def,
    fold_const_expr_def] >> Cases_on `l` >> simp[fold_const_expr_def]
QED

Theorem fold_const_subscript_form[local]:
  subscript_type_ok ty ix rt ==>
  subscript_type_ok ty (fold_const_expr ix) rt
Proof
  Cases_on `ty` >> simp[subscript_type_ok_def] >>
  Cases_on `ix` >> simp[subscript_type_ok_def, fold_const_expr_def] >>
  Cases_on `l` >> simp[fold_const_expr_def]
QED

Theorem fold_const_builtin_operands[local]:
  well_typed_builtin_app ty bt (MAP expr_type es) /\
  builtin_operands_ok bt es ==>
  builtin_operands_ok bt (fold_const_exprs es)
Proof
  strip_tac >>
  Cases_on `bt = Bop Exp \/ bt = Bop ShL \/ bt = Bop ShR`
  >- (gvs[well_typed_builtin_app_def] >>
      Cases_on `es` >> gvs[] >> Cases_on `t` >> gvs[] >>
      gvs[builtin_operands_ok_def, fold_const_expr_def, shift_amount_ok_def] >>
      metis_tac[fold_const_literal_forms, optionTheory.IS_SOME_EXISTS]) >>
  gvs[builtin_operands_ok_def]
QED

Theorem fold_const_builtin_typed[local]:
  well_typed_expr env (Builtin ty bt es) ==>
  well_typed_expr env (fold_const_builtin ty bt es)
Proof
  strip_tac >> Cases_on `bt` >> gvs[fold_const_builtin_def] >>
  Cases_on `es` >> gvs[] >> Cases_on `t` >> gvs[] >>
  Cases_on `h` >> gvs[] >> rename1 `Literal aty l` >> Cases_on `l` >>
  gvs[well_typed_expr_def, well_typed_builtin_app_def, well_typed_literal_def,
      byteTheory.LENGTH_word_to_bytes, compatible_bound_def,
      fcpTheory.index_bit0, fcpTheory.index_one,
      fcpTheory.finite_bit0, fcpTheory.finite_one]
QED

Theorem fold_const_collection_metadata[simp]:
  MAP expr_type (fold_const_exprs es) = MAP expr_type es /\
  LENGTH (fold_const_exprs es) = LENGTH es /\
  MAP FST (fold_const_fields fs) = MAP FST fs /\
  MAP (expr_type o SND) (fold_const_fields fs) = MAP (expr_type o SND) fs
Proof
  rpt conj_tac
  >- (Induct_on `es` >> simp[fold_const_expr_def])
  >- (Induct_on `es` >> simp[fold_const_expr_def])
  >- (Induct_on `fs` >> simp[fold_const_expr_def] >>
      gen_tac >> PairCases_on `h` >> simp[fold_const_expr_def]) >>
  Induct_on `fs` >> simp[fold_const_expr_def] >>
  gen_tac >> PairCases_on `h` >> simp[fold_const_expr_def]
QED

Theorem fold_const_typing_aux[local]:
  (!e. (!env. well_typed_expr env e ==> well_typed_expr env (fold_const_expr e)) /\
       (!env vt. type_place_expr env e = SOME vt ==>
          type_place_expr env (fold_const_expr e) = SOME vt)) /\
  (!t env vt. type_place_target env t = SOME vt ==>
     type_place_target env (fold_const_btarget t) = SOME vt) /\
  (!es env. well_typed_exprs env es ==>
     well_typed_exprs env (fold_const_exprs es)) /\
  (!d env. well_typed_opt env d ==> well_typed_opt env (fold_const_opt d)) /\
  (!fs env. well_typed_named_exprs env fs ==>
     well_typed_named_exprs env (fold_const_fields fs))
Proof
  ho_match_mp_tac fold_const_expr_ind >> rpt conj_tac >> rpt gen_tac
  >~ [`fold_const_expr (Subscript ty a b)`] >- suspend "subscript"
  >~ [`fold_const_expr (Builtin ty bi es)`] >- suspend "builtin"
  >~ [`fold_const_expr (Pop ty t)`] >- suspend "pop"
  >~ [`fold_const_expr (Call ty ct es d)`] >- suspend "call" >>
  simp[fold_const_expr_def, well_typed_expr_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[fold_const_collection_metadata] >>
  metis_tac[fold_const_expr_type]
QED

Resume fold_const_typing_aux[subscript]:
  rpt strip_tac >>
  gvs[fold_const_expr_def, well_typed_expr_def, AllCaseEqs()] >>
  metis_tac[fold_const_subscript_form, fold_const_expr_type]
QED
Resume fold_const_typing_aux[builtin]:
  strip_tac >> conj_tac
  >- (rpt strip_tac >> simp[fold_const_expr_def] >>
      irule fold_const_builtin_typed >>
      gvs[Once well_typed_expr_def] >>
      simp[Once well_typed_expr_def] >>
      metis_tac[fold_const_builtin_operands, fold_const_collection_metadata]) >>
  simp[well_typed_expr_def]
QED
Resume fold_const_typing_aux[pop]:
  rpt strip_tac >> gvs[fold_const_expr_def, well_typed_expr_def] >>
  rename1 `type_place_target env tgt = SOME _` >>
  Cases_on `tgt` >> gvs[fold_const_expr_def] >> metis_tac[]
QED
Resume fold_const_typing_aux[call]:
  strip_tac >> Cases_on `ct`
  >~ [`Call ty (IntCall p) es d`] >-
    (PairCases_on `p` >>
     simp[well_typed_expr_def, fold_const_expr_def] >> rpt strip_tac >>
     gvs[well_typed_expr_def, fold_const_collection_metadata])
  >~ [`Call ty (ExtCall b b0 p l) es d`] >-
    (PairCases_on `p` >>
     simp[well_typed_expr_def, fold_const_expr_def] >> rpt strip_tac >>
     gvs[well_typed_expr_def, fold_const_collection_metadata,
         MAP_DROP, MAP_TAKE, GSYM MAP_TL] >>
     Cases_on `es` >> gvs[fold_const_expr_def, fold_const_collection_metadata])
  >~ [`Call ty RawLog es d`] >- suspend "rawlog" >>
  simp[well_typed_expr_def, fold_const_expr_def] >>
  rpt strip_tac >>
  gvs[well_typed_expr_def, fold_const_collection_metadata,
      raw_call_kws_ok_def, MAP_DROP]
QED
Resume fold_const_typing_aux[rawlog]:
  simp[fold_const_expr_def, well_typed_expr_def] >> rpt strip_tac >>
  Cases_on `es` >> gvs[well_typed_expr_def, fold_const_expr_def] >>
  Cases_on `h` >>
  gvs[well_typed_expr_def, fold_const_expr_def, AllCaseEqs()] >>
  Cases_on `b` >>
  gvs[fold_const_builtin_def, fold_const_collection_metadata] >>
  `LENGTH (fold_const_exprs l) = LENGTH l` by
    simp[fold_const_collection_metadata] >>
  Cases_on `fold_const_exprs l` >> gvs[]
QED
Finalise fold_const_typing_aux

Theorem fold_const_expr_typed:
  well_typed_expr env e ==> well_typed_expr env (fold_const_expr e)
Proof
  metis_tac[fold_const_typing_aux]
QED

Theorem const_fragment_subst_typed:
  (!e ty ix. constant_expr mods e /\
    well_typed_expr env (Subscript ty e ix) ==> well_typed_expr env e) ==>
  (!e. constant_expr mods e /\ well_typed_expr env e /\
    (!ty id r. MEM (ty,id) (const_local_refs e) /\ ALOOKUP E id = SOME r ==>
      expr_type r = ty /\ well_typed_expr env r) ==>
    well_typed_expr env (subst_consts_expr E e) /\
    expr_type (subst_consts_expr E e) = expr_type e) /\
  (!es. EVERY (constant_expr mods) es /\ well_typed_exprs env es /\
    (!ty id r. MEM (ty,id) (const_local_exprs es) /\ ALOOKUP E id = SOME r ==>
      expr_type r = ty /\ well_typed_expr env r) ==>
    well_typed_exprs env (subst_consts_exprs E es) /\
    MAP expr_type (subst_consts_exprs E es) = MAP expr_type es) /\
  (!fs. EVERY (constant_expr mods) (MAP SND fs) /\ well_typed_named_exprs env fs /\
    (!ty id r. MEM (ty,id) (const_local_fields fs) /\ ALOOKUP E id = SOME r ==>
      expr_type r = ty /\ well_typed_expr env r) ==>
    well_typed_named_exprs env (subst_consts_fields E fs) /\
    MAP FST (subst_consts_fields E fs) = MAP FST fs /\
    MAP (expr_type o SND) (subst_consts_fields E fs) = MAP (expr_type o SND) fs)
Proof
  disch_then (mk_asm "subscript_base") >> ho_match_mp_tac const_local_refs_ind >>
  simp[constant_expr_def, const_local_refs_def, subst_consts_expr_def,
       expr_type_def] >> rpt strip_tac
  >>~- ([`subst_consts_expr E (TopLevelName ty ns)`],
    PairCases_on `ns` >> Cases_on `ns0` >>
    gvs[subst_consts_expr_def, expr_type_def] >>
    Cases_on `ALOOKUP E ns1` >> gvs[expr_type_def])
  >>~- ([`well_typed_expr env (Subscript ty (subst_consts_expr E a) (subst_consts_expr E b))`],
    `well_typed_expr env a` by (asm "subscript_base" (fn th => metis_tac[th])) >>
    `subscript_type_ok (expr_type a) b ty` by metis_tac[const_subscript_type_ok] >>
    `well_typed_expr env b` by gvs[Once well_typed_expr_def] >>
    `well_typed_expr env (subst_consts_expr E a) /\
     expr_type (subst_consts_expr E a) = expr_type a` by metis_tac[] >>
    `well_typed_expr env (subst_consts_expr E b) /\
     expr_type (subst_consts_expr E b) = expr_type b` by metis_tac[] >>
    `well_formed_type env.type_defs ty` by
      (qpat_x_assum `well_typed_expr _ (Subscript _ _ _)` mp_tac >>
       simp[Once well_typed_expr_def]) >>
    simp[Once well_typed_expr_def] >>
    metis_tac[const_subst_subscript_form]) >>
  gvs[SF ETA_ss, Once well_typed_expr_def] >>
  rpt (qpat_x_assum `(_ ==> _ /\ _)` mp_tac >>
       (impl_tac >- metis_tac[]) >> strip_tac) >>
  simp[Once well_typed_expr_def] >>
  metis_tac[const_subst_builtin_operands]
QED

Theorem checked_const_fragment_subst_typed[local]:
  check_contract mode layouts addr mods = SOME artifact /\
  constant_expr mods e /\ well_typed_expr (artifact_env artifact mods NONE) e /\
  (!ty id r. MEM (ty,id) (const_local_refs e) /\ ALOOKUP E id = SOME r ==>
    expr_type r = ty /\ well_typed_expr (artifact_env artifact mods NONE) r) ==>
  well_typed_expr (artifact_env artifact mods NONE) (subst_consts_expr E e) /\
  expr_type (subst_consts_expr E e) = expr_type e
Proof
  strip_tac >>
  `!a ty ix. constant_expr mods a /\
    well_typed_expr (artifact_env artifact mods NONE) (Subscript ty a ix) ==>
    well_typed_expr (artifact_env artifact mods NONE) a` by
    (rpt strip_tac >>
     `ALOOKUP (constant_context mods).sources (constant_context mods).txn.target = SOME mods`
       by simp[constant_context_def] >>
     drule_all constant_subscript_base_well_typed >> simp[]) >>
  drule const_fragment_subst_typed >> disch_then (irule o cj 1) >>
  simp[] >> metis_tac[]
QED

Theorem checked_const_prefix_subst_typed[local]:
  check_contract mode layouts addr mods = SOME artifact /\
  ALOOKUP mods NONE = SOME tops /\
  tops = pre ++ VariableDecl vis (Constant e) id ty slot :: rest /\
  const_prefix_syntax E pre /\
  (!n r. ALOOKUP E n = SOME r ==> well_typed_expr (artifact_env artifact mods NONE) r) ==>
  well_typed_expr (artifact_env artifact mods NONE) (subst_consts_expr E e) /\
  expr_type (subst_consts_expr E e) = ty
Proof
  strip_tac >> drule_all checked_const_initializer_prefix >> strip_tac >>
  `!ann n r. MEM (ann,n) (const_local_refs e) /\ ALOOKUP E n = SOME r ==>
    expr_type r = ann /\ well_typed_expr (artifact_env artifact mods NONE) r` by
    (rpt strip_tac >> gvs[const_prefix_syntax_def] >>
     `?v init rt sl. MEM (VariableDecl v (Constant init) n rt sl) pre /\ expr_type r = rt`
       by metis_tac[] >>
     `ann = rt` by (irule checked_constant_reference_annotation >>
       metis_tac[MEM_APPEND, MEM]) >> metis_tac[]) >>
  metis_tac[checked_const_fragment_subst_typed]
QED

Theorem checked_module_consts_env_typed_acc[local]:
  !ts pre E.
  check_contract mode layouts addr mods = SOME artifact /\
  ALOOKUP mods NONE = SOME tops /\ tops = pre ++ ts /\
  const_prefix_syntax E pre /\
  (!n r. ALOOKUP E n = SOME r ==> well_typed_expr (artifact_env artifact mods NONE) r) ==>
  const_prefix_syntax (module_consts_env ts E) tops /\
  (!n r. ALOOKUP (module_consts_env ts E) n = SOME r ==>
    well_typed_expr (artifact_env artifact mods NONE) r)
Proof
  Induct >- (simp[module_consts_env_def] >> metis_tac[]) >>
  rpt gen_tac >>
  qabbrev_tac `pre' = pre ++ [h]` >>
  Cases_on `h` >> simp[module_consts_env_def] >> strip_tac
  >~ [`module_consts_env (VariableDecl vis mut id ty slot :: ts) E`]
  >- (Cases_on `mut` >> gvs[module_consts_env_def]
      >~ [`module_consts_env ts (E ++ [(id,fold_const_expr (subst_consts_expr E e))])`]
      >- (`well_typed_expr (artifact_env artifact mods NONE) (subst_consts_expr E e) /\
           expr_type (subst_consts_expr E e) = ty` by
            (`pre' ++ ts = pre ++ VariableDecl vis (Constant e) id ty slot :: ts` by
               simp[Abbr `pre'`, GSYM APPEND_ASSOC] >>
             drule_all checked_const_prefix_subst_typed >> simp[]) >>
          first_x_assum irule >> reverse conj_tac
          >- (simp[Abbr `pre'`] >> irule const_prefix_syntax_snoc >> simp[]) >>
          rpt strip_tac >> gvs[ALOOKUP_APPEND, AllCaseEqs()] >>
          metis_tac[fold_const_expr_typed]) >>
      first_x_assum irule >>
      conj_tac >- metis_tac[] >>
      simp[Abbr `pre'`] >>
      gvs[const_prefix_syntax_def, const_decl_names_append, const_decl_names_def] >>
      metis_tac[MEM_APPEND]) >>
  gvs[] >> first_x_assum irule >> conj_tac >- metis_tac[] >>
  simp[Abbr `pre'`] >>
  gvs[const_prefix_syntax_def, const_decl_names_append, const_decl_names_def] >>
  metis_tac[MEM_APPEND]
QED

Theorem checked_module_consts_env_replacement_typed:
  check_contract mode layouts addr mods = SOME artifact /\
  ALOOKUP mods NONE = SOME tops /\
  ALOOKUP (module_consts_env tops []) id = SOME r ==>
  well_typed_expr (artifact_env artifact mods NONE) r
Proof
  strip_tac >>
  `const_prefix_syntax (module_consts_env tops []) tops /\
   (!n r. ALOOKUP (module_consts_env tops []) n = SOME r ==>
     well_typed_expr (artifact_env artifact mods NONE) r)` by
    (irule checked_module_consts_env_typed_acc >>
     simp[const_prefix_syntax_def, const_decl_names_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem checked_module_consts_env_replacement_annotation:
  check_contract mode layouts addr mods = SOME artifact /\
  ALOOKUP mods NONE = SOME tops /\
  ALOOKUP (module_consts_env tops []) id = SOME r ==>
  ?vis init ty slot. MEM (VariableDecl vis (Constant init) id ty slot) tops /\
    expr_type r = ty
Proof
  strip_tac >>
  `const_prefix_syntax (module_consts_env tops []) tops /\
   (!n r. ALOOKUP (module_consts_env tops []) n = SOME r ==>
     well_typed_expr (artifact_env artifact mods NONE) r)` by
    (irule checked_module_consts_env_typed_acc >>
     simp[const_prefix_syntax_def, const_decl_names_def] >> metis_tac[]) >>
  gvs[const_prefix_syntax_def] >> metis_tac[]
QED

Theorem checked_module_consts_env_replacement_replay:
  check_contract F cx.layouts cx.txn.target mods = SOME artifact /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  ALOOKUP mods NONE = SOME tops /\
  constants_fold_module mods imms NONE tops FEMPTY = SOME A /\
  ALOOKUP (module_consts_env tops []) id = SOME r /\
  no_sha256_expr r /\
  (!src. IS_SOME src ==>
    get_source_immutables src (constant_machine_immutables am cx.txn.target) =
    get_source_immutables src imms) /\
  (!tv v. FLOOKUP A id = SOME (tv,v) ==>
    FLOOKUP (get_source_immutables NONE
      (constant_machine_immutables am cx.txn.target)) id = SOME (tv,v)) /\
  deployment_constant_cells_typed (type_env_all_modules mods) cx.txn.target mods am ==>
  ?pv roots.
    const_cells_agree roots (initial_state am sc) /\
    constant_roots_provenance mods cx.txn.target roots /\
    const_results_related roots cx (expr_type r)
      (PlaceR (ImmutablePlace NONE id [])) pv /\
    (!st. const_cells_agree roots st ==> eval_expr cx r st = (INL pv,st))
Proof
  strip_tac >>
  drule_all checked_module_consts_env_replacement >> strip_tac >>
  `constant_value mods (constant_machine_immutables am cx.txn.target) r = SOME v` by
    (qsuff_tac `constant_value mods (merge_constant_imms NONE A imms) r =
       constant_value mods (constant_machine_immutables am cx.txn.target) r`
     >- simp[] >> irule constant_value_closed_stable >>
     simp[merge_constant_imms_imports]) >>
  `well_typed_expr (artifact_env artifact mods NONE) r` by
    metis_tac[checked_module_consts_env_replacement_typed] >>
  drule_at (Pat `deployment_constant_cells_typed _ _ _ _`) constant_expr_replay_footprint >>
  simp[] >> disch_then (qspecl_then [`v`,`sc`,`r`,`NONE`] mp_tac) >>
  simp[] >> strip_tac >>
  `get_tenv cx = type_env_all_modules mods` by metis_tac[get_tenv_sources] >>
  `FLOOKUP (get_source_immutables NONE
    (constant_machine_immutables am cx.txn.target)) id = SOME (tv,v)` by metis_tac[] >>
  `const_cells_agree [(cx.txn.target,NONE,id,tv,v)] (initial_state am sc)` by
    (Cases_on `ALOOKUP am.immutables cx.txn.target` >>
     gvs[const_cells_agree_def, initial_state_def, constant_machine_immutables_def,
         get_source_immutables_def]) >>
  qexistsl [`pv`,`[(cx.txn.target,NONE,id,tv,v)] ++ roots`] >>
  simp[const_cells_agree_append, constant_roots_provenance_append] >>
  conj_tac
  >- (simp[constant_roots_provenance_def, declared_constant_def] >>
      metis_tac[ALOOKUP_MEM]) >>
  simp[const_results_related_def] >> disj2_tac >> qexists `v` >> conj_tac
  >- (gvs[const_result_at_def, subscripts_type_def, evaluate_subscripts_def] >>
      metis_tac[]) >>
  irule const_result_at_mono >> qexists `roots` >> simp[]
QED

Theorem const_results_related_mono:
  (!cell. MEM cell xs ==> MEM cell ys) /\ const_results_related xs cx ty p q ==>
  const_results_related ys cx ty p q
Proof
  simp[const_results_related_def] >> metis_tac[const_result_at_mono]
QED

Theorem const_replacement_footprints_union:
  !ns.
  (!id r. MEM id ns /\ ALOOKUP E id = SOME r ==>
    ?pv roots. const_cells_agree roots st0 /\
      constant_roots_provenance mods cx.txn.target roots /\
      const_results_related roots cx (expr_type r)
        (PlaceR (ImmutablePlace NONE id [])) pv /\
      (!st. const_cells_agree roots st ==> eval_expr cx r st = (INL pv,st))) ==>
  ?roots. const_cells_agree roots st0 /\
    constant_roots_provenance mods cx.txn.target roots /\
    (!id r. MEM id ns /\ ALOOKUP E id = SOME r ==>
      ?pv. const_results_related roots cx (expr_type r)
        (PlaceR (ImmutablePlace NONE id [])) pv /\
      (!st. const_cells_agree roots st ==> eval_expr cx r st = (INL pv,st)))
Proof
  Induct
  >- (simp[] >> qexists `[]` >>
      simp[const_cells_agree_def, constant_roots_provenance_def]) >>
  gen_tac >> strip_tac >>
  `?ys. const_cells_agree ys st0 /\
    constant_roots_provenance mods cx.txn.target ys /\
    (!id r. MEM id ns /\ ALOOKUP E id = SOME r ==>
      ?pv. const_results_related ys cx (expr_type r)
        (PlaceR (ImmutablePlace NONE id [])) pv /\
      (!st. const_cells_agree ys st ==> eval_expr cx r st = (INL pv,st)))` by
    (first_x_assum irule >> metis_tac[MEM]) >>
  Cases_on `ALOOKUP E h`
  >- (qexists `ys` >> simp[] >> rpt strip_tac >> gvs[] >>
      first_x_assum irule >> simp[]) >>
  rename1 `ALOOKUP E h = SOME r0` >>
  `?pv xs. const_cells_agree xs st0 /\
    constant_roots_provenance mods cx.txn.target xs /\
    const_results_related xs cx (expr_type r0)
      (PlaceR (ImmutablePlace NONE h [])) pv /\
    (!st. const_cells_agree xs st ==> eval_expr cx r0 st = (INL pv,st))` by
    metis_tac[MEM] >>
  qexists `xs ++ ys` >>
  simp[const_cells_agree_append, constant_roots_provenance_append] >>
  rpt strip_tac >> gvs[]
  >- (qexists `pv` >> conj_tac
      >- (irule const_results_related_mono >> qexists `xs` >> simp[MEM_APPEND]) >>
      metis_tac[]) >>
  qpat_x_assum `!id r. MEM id ns /\ _ ==> ?pv. const_results_related ys _ _ _ _ /\ _`
    (qspecl_then [`id`,`r`] mp_tac) >> simp[] >>
  disch_then (qx_choose_then `qv` strip_assume_tac) >> qexists `qv` >> conj_tac
  >- (irule const_results_related_mono >> qexists `ys` >> simp[MEM_APPEND]) >>
  metis_tac[]
QED

Theorem checked_module_consts_env_replay_footprint:
  check_contract F cx.layouts cx.txn.target mods = SOME artifact /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  ALOOKUP mods NONE = SOME tops /\
  constants_fold_module mods imms NONE tops FEMPTY = SOME A /\
  (!id r. ALOOKUP (module_consts_env tops []) id = SOME r ==>
    no_sha256_expr r) /\
  (!src. IS_SOME src ==>
    get_source_immutables src (constant_machine_immutables am cx.txn.target) =
    get_source_immutables src imms) /\
  (!id tv v. FLOOKUP A id = SOME (tv,v) ==>
    FLOOKUP (get_source_immutables NONE
      (constant_machine_immutables am cx.txn.target)) id = SOME (tv,v)) /\
  deployment_constant_cells_typed (type_env_all_modules mods) cx.txn.target mods am ==>
  ?roots. const_cells_agree roots (initial_state am sc) /\
    constant_roots_provenance mods cx.txn.target roots /\
    (!id r. ALOOKUP (module_consts_env tops []) id = SOME r ==>
      ?pv. const_results_related roots cx (expr_type r)
        (PlaceR (ImmutablePlace NONE id [])) pv /\
      (!st. const_cells_agree roots st ==> eval_expr cx r st = (INL pv,st)))
Proof
  strip_tac >>
  `!id r. MEM id (MAP FST (module_consts_env tops [])) /\
    ALOOKUP (module_consts_env tops []) id = SOME r ==>
    ?pv roots. const_cells_agree roots (initial_state am sc) /\
      constant_roots_provenance mods cx.txn.target roots /\
      const_results_related roots cx (expr_type r)
        (PlaceR (ImmutablePlace NONE id [])) pv /\
      (!st. const_cells_agree roots st ==> eval_expr cx r st = (INL pv,st))` by
    (rpt strip_tac >> irule checked_module_consts_env_replacement_replay >>
     simp[] >> metis_tac[]) >>
  drule const_replacement_footprints_union >> strip_tac >>
  qexists `roots` >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> simp[] >>
  drule ALOOKUP_MEM >> strip_tac >> simp[MEM_MAP] >>
  qexists `(id,r)` >> simp[]
QED

Theorem constant_roots_checked_frame_context:
  constant_roots_provenance mods cx.txn.target roots /\
  check_contract F cx.layouts cx.txn.target mods = SOME artifact /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\ frame_maps env artifact ==>
  !addr src id tv v. MEM (addr,src,id,tv,v) roots ==>
    addr = cx.txn.target /\ checked_frame_context cx mods artifact src id env
Proof
  simp[constant_roots_provenance_def, checked_frame_context_def] >> metis_tac[]
QED

(* Congruence boundaries retain delayed results until the interpreter reads them. *)
Theorem const_computations_related_refl:
  (!x. R x x) ==> const_computations_related R f f st
Proof
  Cases_on `f st` >> Cases_on `q` >> simp[const_computations_related_def]
QED

Theorem const_computations_related_equal:
  f st = g st /\ (!x. R x x) ==> const_computations_related R f g st
Proof
  strip_tac >> Cases_on `g st` >> Cases_on `q` >>
  gvs[const_computations_related_def]
QED

Theorem const_computations_related_bind:
  const_computations_related R f g st /\
  (!x y s. f st = (INL x,s) /\ g st = (INL y,s) /\ R x y ==>
    const_computations_related Rel (k x) (l y) s) ==>
  const_computations_related Rel (bind f k) (bind g l) st
Proof
  rw[const_computations_related_def] >>
  Cases_on `a` >> Cases_on `b` >> gvs[bind_def] >> metis_tac[]
QED

Theorem const_computations_related_read:
  const_results_related roots cx ty p q /\ const_cells_agree roots st ==>
  const_computations_related $= (read_result cx p) (read_result cx q) st
Proof
  strip_tac >> drule_all const_results_related_read >> strip_tac >>
  irule const_computations_related_equal >> simp[]
QED

Theorem const_computations_related_read_results:
  const_result_lists_related roots cx tys ps qs /\ const_cells_agree roots st ==>
  const_computations_related $= (read_results cx ps) (read_results cx qs) st
Proof
  strip_tac >> drule_all const_result_lists_related_read >> strip_tac >>
  irule const_computations_related_equal >> simp[]
QED

Theorem const_computations_related_attribute:
  const_computations_related (const_results_related roots cx ct) f g st /\
  (!p s. f st = (INL p,s) ==> const_cells_agree roots s) /\
  attribute_type (get_tenv cx) ct id = SOME ty ==>
  const_computations_related (const_results_related roots cx ty)
    (bind f (\p. select_result cx ct p (AttrSubscript id)))
    (bind g (\q. select_result cx ct q (AttrSubscript id))) st
Proof
  strip_tac >> irule const_computations_related_bind >>
  qexists `const_results_related roots cx ct` >> simp[] >>
  rpt strip_tac >> irule const_results_related_attribute >> metis_tac[]
QED

Theorem const_computations_related_length:
  const_computations_related (const_results_related roots cx ct) f g st /\
  (!p s. f st = (INL p,s) ==> const_cells_agree roots s) ==>
  const_computations_related $=
    (bind f (result_array_length cx)) (bind g (result_array_length cx)) st
Proof
  strip_tac >> irule const_computations_related_bind >>
  qexists `const_results_related roots cx ct` >> simp[] >> rpt strip_tac >>
  `result_array_length cx x s = result_array_length cx y s` by
    metis_tac[const_results_related_length] >>
  irule const_computations_related_equal >> simp[]
QED

Theorem const_computations_related_conditional:
  const_computations_related (const_results_related roots cx ty) f g st /\
  (!p s. f st = (INL p,s) ==> const_cells_agree roots s) ==>
  const_computations_related (const_results_related roots cx ty)
    (bind f (conditional_result cx)) (bind g (conditional_result cx)) st
Proof
  strip_tac >> irule const_computations_related_bind >>
  qexists `const_results_related roots cx ty` >> simp[] >> rpt strip_tac >>
  irule const_computations_related_equal >> simp[const_results_related_def] >>
  metis_tac[const_results_related_conditional]
QED

Theorem const_computations_related_switch:
  const_results_related roots cx ct p q /\ const_cells_agree roots st /\
  const_computations_related Rel f f' st /\
  const_computations_related Rel g g' st ==>
  const_computations_related Rel (switch_BoolV cx p f g)
    (switch_BoolV cx q f' g') st
Proof
  strip_tac >> rewrite_tac[switch_BoolV_def] >>
  irule const_computations_related_bind >> qexists `$=` >>
  reverse conj_tac >- metis_tac[const_computations_related_read] >> rpt strip_tac >>
  `s = st` by metis_tac[read_result_state] >> gvs[] >>
  Cases_on `x = BoolV T` >> simp[] >> Cases_on `x = BoolV F` >> simp[] >>
  simp[const_computations_related_def, raise_def]
QED

Theorem const_computations_related_ifexp:
  const_computations_related (const_results_related roots cx ct) c c' st /\
  (!p s. c st = (INL p,s) ==> const_cells_agree roots s) /\
  (!s. const_cells_agree roots s ==>
    const_computations_related (const_results_related roots cx ty) f f' s /\
    const_computations_related (const_results_related roots cx ty) g g' s) /\
  (!p s. bind c (\v. switch_BoolV cx v f g) st = (INL p,s) ==>
    const_cells_agree roots s) ==>
  const_computations_related (const_results_related roots cx ty)
    (bind (bind c (\v. switch_BoolV cx v f g)) (conditional_result cx))
    (bind (bind c' (\v. switch_BoolV cx v f' g')) (conditional_result cx)) st
Proof
  strip_tac >> irule const_computations_related_conditional >> simp[] >>
  irule const_computations_related_bind >>
  qexists `const_results_related roots cx ct` >> simp[] >> rpt strip_tac >>
  irule const_computations_related_switch >> metis_tac[]
QED

Theorem const_computations_related_subscript:
  const_computations_related (const_results_related roots cx ct) bf bf' st /\
  (!p s. bf st = (INL p,s) ==> const_cells_agree roots s) /\
  (!s. const_cells_agree roots s ==>
    const_computations_related (const_results_related roots cx it) idx idx' s) /\
  (!s p t. const_cells_agree roots s /\ idx s = (INL p,t) ==>
    const_cells_agree roots t) /\ subscript_type_ok ct ie ty /\
  (!s p t v. const_cells_agree roots s /\ idx s = (INL p,t) /\
    read_result cx p t = (INL v,t) ==>
    vyperTypeExprResult$subscript_index_matches ct ie v) ==>
  const_computations_related (const_results_related roots cx ty)
    (bind bf (\p. bind idx (\i. bind (read_result cx i)
      (\v. select_result cx ct p (ValueSubscript v)))))
    (bind bf' (\p. bind idx' (\i. bind (read_result cx i)
      (\v. select_result cx ct p (ValueSubscript v))))) st
Proof
  strip_tac >> irule const_computations_related_bind >>
  qexists `const_results_related roots cx ct` >> simp[] >> rpt strip_tac >>
  rename1 `const_results_related roots cx ct p q` >>
  `const_cells_agree roots s` by metis_tac[] >>
  irule const_computations_related_bind >>
  qexists `const_results_related roots cx it` >> simp[] >> rpt strip_tac >>
  rename1 `idx s = (INL ip,t)` >>
  `const_cells_agree roots t` by metis_tac[] >>
  irule const_computations_related_bind >> qexists `$=` >>
  reverse conj_tac >- metis_tac[const_computations_related_read] >> rpt strip_tac >>
  `s' = t` by metis_tac[read_result_state] >> gvs[] >>
  irule const_results_related_subscript >> metis_tac[]
QED

Theorem const_computations_related_prefix:
  const_computations_related $= f g st /\
  (!x s. f st = (INL x,s) ==> const_computations_related Rel (k x) (l x) s) ==>
  const_computations_related Rel (bind f k) (bind g l) st
Proof
  strip_tac >> irule const_computations_related_bind >> qexists `$=` >>
  simp[] >> metis_tac[]
QED

Theorem const_computations_related_subscript_exact_base:
  bf st = bf' st /\
  (!p s. bf st = (INL p,s) ==> const_cells_agree roots s) /\
  (!s. const_cells_agree roots s ==>
    const_computations_related (const_results_related roots cx it) idx idx' s) /\
  (!s p t. const_cells_agree roots s /\ idx s = (INL p,t) ==>
    const_cells_agree roots t) ==>
  const_computations_related $=
    (bind bf (\p. bind idx (\i. bind (read_result cx i)
      (\v. select_result cx ct p (ValueSubscript v)))))
    (bind bf' (\p. bind idx' (\i. bind (read_result cx i)
      (\v. select_result cx ct p (ValueSubscript v))))) st
Proof
  strip_tac >> irule const_computations_related_prefix >> reverse conj_tac
  >- (irule const_computations_related_equal >> simp[]) >>
  rpt strip_tac >> BETA_TAC >> irule const_computations_related_bind >>
  qexists `const_results_related roots cx it` >> reverse conj_tac
  >- metis_tac[] >> rpt strip_tac >> BETA_TAC >>
  irule const_computations_related_prefix >> reverse conj_tac
  >- (irule const_computations_related_read >> metis_tac[]) >>
  rpt strip_tac >> irule const_computations_related_refl >> simp[]
QED

Theorem const_computations_related_delayed_read:
  const_result_lists_related roots cx tys ps qs /\
  const_computations_related $= f g st /\
  (!x s. f st = (INL x,s) ==> const_cells_agree roots s) /\
  (!x. Rel x x) ==>
  const_computations_related Rel
    (bind f (\x. bind (read_results cx ps) (k x)))
    (bind g (\x. bind (read_results cx qs) (k x))) st
Proof
  strip_tac >> irule const_computations_related_prefix >> simp[] >> rpt strip_tac >>
  irule const_computations_related_prefix >> reverse conj_tac
  >- metis_tac[const_computations_related_read_results] >>
  rpt strip_tac >> irule const_computations_related_refl >> simp[]
QED

Theorem const_computations_related_arguments:
  const_computations_related (const_result_lists_related roots cx tys) args args' st /\
  (!ps s. args st = (INL ps,s) ==> const_cells_agree roots s) /\
  (!s. const_cells_agree roots s ==> const_computations_related $= suffix suffix' s) /\
  (!s x t. const_cells_agree roots s /\ suffix s = (INL x,t) ==>
    const_cells_agree roots t) /\ (!x. Rel x x) ==>
  const_computations_related Rel
    (bind args (\ps. bind suffix (\x. bind (read_results cx ps) (k x))))
    (bind args' (\ps. bind suffix' (\x. bind (read_results cx ps) (k x)))) st
Proof
  strip_tac >> irule const_computations_related_bind >>
  qexists `const_result_lists_related roots cx tys` >> simp[] >> rpt strip_tac >>
  irule const_computations_related_delayed_read >> metis_tac[]
QED

Theorem checked_intcall_defaults_protected_cell_frame:
  checked_frame_context cx mods art src id env /\
  well_typed_expr env (Call ty (IntCall (call_src,fn)) es drv) /\
  get_module_code cx call_src = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,ss) ==>
  state_rel_frame (protected_cell_frame addr src id)
    (finally
      (bind (set_scopes [FEMPTY]) (\u.
        eval_exprs (cx with stk updated_by CONS (call_src,fn)) (DROP n dflts)))
      (set_scopes prev))
Proof
  strip_tac >> drule_all checked_frame_intcall_static >> strip_tac >>
  irule protected_cell_frame_finally >> simp[protected_cell_frame_primitives] >>
  irule protected_cell_frame_bind >> simp[protected_cell_frame_primitives] >>
  rpt strip_tac >> simp_tac bool_ss [] >>
  irule checked_eval_exprs_protected_cell_frame >>
  qexistsl [`art`,`defaults_env (function_entry_env art mods call_src Internal args)`,`mods`] >>
  simp[] >> conj_tac
  >- (irule (cj 2 frame_well_typed_exprs_slices) >> simp[]) >>
  gvs[checked_frame_context_def]
QED

Theorem checked_intcall_defaults_const_cells_agree:
  well_typed_expr env (Call ty (IntCall (call_src,fn)) es drv) /\
  get_module_code cx call_src = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,ss) /\
  (!addr src id tv root. MEM (addr,src,id,tv,root) roots ==>
    checked_frame_context cx mods art src id env) /\
  const_cells_agree roots st /\
  finally
    (bind (set_scopes [FEMPTY]) (\u.
      eval_exprs (cx with stk updated_by CONS (call_src,fn)) (DROP n dflts)))
    (set_scopes prev) st = (res,st') ==>
  const_cells_agree roots st'
Proof
  strip_tac >> irule protected_cell_frame_cells_agree >>
  qexists `st` >> simp[] >> rpt strip_tac >>
  `state_rel_frame (protected_cell_frame addr src id)
    (finally
      (bind (set_scopes [FEMPTY]) (\u.
        eval_exprs (cx with stk updated_by CONS (call_src,fn)) (DROP n dflts)))
      (set_scopes prev))` by
    (irule checked_intcall_defaults_protected_cell_frame >> metis_tac[]) >>
  gvs[state_rel_frame_result] >> metis_tac[]
QED

Theorem const_computations_related_observe_results:
  const_computations_related (const_result_lists_related roots cx tys) f g st /\
  (!ps s. f st = (INL ps,s) ==> const_cells_agree roots s) ==>
  const_computations_related $= (bind f (read_results cx)) (bind g (read_results cx)) st
Proof
  strip_tac >> irule const_computations_related_bind >>
  qexists `const_result_lists_related roots cx tys` >> simp[] >> rpt strip_tac >>
  irule const_computations_related_read_results >> metis_tac[]
QED

Theorem const_computations_related_extcall:
  const_computations_related $= target target' st /\
  (!v s. target st = (INL v,s) ==> const_cells_agree roots s) /\
  (!s. const_cells_agree roots s ==>
    const_computations_related (const_result_lists_related roots cx tys) actuals actuals' s) /\
  (!s ps t. const_cells_agree roots s /\ actuals s = (INL ps,t) ==>
    const_cells_agree roots t) /\
  (!s. const_cells_agree roots s ==> const_computations_related $= kwargs kwargs' s) /\
  (!s kw t. const_cells_agree roots s /\ kwargs s = (INL kw,t) ==>
    const_cells_agree roots t) ==>
  const_computations_related (const_results_related roots cx ty)
    (bind target (\tg. bind actuals (\ps. bind kwargs (\kw.
      bind (read_results cx ps) (\vs. eval_ext_call cx static skip sig opts (tg ++ vs ++ kw))))))
    (bind target' (\tg. bind actuals' (\ps. bind kwargs' (\kw.
      bind (read_results cx ps) (\vs. eval_ext_call cx static skip sig opts (tg ++ vs ++ kw)))))) st
Proof
  strip_tac >> irule const_computations_related_prefix >> simp[] >> rpt strip_tac >>
  ho_match_mp_tac const_computations_related_arguments >>
  simp[const_results_related_def] >> metis_tac[]
QED

Theorem const_computations_related_create_blueprint:
  const_computations_related $= prefix prefix' st /\
  (!v s. prefix st = (INL v,s) ==> const_cells_agree roots s) /\
  (!s. const_cells_agree roots s ==>
    const_computations_related (const_result_lists_related roots cx tys) actuals actuals' s) /\
  (!s ps t. const_cells_agree roots s /\ actuals s = (INL ps,t) ==>
    const_cells_agree roots t) ==>
  const_computations_related (const_results_related roots cx ty)
    (bind prefix (\pre. bind (check_create_blueprint salt pre) (\sz.
      bind (bind actuals (read_results cx)) (\vs.
        eval_create cx (CreateFromBlueprint raw_args) salt rof ats (pre ++ vs) (SOME sz)))))
    (bind prefix' (\pre. bind (check_create_blueprint salt pre) (\sz.
      bind (bind actuals' (read_results cx)) (\vs.
        eval_create cx (CreateFromBlueprint raw_args) salt rof ats (pre ++ vs) (SOME sz))))) st
Proof
  strip_tac >> irule const_computations_related_prefix >> simp[] >> rpt strip_tac >>
  `const_cells_agree roots s` by metis_tac[] >>
  irule const_computations_related_prefix >> reverse conj_tac
  >- (irule const_computations_related_refl >> simp[]) >> rpt strip_tac >>
  drule check_create_blueprint_result_state >> strip_tac >> gvs[] >>
  irule const_computations_related_prefix >> reverse conj_tac
  >- (irule const_computations_related_observe_results >> qexistsl [`roots`,`tys`] >> metis_tac[]) >>
  rpt strip_tac >> irule const_computations_related_refl >> simp[const_results_related_def]
QED

Theorem const_computations_related_raw_create:
  const_computations_related $= prefix prefix' st /\
  (!v s. prefix st = (INL v,s) ==> const_cells_agree roots s) /\
  (!s. const_cells_agree roots s ==>
    const_computations_related (const_result_lists_related roots cx tys) actuals actuals' s) /\
  (!s ps t. const_cells_agree roots s /\ actuals s = (INL ps,t) ==>
    const_cells_agree roots t) /\
  (!s. const_cells_agree roots s ==> const_computations_related $= salt salt' s) ==>
  const_computations_related (const_results_related roots cx ty)
    (bind prefix (\pre. bind (bind actuals (read_results cx)) (\vs.
      bind salt (\sv. eval_create cx RawCreate has_salt rof ats (pre ++ vs ++ sv) NONE))))
    (bind prefix' (\pre. bind (bind actuals' (read_results cx)) (\vs.
      bind salt' (\sv. eval_create cx RawCreate has_salt rof ats (pre ++ vs ++ sv) NONE)))) st
Proof
  strip_tac >> irule const_computations_related_prefix >> simp[] >> rpt strip_tac >>
  `const_cells_agree roots s` by metis_tac[] >>
  irule const_computations_related_prefix >> reverse conj_tac
  >- (irule const_computations_related_observe_results >> qexistsl [`roots`,`tys`] >> metis_tac[]) >>
  rpt strip_tac >>
  qpat_x_assum `bind actuals _ _ = (INL _,_)` mp_tac >>
  simp[bind_def, AllCaseEqs()] >> rpt strip_tac >>
  drule read_results_state >> strip_tac >> gvs[] >>
  irule const_computations_related_prefix >> reverse conj_tac
  >- (first_x_assum irule >> metis_tac[]) >>
  rpt strip_tac >> irule const_computations_related_refl >> simp[const_results_related_def]
QED

Theorem const_computations_related_intcall_arguments:
  const_computations_related (const_result_lists_related roots cx tys)
    (eval_expr_results cx es) actuals' st /\
  (!ps s. eval_expr_results cx es st = (INL ps,s) ==> const_cells_agree roots s) /\
  well_typed_expr env (Call ty (IntCall (call_src,fn)) es drv) /\
  get_module_code cx call_src = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,ss) /\
  (!addr src id tv root. MEM (addr,src,id,tv,root) roots ==>
    checked_frame_context cx mods art src id env) /\ (!x. Rel x x) ==>
  const_computations_related Rel
    (bind (eval_expr_results cx es) (\ps. bind get_scopes (\prev.
      bind (finally
        (bind (set_scopes [FEMPTY]) (\u.
          eval_exprs (cx with stk updated_by CONS (call_src,fn)) (DROP n dflts)))
        (set_scopes prev)) (\vs. bind (read_results cx ps) (k prev vs)))))
    (bind actuals' (\ps. bind get_scopes (\prev.
      bind (finally
        (bind (set_scopes [FEMPTY]) (\u.
          eval_exprs (cx with stk updated_by CONS (call_src,fn)) (DROP n dflts)))
        (set_scopes prev)) (\vs. bind (read_results cx ps) (k prev vs))))) st
Proof
  strip_tac >> irule const_computations_related_bind >>
  qexists `const_result_lists_related roots cx tys` >> simp[] >> rpt strip_tac >>
  `const_cells_agree roots s` by metis_tac[] >>
  irule const_computations_related_prefix >> reverse conj_tac
  >- (irule const_computations_related_refl >> simp[]) >> rpt strip_tac >>
  qpat_x_assum `get_scopes _ = _` mp_tac >>
  simp[get_scopes_def, return_def] >> strip_tac >> gvs[] >>
  ho_match_mp_tac const_computations_related_delayed_read >> simp[] >>
  reverse conj_tac
  >- (rpt strip_tac >> irule checked_intcall_defaults_const_cells_agree >>
      metis_tac[]) >>
  irule const_computations_related_refl >> simp[]
QED

Theorem const_computations_related_intcall_results:
  const_computations_related (const_result_lists_related roots cx tys)
    (eval_expr_results cx es) actuals' st /\
  (!ps s. eval_expr_results cx es st = (INL ps,s) ==> const_cells_agree roots s) /\
  well_typed_expr env (Call ty (IntCall (call_src,fn)) es drv) /\
  get_module_code cx call_src = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,ss) /\
  (!addr src id tv root. MEM (addr,src,id,tv,root) roots ==>
    checked_frame_context cx mods art src id env) ==>
  const_computations_related (const_results_related roots cx out_ty)
    (bind (eval_expr_results cx es) (\ps. bind get_scopes (\prev.
      bind (finally
        (bind (set_scopes [FEMPTY]) (\u.
          eval_exprs (cx with stk updated_by CONS (call_src,fn)) (DROP n dflts)))
        (set_scopes prev)) (\vs. bind (read_results cx ps) (\vals. k prev vs vals)))))
    (bind actuals' (\ps. bind get_scopes (\prev.
      bind (finally
        (bind (set_scopes [FEMPTY]) (\u.
          eval_exprs (cx with stk updated_by CONS (call_src,fn)) (DROP n dflts)))
        (set_scopes prev)) (\vs. bind (read_results cx ps) (\vals. k prev vs vals))))) st
Proof
  strip_tac >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
  ho_match_mp_tac (INST_TYPE [alpha |-> ``:eval_result``]
    const_computations_related_intcall_arguments) >>
  simp[const_results_related_def] >> metis_tac[]
QED

(* Fixed-footprint inputs for the structural induction.  The collector
   specialization discharges these static maps and pure replay facts. *)
Definition const_subst_context_def:
  const_subst_context roots cx env E mods art <=>
    env.type_defs = get_tenv cx /\
    (!addr src id tv root. MEM (addr,src,id,tv,root) roots ==>
      checked_frame_context cx mods art src id env) /\
    (!id r. ALOOKUP E id = SOME r ==>
      FLOOKUP env.bare_globals (NONE,id) = SOME (expr_type r) /\
      FLOOKUP env.toplevel_vtypes (NONE,id) = SOME (Type (expr_type r)) /\
      (!st. const_cells_agree roots st ==>
        lookup_global cx NONE id st = (INL (PlaceR (ImmutablePlace NONE id [])),st)) /\
      ?pv. const_results_related roots cx (expr_type r)
        (PlaceR (ImmutablePlace NONE id [])) pv /\
        (!st. const_cells_agree roots st ==> eval_expr cx r st = (INL pv,st)))
End

Theorem const_subst_typed_annotation:
  const_subst_context roots cx env E mods art /\
  (well_typed_expr env e \/ IS_SOME (type_place_expr env e)) ==>
  expr_type (subst_consts_expr E e) = expr_type e
Proof
  strip_tac >> Cases_on `e` >>
  simp[subst_consts_expr_def, expr_type_def] >>
  PairCases_on `p` >> Cases_on `p0` >>
  simp[subst_consts_expr_def, expr_type_def] >>
  Cases_on `ALOOKUP E p1` >> simp[expr_type_def] >>
  gvs[const_subst_context_def] >>
  first_x_assum drule >> strip_tac >>
  gvs[well_typed_expr_def, vtype_annotation_ok_def]
QED

Theorem subst_consts_exprs_map:
  subst_consts_exprs E es = MAP (subst_consts_expr E) es
Proof
  Induct_on `es` >> simp[subst_consts_expr_def]
QED

Theorem subst_consts_fields_maps:
  MAP FST (subst_consts_fields E fs) = MAP FST fs /\
  MAP SND (subst_consts_fields E fs) = subst_consts_exprs E (MAP SND fs)
Proof
  Induct_on `fs` >> simp[subst_consts_expr_def] >>
  gen_tac >> PairCases_on `h` >> simp[subst_consts_expr_def]
QED

Theorem const_subst_typed_annotations:
  const_subst_context roots cx env E mods art /\ well_typed_exprs env es ==>
  MAP expr_type (subst_consts_exprs E es) = MAP expr_type es
Proof
  Induct_on `es` >> simp[well_typed_expr_def, subst_consts_expr_def] >>
  rpt strip_tac >> metis_tac[const_subst_typed_annotation]
QED

Theorem const_subst_context_expr_frame:
  const_subst_context roots cx env E mods art /\
  (well_typed_expr env e \/ IS_SOME (type_place_expr env e)) /\
  const_cells_agree roots st /\ eval_expr cx e st = (res,st') ==>
  const_cells_agree roots st'
Proof
  simp[const_subst_context_def, optionTheory.IS_SOME_EXISTS] >>
  metis_tac[checked_eval_expr_or_place_const_cells_agree]
QED

Theorem const_subst_context_exprs_frame:
  const_subst_context roots cx env E mods art /\
  well_typed_exprs env es /\ const_cells_agree roots st /\
  eval_exprs cx es st = (res,st') ==> const_cells_agree roots st'
Proof
  strip_tac >> irule protected_cell_frame_cells_agree >>
  qexists `st` >> simp[] >> rpt strip_tac >>
  gvs[const_subst_context_def] >>
  `checked_frame_context cx mods art src id env` by metis_tac[] >>
  drule_all checked_eval_exprs_protected_cell_frame >>
  simp[state_rel_frame_result] >> metis_tac[]
QED

Theorem const_subst_context_results_frame:
  const_subst_context roots cx env E mods art /\
  well_typed_exprs env es /\ const_cells_agree roots st /\
  eval_expr_results cx es st = (res,st') ==> const_cells_agree roots st'
Proof
  strip_tac >> irule protected_cell_frame_cells_agree >>
  qexists `st` >> simp[] >> rpt strip_tac >>
  gvs[const_subst_context_def] >>
  `checked_frame_context cx mods art src id env` by metis_tac[] >>
  drule_all checked_eval_expr_results_protected_cell_frame >>
  simp[state_rel_frame_result] >> metis_tac[]
QED

Theorem const_subst_context_base_frame:
  const_subst_context roots cx env E mods art /\
  IS_SOME (type_place_target env bt) /\ const_cells_agree roots st /\
  eval_base_place cx bt st = (res,st') ==>
  const_cells_agree roots st'
Proof
  strip_tac >> irule protected_cell_frame_cells_agree >>
  qexists `st` >> simp[] >> rpt strip_tac >>
  gvs[const_subst_context_def] >>
  metis_tac[cj 7 checked_protected_cell_frame_mutual]
QED

Definition const_subst_expr_ok_def:
  const_subst_expr_ok roots cx env E e <=>
    (well_typed_expr env e \/ IS_SOME (type_place_expr env e)) ==>
    !st. const_cells_agree roots st ==>
      const_computations_related (const_results_related roots cx (expr_type e))
        (eval_expr cx e) (eval_expr cx (subst_consts_expr E e)) st /\
      (!kt vt. type_place_expr env e = SOME (HashMapT kt vt) ==>
        eval_expr cx e st = eval_expr cx (subst_consts_expr E e) st)
End

Definition const_subst_btarget_ok_def:
  const_subst_btarget_ok roots cx env E bt <=>
    IS_SOME (type_place_target env bt) ==>
    !st. const_cells_agree roots st ==>
      eval_base_place cx bt st = eval_base_place cx (subst_consts_btarget E bt) st /\
      eval_target_place cx bt st = eval_target_place cx (subst_consts_btarget E bt) st
End

Definition const_subst_exprs_ok_def:
  const_subst_exprs_ok roots cx env E es <=>
    well_typed_exprs env es ==>
    !st. const_cells_agree roots st ==>
      eval_exprs cx es st = eval_exprs cx (subst_consts_exprs E es) st /\
      const_computations_related (const_result_lists_related roots cx (MAP expr_type es))
        (eval_expr_results cx es) (eval_expr_results cx (subst_consts_exprs E es)) st
End

Theorem const_computations_related_eq:
  const_computations_related $= f g st <=> f st = g st
Proof
  Cases_on `f st` >> Cases_on `g st` >> Cases_on `q` >> Cases_on `q'` >>
  simp[const_computations_related_def] >> metis_tac[]
QED

Theorem const_result_lists_related_cons:
  const_result_lists_related roots cx (ty::tys) (p::ps) (q::qs) <=>
  const_results_related roots cx ty p q /\
  const_result_lists_related roots cx tys ps qs
Proof
  simp[const_result_lists_related_def, CONJ_ASSOC]
QED

Theorem const_subst_expr_observe:
  const_subst_context roots cx env E mods art /\
  const_subst_expr_ok roots cx env E e /\ well_typed_expr env e /\
  const_cells_agree roots st ==>
  bind (eval_expr cx e) (read_result cx) st =
  bind (eval_expr cx (subst_consts_expr E e)) (read_result cx) st
Proof
  strip_tac >> rewrite_tac[GSYM const_computations_related_eq] >>
  irule const_computations_related_bind >>
  qexists `const_results_related roots cx (expr_type e)` >>
  reverse conj_tac >- gvs[const_subst_expr_ok_def] >>
  rpt strip_tac >> irule const_computations_related_read >> simp[] >>
  metis_tac[const_subst_context_expr_frame]
QED

Theorem const_subst_exprs_from_elements:
  !es. const_subst_context roots cx env E mods art /\
    EVERY (const_subst_expr_ok roots cx env E) es ==>
    const_subst_exprs_ok roots cx env E es
Proof
  Induct
  >- simp[const_subst_exprs_ok_def, subst_consts_expr_def,
      evaluate_def, return_def, const_computations_related_def,
      const_result_lists_related_def] >>
  gen_tac >> strip_tac >>
  simp[const_subst_exprs_ok_def, well_typed_expr_def] >>
  strip_tac >> gen_tac >> strip_tac >> conj_tac
  >- (gvs[EVERY_DEF] >>
      simp_tac bool_ss [subst_consts_expr_def, Ntimes evaluate_def 2] >>
      rewrite_tac[GSYM const_computations_related_eq] >>
      irule const_computations_related_bind >>
      qexists `const_results_related roots cx (expr_type h)` >>
      reverse conj_tac >- gvs[const_subst_expr_ok_def] >>
      rpt strip_tac >>
      `const_cells_agree roots s` by metis_tac[const_subst_context_expr_frame] >>
      BETA_TAC >> irule const_computations_related_prefix >> reverse conj_tac
      >- metis_tac[const_computations_related_read] >>
      rpt strip_tac >> drule read_result_state >> strip_tac >> gvs[] >>
      irule const_computations_related_prefix >> reverse conj_tac
      >- gvs[const_computations_related_eq, const_subst_exprs_ok_def] >>
      rpt strip_tac >> irule const_computations_related_refl >> simp[]) >>
  gvs[EVERY_DEF] >>
  simp_tac bool_ss [subst_consts_expr_def, Ntimes evaluate_def 2] >>
  irule const_computations_related_bind >>
  qexists `const_results_related roots cx (expr_type h)` >>
  reverse conj_tac >- gvs[const_subst_expr_ok_def] >>
  rpt strip_tac >> BETA_TAC >>
  `const_cells_agree roots s` by metis_tac[const_subst_context_expr_frame] >>
  irule const_computations_related_bind >>
  qexists `const_result_lists_related roots cx (MAP expr_type es)` >>
  reverse conj_tac >- gvs[const_subst_exprs_ok_def] >>
  rpt strip_tac >> BETA_TAC >>
  simp[const_computations_related_def, return_def, const_result_lists_related_cons]
QED



Theorem eval_bind_assoc:
  bind (bind f g) h = bind f (\x. bind (g x) h)
Proof
  simp[FUN_EQ_THM, bind_def] >> gen_tac >>
  Cases_on `f x` >> Cases_on `q` >> simp[bind_def]
QED

Theorem const_computations_related_ifexp_eval:
  const_computations_related (const_results_related roots cx ct) c c' st /\
  (!p s. c st = (INL p,s) ==> const_cells_agree roots s) /\
  (!s. const_cells_agree roots s ==>
    const_computations_related (const_results_related roots cx ty) f f' s /\
    const_computations_related (const_results_related roots cx ty) g g' s) /\
  (!p s. bind c (\v. switch_BoolV cx v f g) st = (INL p,s) ==>
    const_cells_agree roots s) ==>
  const_computations_related (const_results_related roots cx ty)
    (bind c (\v. bind (switch_BoolV cx v f g) (conditional_result cx)))
    (bind c' (\v. bind (switch_BoolV cx v f' g') (conditional_result cx))) st
Proof
  MATCH_ACCEPT_TAC (BETA_RULE
    (PURE_REWRITE_RULE [eval_bind_assoc] const_computations_related_ifexp))
QED

(* Instantiate the five mutual predicates from the typed goal. *)
fun const_subst_structural_ind_tac (g as (_,w)) =
  let
    val cs = strip_conj w
    fun predicate c =
      let val (vs,b) = strip_forall c
      in
        if length vs = 2 then list_mk_abs (vs,b)
        else raise Fail "const_subst induction: expected two binders"
      end
    val ps = map predicate cs
    val ith =
      if length ps = 5 then
        BETA_RULE (ISPECL ps subst_consts_expr_ind)
      else raise Fail "const_subst induction: expected five conjuncts"
    val (_,conclusion) = dest_imp (concl ith)
  in
    if aconv conclusion w then MATCH_MP_TAC ith g
    else raise Fail "const_subst induction: specialized conclusion differs"
  end;

Theorem const_subst_structural:
  (!E e. const_subst_context roots cx env E mods art ==>
    const_subst_expr_ok roots cx env E e) /\
  (!E bt. const_subst_context roots cx env E mods art ==>
    const_subst_btarget_ok roots cx env E bt) /\
  (!E es. const_subst_context roots cx env E mods art ==>
    EVERY (const_subst_expr_ok roots cx env E) es) /\
  (!E opt. const_subst_context roots cx env E mods art ==>
    (case opt of NONE => T | SOME e => const_subst_expr_ok roots cx env E e)) /\
  (!E (fs : (string # expr) list). const_subst_context roots cx env E mods art ==>
    EVERY (const_subst_expr_ok roots cx env E) (MAP SND fs))
Proof
  const_subst_structural_ind_tac >>
  rpt conj_tac >> rpt gen_tac >> rpt strip_tac
  >~ [`const_subst_expr_ok _ _ _ _ (Name _ _)`]
  >- simp[const_subst_expr_ok_def, subst_consts_expr_def,
       const_computations_related_refl, const_results_related_def]
  >~ [`const_subst_expr_ok _ _ _ _ (FlagMember _ _ _)`]
  >- simp[const_subst_expr_ok_def, subst_consts_expr_def,
       const_computations_related_refl, const_results_related_def]
  >~ [`const_subst_expr_ok _ _ _ _ (Literal _ _)`]
  >- simp[const_subst_expr_ok_def, subst_consts_expr_def,
       const_computations_related_refl, const_results_related_def]
  >~ [`const_subst_btarget_ok _ _ _ _ (NameTarget _)`]
  >- simp[const_subst_btarget_ok_def, subst_consts_expr_def]
  >~ [`const_subst_btarget_ok _ _ _ _ (TopLevelNameTarget _)`]
  >- simp[const_subst_btarget_ok_def, subst_consts_expr_def]
  >~ [`const_subst_expr_ok _ _ _ _ (TopLevelName ty (ns,id))`]
  >- (Cases_on `ns`
      >- (Cases_on `ALOOKUP env' id`
          >- simp[const_subst_expr_ok_def, subst_consts_expr_def,
               const_computations_related_refl, const_results_related_def] >>
          gvs[const_subst_context_def] >>
          first_x_assum drule >> strip_tac >>
          simp[const_subst_expr_ok_def, subst_consts_expr_def, expr_type_def] >>
          rpt strip_tac >>
          gvs[well_typed_expr_def, vtype_annotation_ok_def,
              evaluate_def, const_computations_related_def]) >>
      simp[const_subst_expr_ok_def, subst_consts_expr_def,
        const_computations_related_refl, const_results_related_def])
  >~ [`const_subst_expr_ok _ _ _ _ (IfExp ty a b c)`]
  >- (gvs[] >> simp[const_subst_expr_ok_def, well_typed_expr_def] >>
      rpt strip_tac >>
      simp_tac bool_ss [subst_consts_expr_def, Ntimes evaluate_def 2] >>
      simp_tac bool_ss [SF ETA_ss, expr_type_def] >>
      irule const_computations_related_ifexp_eval >>
      rpt conj_tac
      >- metis_tac[const_subst_context_expr_frame, frame_subscript_typing,
                       optionTheory.IS_SOME_EXISTS]
      >- (rpt strip_tac >>
          gvs[bind_def, switch_BoolV_def, AllCaseEqs()] >>
          drule read_result_state >> strip_tac >> gvs[] >>
          `const_cells_agree roots s''` by
            metis_tac[const_subst_context_expr_frame] >>
          qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
          IF_CASES_TAC
          >- (simp[] >> strip_tac >> metis_tac[const_subst_context_expr_frame]) >>
          IF_CASES_TAC >> simp[raise_def] >> strip_tac >>
          metis_tac[const_subst_context_expr_frame])
      >- gvs[const_subst_expr_ok_def] >>
      qexists `expr_type a` >> gvs[const_subst_expr_ok_def])
  >> gvs[EVERY_DEF]
  >~ [`const_subst_expr_ok _ _ _ _ (StructLit ty ns fs)`]
  >- (PairCases_on `ns` >> simp[const_subst_expr_ok_def, well_typed_expr_def] >>
      rpt strip_tac >>
      simp_tac bool_ss [subst_consts_expr_def, Ntimes evaluate_def 2,
        subst_consts_fields_maps, expr_type_def] >>
      drule vyperTypeEvalSoundnessTheory.well_typed_named_exprs_MAP_SND_stmt >> strip_tac >>
      drule_all const_subst_exprs_from_elements >>
      simp[const_subst_exprs_ok_def] >> strip_tac >>
      simp_tac bool_ss [LET_THM] >>
      irule const_computations_related_prefix >> reverse conj_tac
      >- gvs[const_computations_related_eq] >>
      rpt strip_tac >> irule const_computations_related_refl >>
      simp[const_results_related_def])
  >~ [`const_subst_expr_ok _ _ _ _ (Attribute ty a id)`]
  >- (simp[const_subst_expr_ok_def, well_typed_expr_def] >>
      rpt strip_tac >>
      simp_tac bool_ss [subst_consts_expr_def, Ntimes evaluate_def 2, expr_type_def] >>
      `expr_type (subst_consts_expr env' a) = expr_type a` by
        metis_tac[const_subst_typed_annotation] >> simp[] >>
      irule const_computations_related_attribute >>
      rpt conj_tac
      >- metis_tac[const_subst_context_expr_frame]
      >- gvs[const_subst_context_def, attribute_type_ok_def] >>
      gvs[const_subst_expr_ok_def])
  >~ [`const_subst_btarget_ok _ _ _ _ (AttributeTarget tgt id)`]
  >- (simp[const_subst_btarget_ok_def, well_typed_expr_def, AllCaseEqs()] >>
      rpt strip_tac >>
      simp_tac bool_ss [subst_consts_expr_def, Ntimes evaluate_def 4] >>
      `IS_SOME (type_place_target env tgt)` by
        (Cases_on `type_place_target env tgt` >> gvs[]) >>
      gvs[const_subst_btarget_ok_def] >>
      simp[bind_def])
  >~ [`const_subst_expr_ok _ _ _ _ (Pop ty tgt)`]
  >- (simp[const_subst_expr_ok_def, well_typed_expr_def] >>
      rpt strip_tac >>
      simp_tac bool_ss [subst_consts_expr_def, Ntimes evaluate_def 2, expr_type_def] >>
      simp_tac bool_ss [Ntimes evaluate_def 3] >>
      irule const_computations_related_prefix >> reverse conj_tac
      >- (gvs[const_subst_btarget_ok_def, const_computations_related_eq] >>
          simp[bind_def]) >>
      rpt strip_tac >> irule const_computations_related_refl >>
      simp[const_results_related_def])
  >~ [`const_subst_expr_ok _ _ _ _ (TypeBuiltin ty bi t es)`]
  >- (simp[const_subst_expr_ok_def, well_typed_expr_def] >>
      rpt strip_tac >>
      simp_tac bool_ss [subst_consts_expr_def, Ntimes evaluate_def 2, expr_type_def] >>
      `MAP expr_type (subst_consts_exprs env' es) = MAP expr_type es` by
        metis_tac[const_subst_typed_annotations] >>
      simp[subst_consts_exprs_map] >>
      drule_all const_subst_exprs_from_elements >>
      simp[const_subst_exprs_ok_def] >> strip_tac >>
      rewrite_tac[ignore_bind_def] >>
      irule const_computations_related_prefix >> reverse conj_tac
      >- (irule const_computations_related_refl >> simp[]) >>
      rpt strip_tac >> BETA_TAC >>
      `s = st` by (gvs[type_check_def, assert_def, return_def, raise_def, AllCaseEqs()]) >>
      gvs[] >> irule const_computations_related_prefix >> reverse conj_tac
      >- gvs[const_computations_related_eq, subst_consts_exprs_map] >>
      rpt strip_tac >> irule const_computations_related_refl >>
      simp[const_results_related_def])
  >~ [`const_subst_btarget_ok _ _ _ _ (SubscriptTarget tgt e)`]
  >- (simp[const_subst_btarget_ok_def, well_typed_expr_def] >>
      strip_tac >> gen_tac >> strip_tac >>
      `well_typed_expr env e /\ IS_SOME (type_place_target env tgt)` by
        (Cases_on `well_typed_expr env e` >>
         Cases_on `type_place_target env tgt` >> gvs[]) >>
      `eval_base_place cx (SubscriptTarget tgt e) st =
       eval_base_place cx (subst_consts_btarget env' (SubscriptTarget tgt e)) st` by
       (simp_tac bool_ss [subst_consts_expr_def, Ntimes evaluate_def 2] >>
        rewrite_tac[GSYM const_computations_related_eq] >>
        irule const_computations_related_prefix >> reverse conj_tac
        >- gvs[const_subst_btarget_ok_def, const_computations_related_eq] >>
        rpt strip_tac >> BETA_TAC >>
        `const_cells_agree roots s` by metis_tac[const_subst_context_base_frame] >>
        simp_tac bool_ss [GSYM eval_bind_assoc] >>
        irule const_computations_related_prefix >> reverse conj_tac
        >- (simp[const_computations_related_eq] >>
            metis_tac[const_subst_expr_observe]) >>
        rpt strip_tac >> irule const_computations_related_refl >> simp[]) >>
      simp[] >>
      qpat_x_assum `eval_base_place cx (SubscriptTarget tgt e) st = _` mp_tac >>
      simp_tac bool_ss [evaluate_def, subst_consts_expr_def, bind_def] >>
      metis_tac[])
  >~ [`const_subst_expr_ok _ _ _ _ (Subscript ty a b)`]
  >- (simp[const_subst_expr_ok_def] >> disch_tac >>
      `well_typed_expr env b` by
        metis_tac[frame_subscript_typing, optionTheory.IS_SOME_EXISTS] >>
      drule (SRULE [GSYM optionTheory.IS_SOME_EXISTS] frame_subscript_typing) >>
      disch_then (assume_tac o CONJUNCT1) >>
      gen_tac >> strip_tac >>
      `expr_type (subst_consts_expr env' a) = expr_type a` by
        metis_tac[const_subst_typed_annotation, frame_subscript_typing,
                  optionTheory.IS_SOME_EXISTS] >>
      Cases_on `?kt vt. type_place_expr env a = SOME (HashMapT kt vt)`
      >- (pop_assum strip_assume_tac >>
          `eval_expr cx a st = eval_expr cx (subst_consts_expr env' a) st` by
            gvs[const_subst_expr_ok_def] >>
          `const_computations_related $=
            (eval_expr cx (Subscript ty a b))
            (eval_expr cx (Subscript ty (subst_consts_expr env' a) (subst_consts_expr env' b))) st` by
            (simp_tac bool_ss [Ntimes evaluate_def 2] >> simp[] >>
             irule const_computations_related_subscript_exact_base >>
             reverse conj_tac >- simp[] >>
             qexistsl [`expr_type b`, `roots`] >> rpt conj_tac
             >- metis_tac[const_subst_context_expr_frame, frame_subscript_typing,
                          optionTheory.IS_SOME_EXISTS]
             >- metis_tac[const_subst_context_expr_frame]
             >> gvs[const_subst_expr_ok_def]) >>
          gvs[const_computations_related_eq, subst_consts_expr_def] >>
          irule const_computations_related_equal >>
          simp[const_results_related_def]) >>
      `subscript_type_ok (expr_type a) b ty` by
        metis_tac[const_subscript_domain_type_ok] >>
      simp_tac bool_ss [subst_consts_expr_def, Ntimes evaluate_def 2, expr_type_def] >>
      simp[] >> conj_tac
      >- (irule const_computations_related_subscript >>
          rpt conj_tac
          >- metis_tac[const_subst_context_expr_frame]
          >- metis_tac[const_subst_context_expr_frame]
          >- (qexists `expr_type b` >> gvs[const_subst_expr_ok_def])
          >- (qexists `b` >> simp[] >> rpt strip_tac >>
              Cases_on `expr_type a` >>
              gvs[vyperTypeExprResultTheory.subscript_index_matches_def,
                  vyperTypeExprResultTheory.subscript_type_ok_tuple] >>
              gvs[Once evaluate_def, vyperValueOperationTheory.evaluate_literal_def,
                  return_def, read_result_def]) >>
          metis_tac[const_subst_expr_ok_def, frame_subscript_typing,
                    optionTheory.IS_SOME_EXISTS]) >>
      metis_tac[const_subscript_hashmap_base])
  >~ [`const_subst_expr_ok _ _ _ _ (Builtin ty bi es)`]
  >- (simp[const_subst_expr_ok_def, well_typed_expr_def] >>
      rpt strip_tac >>
      simp_tac bool_ss [subst_consts_expr_def, Ntimes evaluate_def 2, expr_type_def] >>
      `MAP expr_type (subst_consts_exprs env' es) = MAP expr_type es` by
        metis_tac[const_subst_typed_annotations] >>
      simp[subst_consts_exprs_map] >>
      rewrite_tac[ignore_bind_def] >>
      irule const_computations_related_prefix >> reverse conj_tac
      >- (irule const_computations_related_refl >> simp[]) >>
      rpt strip_tac >> BETA_TAC >>
      `s = st` by (gvs[type_check_def, assert_def, return_def, raise_def, AllCaseEqs()]) >>
      gvs[] >> Cases_on `bi = Len`
      >- (gvs[] >> Cases_on `es` >>
          gvs[well_typed_builtin_app_def, well_typed_expr_def] >>
          simp_tac bool_ss [GSYM eval_bind_assoc] >>
          irule const_computations_related_prefix >> reverse conj_tac
          >- (irule const_computations_related_prefix >> reverse conj_tac
              >- (simp_tac bool_ss [SF ETA_ss] >>
                  irule const_computations_related_length >>
                  qexistsl [`expr_type h`, `roots`] >>
                  gvs[const_subst_expr_ok_def] >>
                  metis_tac[const_subst_context_expr_frame]) >>
              rpt strip_tac >> irule const_computations_related_refl >> simp[]) >>
          rpt strip_tac >> irule const_computations_related_refl >>
          simp[const_results_related_def]) >>
      Cases_on `bi = Env MsgGas` >> simp[]
      >- (irule const_computations_related_refl >> simp[const_results_related_def]) >>
      simp_tac bool_ss [GSYM eval_bind_assoc] >>
      irule const_computations_related_prefix >> reverse conj_tac
      >- (irule const_computations_related_prefix >> reverse conj_tac
          >- (drule_all const_subst_exprs_from_elements >>
              simp[const_subst_exprs_ok_def, const_computations_related_eq,
                   subst_consts_exprs_map] >>
              disch_then (qspec_then `s` mp_tac) >>
              simp[bind_def]) >>
          rpt strip_tac >> irule const_computations_related_refl >> simp[]) >>
      rpt strip_tac >> irule const_computations_related_refl >>
      simp[const_results_related_def])
  >~ [`const_subst_expr_ok _ _ _ _ (Call ty ct es d)`]
  >- (simp[const_subst_expr_ok_def] >> disch_tac >>
      `well_typed_expr env (Call ty ct es d)` by
        gvs[frame_place_expr_other] >>
      `well_typed_exprs env es` by
        (Cases_on `ct` >> gvs[well_typed_expr_def]
         >~ [`well_typed_expr env (Call ty (IntCall p) es d)`]
         >- (PairCases_on `p` >> gvs[well_typed_expr_def]) >>
         rename1 `ExtCall _ _ sig _` >> PairCases_on `sig` >>
         gvs[well_typed_expr_def]) >>
      gen_tac >> strip_tac >>
      drule_all const_subst_exprs_from_elements >>
      simp[const_subst_exprs_ok_def] >> disch_tac >>
      simp[frame_place_expr_other, expr_type_def] >>
      Cases_on `ct`
      >~ [`IntCall p`]
      >- suspend "intcall"
      >~ [`ExtCall _ _ _ _`]
      >- suspend "extcall"
      >~ [`CreateTarget _ _ _ _`]
      >- suspend "create"
      >~ [`Send has_gas`]
      >- (simp_tac bool_ss [subst_consts_expr_def, Ntimes evaluate_def 2] >>
          simp[subst_consts_exprs_map] >> rewrite_tac[ignore_bind_def] >>
          irule const_computations_related_prefix >> reverse conj_tac
          >- (irule const_computations_related_refl >> simp[]) >>
          rpt strip_tac >> BETA_TAC >>
          `s = st` by (gvs[type_check_def, assert_def, return_def, raise_def, AllCaseEqs()]) >>
          gvs[] >> irule const_computations_related_prefix >> reverse conj_tac
          >- gvs[const_computations_related_eq, subst_consts_exprs_map] >>
          rpt strip_tac >> irule const_computations_related_refl >>
          simp[const_results_related_def]) >>
      simp_tac bool_ss [subst_consts_expr_def, Ntimes evaluate_def 2] >>
      irule const_computations_related_prefix >> reverse conj_tac
      >- gvs[const_computations_related_eq] >>
      rpt strip_tac >> BETA_TAC >> irule const_computations_related_equal >>
      simp[const_results_related_def])
QED

Resume const_subst_structural[intcall]:
  PairCases_on `p` >>
  simp_tac bool_ss [subst_consts_expr_def, Ntimes evaluate_def 2] >>
  simp[subst_consts_exprs_map] >> rewrite_tac[ignore_bind_def] >>
  irule const_computations_related_prefix >> reverse conj_tac
  >- (irule const_computations_related_refl >> simp[]) >>
  rpt strip_tac >> BETA_TAC >>
  `s = st` by (gvs[type_check_def, assert_def, return_def, raise_def, AllCaseEqs()]) >>
  gvs[] >>
  irule const_computations_related_prefix >> reverse conj_tac
  >- (irule const_computations_related_refl >> simp[]) >>
  rpt strip_tac >> BETA_TAC >>
  Cases_on `get_module_code cx p0` >>
  gvs[lift_option_type_def, lift_option_def, return_def, raise_def] >>
  irule const_computations_related_prefix >> reverse conj_tac
  >- (irule const_computations_related_refl >> simp[]) >>
  rpt strip_tac >> BETA_TAC >>
  rename1 `lookup_callable_function cx.in_deploy p1 ts` >>
  Cases_on `lookup_callable_function cx.in_deploy p1 ts` >>
  gvs[lift_option_type_def, lift_option_def, return_def, raise_def] >>
  PairCases_on `x` >> simp[] >>
  irule const_computations_related_prefix >> reverse conj_tac
  >- (irule const_computations_related_refl >> simp[]) >>
  rpt strip_tac >> BETA_TAC >>
  qpat_x_assum `type_check _ "IntCall args length" _ = _` mp_tac >>
  simp[type_check_def, assert_def, return_def, raise_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  `!ps t. eval_expr_results cx es s = (INL ps,t) ==> const_cells_agree roots t` by
    metis_tac[const_subst_context_results_frame] >>
  ho_match_mp_tac (GEN_ALL const_computations_related_intcall_results) >>
  qexists `MAP expr_type es` >>
  simp[GSYM subst_consts_exprs_map] >>
  gvs[const_subst_context_def] >> metis_tac[]
QED
Resume const_subst_structural[extcall]:
  `!xs. EVERY (const_subst_expr_ok roots cx env env') xs /\
         well_typed_exprs env xs ==> const_subst_exprs_ok roots cx env env' xs` by
    metis_tac[const_subst_exprs_from_elements] >>
  `!xs s res t. well_typed_exprs env xs /\ const_cells_agree roots s /\
      eval_exprs cx xs s = (res,t) ==> const_cells_agree roots t` by
    metis_tac[const_subst_context_exprs_frame] >>
  `!xs s res t. well_typed_exprs env xs /\ const_cells_agree roots s /\
      eval_expr_results cx xs s = (res,t) ==> const_cells_agree roots t` by
    metis_tac[const_subst_context_results_frame] >>
  simp_tac bool_ss [subst_consts_expr_def, Once evaluate_def] >>
  simp_tac bool_ss [Once evaluate_def] >>
  rewrite_tac[subst_consts_exprs_map, GSYM MAP_TAKE, GSYM MAP_DROP] >>
  PairCases_on `p` >> simp_tac bool_ss [LET_THM] >> BETA_TAC >>
  ho_match_mp_tac (GEN_ALL const_computations_related_extcall) >>
  qexists `MAP expr_type (TAKE (LENGTH p1) (DROP 1 es))` >>
  simp[GSYM subst_consts_exprs_map, const_computations_related_eq] >>
  `well_typed_exprs env (TAKE 1 es) /\
   well_typed_exprs env (TAKE (LENGTH p1) (DROP 1 es)) /\
   well_typed_exprs env (DROP (1 + LENGTH p1) es)` by
    metis_tac[frame_well_typed_exprs_slices] >>
  `const_subst_exprs_ok roots cx env env' (TAKE 1 es) /\
   const_subst_exprs_ok roots cx env env' (TAKE (LENGTH p1) (DROP 1 es)) /\
   const_subst_exprs_ok roots cx env env' (DROP (1 + LENGTH p1) es)` by
    metis_tac[rich_listTheory.EVERY_TAKE, rich_listTheory.EVERY_DROP] >>
  gvs[const_subst_exprs_ok_def] >> metis_tac[]
QED
Resume const_subst_structural[create]:
  `!xs. EVERY (const_subst_expr_ok roots cx env env') xs /\
         well_typed_exprs env xs ==> const_subst_exprs_ok roots cx env env' xs` by
    metis_tac[const_subst_exprs_from_elements] >>
  `!xs s res t. well_typed_exprs env xs /\ const_cells_agree roots s /\
      eval_exprs cx xs s = (res,t) ==> const_cells_agree roots t` by
    metis_tac[const_subst_context_exprs_frame] >>
  `!xs s res t. well_typed_exprs env xs /\ const_cells_agree roots s /\
      eval_expr_results cx xs s = (res,t) ==> const_cells_agree roots t` by
    metis_tac[const_subst_context_results_frame] >>
  `MAP expr_type (subst_consts_exprs env' es) = MAP expr_type es` by
    metis_tac[const_subst_typed_annotations] >>
  simp_tac bool_ss [subst_consts_expr_def, Once evaluate_def] >>
  simp_tac bool_ss [Once evaluate_def] >>
  gvs[subst_consts_exprs_map] >>
  Cases_on `c` >> simp_tac (srw_ss()) []
  >- (irule const_computations_related_prefix >>
      reverse conj_tac >- (simp[const_computations_related_eq]) >>
      rpt strip_tac >> irule const_computations_related_equal >>
      simp[const_results_related_def])
  >- (simp_tac bool_ss [] >> irule const_computations_related_prefix >>
      reverse conj_tac >- (simp[const_computations_related_eq]) >>
      rpt strip_tac >> irule const_computations_related_equal >>
      simp[const_results_related_def])
  >- (simp_tac bool_ss [] >>
      rewrite_tac[MAP_TAKE, MAP_DROP] >>
      ho_match_mp_tac (GEN_ALL (BETA_RULE (PURE_REWRITE_RULE [eval_bind_assoc]
        const_computations_related_create_blueprint))) >>
      qexists `MAP expr_type (DROP (if b then 4 else 3) es)` >>
      simp[GSYM MAP_TAKE, GSYM MAP_DROP, GSYM subst_consts_exprs_map,
        const_computations_related_eq] >>
      `well_typed_exprs env (TAKE (if b then 4 else 3) es) /\
       well_typed_exprs env (DROP (if b then 4 else 3) es)` by
        metis_tac[frame_well_typed_exprs_slices] >>
      `const_subst_exprs_ok roots cx env env' (TAKE (if b then 4 else 3) es) /\
       const_subst_exprs_ok roots cx env env' (DROP (if b then 4 else 3) es)` by
        metis_tac[rich_listTheory.EVERY_TAKE, rich_listTheory.EVERY_DROP] >>
      gvs[const_subst_exprs_ok_def] >> conj_tac
      >- (rpt strip_tac >>
          qpat_x_assum `!s. const_cells_agree roots s ==> _ /\
            const_computations_related _ (eval_expr_results cx (TAKE _ es)) _ s`
            (qspec_then `st` mp_tac) >>
          simp[] >> strip_tac >>
          qpat_x_assum `eval_exprs cx _ st = (INL v,s)` mp_tac >>
          asm_rewrite_tac[] >> strip_tac >>
          qpat_x_assum `!xs s res t. _ /\ _ /\ eval_exprs cx xs s = _ ==> _`
            irule >> goal_assum (drule_at Any) >> simp[]) >>
      rpt strip_tac >>
      qpat_x_assum `!xs s res t. _ /\ _ /\ eval_expr_results cx xs s = _ ==> _`
        irule >> goal_assum (drule_at Any) >> simp[]) >>
  simp_tac bool_ss [] >>
  ho_match_mp_tac (GEN_ALL (BETA_RULE (PURE_REWRITE_RULE [eval_bind_assoc]
    const_computations_related_raw_create))) >>
  qmatch_goalsub_abbrev_tac `TAKE n (DROP 2 es)` >>
  qexists `MAP expr_type (TAKE n (DROP 2 es))` >>
  simp[GSYM MAP_TAKE, GSYM MAP_DROP, GSYM subst_consts_exprs_map,
    const_computations_related_eq] >>
  `well_typed_exprs env (TAKE 2 es) /\
   well_typed_exprs env (TAKE n (DROP 2 es)) /\
   well_typed_exprs env (DROP n (DROP 2 es))` by
    metis_tac[frame_well_typed_exprs_slices] >>
  `const_subst_exprs_ok roots cx env env' (TAKE 2 es) /\
   const_subst_exprs_ok roots cx env env' (TAKE n (DROP 2 es)) /\
   const_subst_exprs_ok roots cx env env' (DROP n (DROP 2 es))` by
    metis_tac[rich_listTheory.EVERY_TAKE, rich_listTheory.EVERY_DROP] >>
  gvs[const_subst_exprs_ok_def, subst_consts_exprs_map,
    GSYM MAP_TAKE, GSYM MAP_DROP] >> metis_tac[]
QED
Finalise const_subst_structural

Theorem constant_lookup_footprint:
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  declared_constant mods NONE id /\
  constant_value mods (constant_machine_immutables am cx.txn.target)
    (TopLevelName ty (NONE,id)) = SOME v ==>
  ?roots. const_cells_agree roots (initial_state am sc) /\
    constant_roots_provenance mods cx.txn.target roots /\
    (!st. const_cells_agree roots st ==>
      lookup_global cx NONE id st = (INL (PlaceR (ImmutablePlace NONE id [])),st))
Proof
  strip_tac >>
  gvs[constant_value_def, AllCaseEqs()] >> PairCases_on `z` >> gvs[] >>
  qexists `[(cx.txn.target,NONE,id,z0,z1)]` >>
  simp[const_cells_agree_def, constant_roots_provenance_def] >>
  conj_tac
  >- (Cases_on `ALOOKUP am.immutables cx.txn.target` >>
      gvs[initial_state_def, constant_machine_immutables_def,
          get_source_immutables_def]) >>
  rpt strip_tac >>
  simp[lookup_global_def, get_module_code_def, get_immutables_def,
       get_address_immutables_def, bind_def, return_def, lift_option_type_def] >>
  metis_tac[]
QED

(* Finite unions retain any observation monotone in the protected cells. *)
Theorem constant_observation_footprints_union:
  !ns. (!id. MEM id ns ==> ?xs.
    const_cells_agree xs st0 /\ constant_roots_provenance mods addr xs /\
    (!st. const_cells_agree xs st ==> P id st)) ==>
  ?roots. const_cells_agree roots st0 /\
    constant_roots_provenance mods addr roots /\
    (!id st. MEM id ns /\ const_cells_agree roots st ==> P id st)
Proof
  Induct
  >- (simp[] >> qexists `[]` >>
      simp[const_cells_agree_def, constant_roots_provenance_def]) >>
  gen_tac >> strip_tac >>
  `?xs. const_cells_agree xs st0 /\ constant_roots_provenance mods addr xs /\
    (!st. const_cells_agree xs st ==> P h st)` by metis_tac[MEM] >>
  `?ys. const_cells_agree ys st0 /\ constant_roots_provenance mods addr ys /\
    (!id st. MEM id ns /\ const_cells_agree ys st ==> P id st)` by
    (first_x_assum irule >> rpt strip_tac >>
     qpat_x_assum `!id. MEM id (h::ns) ==> _` irule >> simp[]) >>
  qexists `xs ++ ys` >>
  simp[const_cells_agree_append, constant_roots_provenance_append] >>
  metis_tac[]
QED

Theorem checked_module_consts_lookup_footprint:
  check_contract F cx.layouts cx.txn.target mods = SOME artifact /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  ALOOKUP mods NONE = SOME tops /\
  constants_fold_module mods imms NONE tops FEMPTY = SOME A /\
  (!src. IS_SOME src ==>
    get_source_immutables src (constant_machine_immutables am cx.txn.target) =
    get_source_immutables src imms) /\
  (!id tv v. FLOOKUP A id = SOME (tv,v) ==>
    FLOOKUP (get_source_immutables NONE
      (constant_machine_immutables am cx.txn.target)) id = SOME (tv,v)) /\
  deployment_constant_cells_typed (type_env_all_modules mods) cx.txn.target mods am ==>
  ?roots. const_cells_agree roots (initial_state am sc) /\
    constant_roots_provenance mods cx.txn.target roots /\
    (!id r st. ALOOKUP (module_consts_env tops []) id = SOME r /\
      const_cells_agree roots st ==>
      lookup_global cx NONE id st = (INL (PlaceR (ImmutablePlace NONE id [])),st))
Proof
  strip_tac >>
  `!id. MEM id (MAP FST (module_consts_env tops [])) ==>
    ?xs. const_cells_agree xs (initial_state am sc) /\
      constant_roots_provenance mods cx.txn.target xs /\
      (!st. const_cells_agree xs st ==>
        lookup_global cx NONE id st = (INL (PlaceR (ImmutablePlace NONE id [])),st))` by
    (rpt strip_tac >>
     `?r. ALOOKUP (module_consts_env tops []) id = SOME r` by
       (Cases_on `ALOOKUP (module_consts_env tops []) id` >>
        gvs[ALOOKUP_FAILS, MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[]) >>
     drule_all checked_module_consts_env_replacement_annotation >> strip_tac >>
     `well_typed_expr (artifact_env artifact mods NONE) r` by
       metis_tac[checked_module_consts_env_replacement_typed] >>
     `!tv v. FLOOKUP A id = SOME (tv,v) ==>
       FLOOKUP (get_source_immutables NONE
         (constant_machine_immutables am cx.txn.target)) id = SOME (tv,v)` by
       metis_tac[] >>
     drule_all checked_module_consts_env_runtime_read >> strip_tac >>
     irule constant_lookup_footprint >> simp[] >>
     conj_tac
     >- (first_x_assum (qspec_then `sc` strip_assume_tac) >> metis_tac[]) >>
     simp[declared_constant_def] >> metis_tac[ALOOKUP_MEM]) >>
  `?roots. const_cells_agree roots (initial_state am sc) /\
    constant_roots_provenance mods cx.txn.target roots /\
    (!id st. MEM id (MAP FST (module_consts_env tops [])) /\
      const_cells_agree roots st ==>
      lookup_global cx NONE id st = (INL (PlaceR (ImmutablePlace NONE id [])),st))` by
    (ho_match_mp_tac constant_observation_footprints_union >> simp[]) >>
  qexists `roots` >> simp[] >> rpt strip_tac >> first_x_assum irule >>
  simp[] >> drule ALOOKUP_MEM >> simp[MEM_MAP] >> metis_tac[pairTheory.FST]
QED

Theorem checked_module_consts_subst_context:
  check_contract F cx.layouts cx.txn.target mods = SOME artifact /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  ALOOKUP mods NONE = SOME tops /\
  constants_fold_module mods imms NONE tops FEMPTY = SOME A /\
  (!id r. ALOOKUP (module_consts_env tops []) id = SOME r ==>
    no_sha256_expr r) /\
  (!src. IS_SOME src ==>
    get_source_immutables src (constant_machine_immutables am cx.txn.target) =
    get_source_immutables src imms) /\
  (!id tv v. FLOOKUP A id = SOME (tv,v) ==>
    FLOOKUP (get_source_immutables NONE
      (constant_machine_immutables am cx.txn.target)) id = SOME (tv,v)) /\
  deployment_constant_cells_typed (type_env_all_modules mods) cx.txn.target mods am ==>
  ?roots. const_cells_agree roots (initial_state am sc) /\
    const_subst_context roots cx (artifact_env artifact mods current_src)
      (module_consts_env tops []) mods artifact
Proof
  strip_tac >>
  drule_all checked_module_consts_env_replay_footprint >>
  disch_then (qspec_then `sc` strip_assume_tac) >>
  drule_all checked_module_consts_lookup_footprint >>
  disch_then (qspec_then `sc` strip_assume_tac) >>
  qexists `roots ++ roots'` >>
  simp[const_cells_agree_append, const_subst_context_def] >>
  conj_tac
  >- (drule get_tenv_sources >> simp[artifact_env_def]) >>
  conj_tac
  >- (gvs[constant_roots_provenance_def, checked_frame_context_def,
          frame_maps_def, artifact_env_def] >> metis_tac[]) >>
  rpt strip_tac >>
  drule_all checked_module_consts_env_replacement_annotation >> strip_tac >>
  rpt conj_tac
  >- (drule check_contract_artifact_fields >> strip_tac >>
      simp[artifact_env_def] >>
      irule build_contract_type_artifact_bare_globals_complete >> metis_tac[])
  >- (simp[artifact_env_def] >>
      drule vyperTypeContractStaticMapsTheory.check_contract_bare_global_toplevel_vtype >>
      disch_then irule >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> simp[])
  >> qpat_x_assum `!id r. _ ==> ?pv. _` drule >> strip_tac >> qexists `pv` >>
  conj_tac
  >- (irule const_results_related_mono >> goal_assum (drule_at Any) >> simp[]) >>
  simp[const_cells_agree_append] >> metis_tac[]
QED

Theorem checked_module_consts_substitution:
  check_contract F cx.layouts cx.txn.target mods = SOME artifact /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  ALOOKUP mods NONE = SOME tops /\
  constants_fold_module mods imms NONE tops FEMPTY = SOME A /\
  (!id r. ALOOKUP (module_consts_env tops []) id = SOME r ==>
    no_sha256_expr r) /\
  (!src. IS_SOME src ==>
    get_source_immutables src (constant_machine_immutables am cx.txn.target) =
    get_source_immutables src imms) /\
  (!id tv v. FLOOKUP A id = SOME (tv,v) ==>
    FLOOKUP (get_source_immutables NONE
      (constant_machine_immutables am cx.txn.target)) id = SOME (tv,v)) /\
  deployment_constant_cells_typed (type_env_all_modules mods) cx.txn.target mods am /\
  well_typed_expr (artifact_env artifact mods current_src) e ==>
  bind (eval_expr cx (subst_consts_expr (module_consts_env tops []) e))
    (read_result cx) (initial_state am sc) =
  bind (eval_expr cx e) (read_result cx) (initial_state am sc)
Proof
  strip_tac >> drule_all checked_module_consts_subst_context >>
  disch_then (qspecl_then [`sc`,`current_src`] strip_assume_tac) >>
  `const_subst_expr_ok roots cx (artifact_env artifact mods current_src)
    (module_consts_env tops []) e` by
    (irule (cj 1 const_subst_structural) >> goal_assum (drule_at Any)) >>
  `const_computations_related $=
    (bind (eval_expr cx e) (read_result cx))
    (bind (eval_expr cx (subst_consts_expr (module_consts_env tops []) e))
      (read_result cx)) (initial_state am sc)` suffices_by
    (simp[const_computations_related_def] >> strip_tac >>
     Cases_on `a` >> Cases_on `b` >> gvs[]) >>
  irule const_computations_related_bind >>
  qexists `const_results_related roots cx (expr_type e)` >> reverse conj_tac
  >- (gvs[const_subst_expr_ok_def] >> first_x_assum drule >> simp[]) >>
  rpt strip_tac >> irule const_computations_related_read >>
  goal_assum (drule_at Any) >>
  qpat_x_assum `eval_expr cx (subst_consts_expr _ _) _ = _` kall_tac >>
  irule const_subst_context_expr_frame >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[]
QED
